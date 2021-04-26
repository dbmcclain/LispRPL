
;; ------------------------------------------------------------------
(in-package #:forthrpl)
;; ------------------------------------------------------------------

;; ----------------------------------------------------------
;; MetaCompiler Support
(defparameter *fstack*          nil)

;; fwd refs
(defparameter *tic-flit*        nil)
(defparameter *tic-meta-lit32i* nil)
(defparameter *tic-meta-lit64f* nil)
(defparameter *tic-meta-inner*  nil)
(defparameter *tic-meta-step*   nil)
(defparameter *tic-outer-meta*  nil)

(setf *meta-present* t) ;; activate metacompiler overrides

;; -------------------------------

(defmethod compile-literal ((v float))
  (if *meta-present*
      (progn
        (forth-compile-in *tic-flit*)
        (forth-compile-in (dfloat v)))
    ;; else
    (call-next-method)))
    
(defmethod push-literal ((v float))
  (if *meta-present*
      (push (dfloat v) *fstack*)
    ;; else
    (call-next-method)))

;; -------------------------------

(defmethod compile-literal ((v integer))
  (basic-compile-literal v))

(defmethod push-literal ((v integer))
  (basic-push-literal v))

;; -------------------------------

(defmethod compile-literal ((v rational))
  (compile-literal (dfloat v)))

(defmethod push-literal ((v rational))
  (push-literal (dfloat v)))

;; -------------------------------
;; augmentation to make us use an F-Stack
(defmethod init-interpreter :after ()
  (setf *fstack* nil))

;; --------------------------------------------------

(defmacro define-unary-fops (&rest ops)
  `(progn
     ,@(mapcar #`(code ,(if (consp a1)
                            (car a1)
                          a1)
                   (setf (car *fstack*)
                         (,(if (consp a1)
                               (cadr a1)
                             a1)
                          (car *fstack*))))
               ops)))

(defmacro define-unary-fcompares (&rest ops)
  `(progn
     ,@(mapcar #`(code ,(if (consp a1)
                            (car a1)
                          a1)
                   (push (,(if (consp a1)
                               (cadr a1)
                             a1)
                          (pop *fstack*))
                         *pstack*))
               ops)))

(defmacro define-binary-fops (&rest ops)
  `(progn
     ,@(mapcar #`(code ,(if (consp a1)
                            (car a1)
                          a1)
                   (let ((opnd2 (pop *fstack*)))
                     (setf (car *fstack*)
                           (,(if (consp a1)
                                 (cadr a1)
                               a1)
                            (car *fstack*) opnd2))))
               ops)))

(defmacro define-binary-fcompares (&rest ops)
  `(progn
     ,@(mapcar #`(code ,(if (consp a1)
                            (car a1)
                          a1)
                   (let ((opnd2 (pop *fstack*))
                         (opnd1 (pop *fstack*)))
                     (push (,(if (consp a1)
                                 (cadr a1)
                               a1)
                            opnd1 opnd2)
                           *pstack*)))
               ops)))

;; --------------------------------------------------------

(defparameter *fmem* (make-array 4096
                               :element-type    '(signed-byte 32)
                               :initial-element 0
                               :fill-pointer    64 ;; reserve room for 64 entry points
                               :adjustable      t))

(defun mhere ()
  (fill-pointer *fmem*))

(defun mcompile (val)
  (vector-push-extend val *fmem*))

(defun pad-fmem-table (nw)
  (let* ((nel  (length *fmem*))
         (nrem (mod nel nw)))
    (unless (zerop nrem)
      (loop repeat (- nw nrem) do
            (mcompile 0)))))
    
;; --------------------------------------------------------

(fli:define-c-struct long-pair
  (h :int32)
  (l :int32))

(fli:define-c-union double-bits
  (d  :double-float)
  (i  (:struct long-pair)))

;; --------------------------------------------------------------

(defparameter *ccode-list* (make-array 16
                                     :initial-element nil
                                     :fill-pointer 0
                                     :adjustable t))

(defun c-code (ccode)
  (vector-push-extend ccode *ccode-list*))


(defparameter *cfn-list* (make-array 16
                                   :initial-element nil
                                   :fill-pointer 0
                                   :adjustable   t))

(defun chere ()
  (fill-pointer *cfn-list*))

(defun not-executable (self)
  (error "Meta word not executable: ~A" (fw-nfa self)))

;; -----------------------------------------------------------------

(defparameter *m_funcs* (make-array 128
                                  :adjustable t
                                  :fill-pointer 0))

(defun last-mcode ()
  (mw-mfa (last-def)))

(defun meta-link (w)
  (vector-push-extend w *m_funcs*)
  (link w))

(defun meta-link-derived-word (parent &rest props)
  (meta-link (apply #'derive-word parent props)))

;; ------------------------------------------------------------------

(defclass <meta-def> (<scolon-def>)
  ((mfa  :accessor mw-mfa   :initarg :mfa)
   )
  (:default-initargs
   :mfa  'no-meta-def))

(defun no-meta-def (self)
  (error "Not defined in META: ~A" (fw-nfa self)))

(defmacro mcode (name &key cname ccode does)
  (format t "~%mcode: ~A" name)
  (let ((cfa   (chere))
        (ccode (concatenate 'string
                            (format nil "~%void ~A()~%{~%" cname)
                            ccode
                            (format nil "~&}~%")))
        (nfa   (string name))
        (ifa   (mhere))
        (beh   (if does #'docol #'not-executable))
        (ilst  (and does
                    (fw-ifa (car (interpret does))))))
    (vector-push-extend cname *cfn-list*)
    (vector-push-extend ccode *ccode-list*)
    (mcompile cfa)
    `(meta-link-derived-word '<meta-def>
                             :nfa  ,nfa
                             :cfa  ,beh
                             :ifa  ',ilst
                             :mfa  ,ifa)
    ))

;; -----------------------------------------------------------

(defmethod mcompile-literal ((val integer))
  (cond
   ((< (integer-length (abs val)) 32)
    (mcompile (mw-mfa *tic-meta-lit32i*))
    (mcompile val))
   (t (error "Integer value too large: ~A" val))))

(defmethod mcompile-literal ((val single-float))
  (mcompile-literal (coerce val 'double-float)))

(defmethod mcompile-literal ((val double-float))
  (mcompile (mw-mfa *tic-meta-lit64f*))
  (fli:with-dynamic-foreign-objects ((u double-bits))
    (setf (fli:foreign-slot-value u 'd) val)
    (mcompile (fli:foreign-slot-value u '(i h)))
    (mcompile (fli:foreign-slot-value u '(i l))) ))

(defun meta-handle-found (word)
  (handle-found word (um:compose #'mcompile #'mw-mfa)))

(defun meta-handle-not-found (str)
  (handle-not-found str #'mcompile-literal))

(defun meta-compile (verbs-string)
  (interpret verbs-string *tic-outer-meta*))

(defun interactive-meta ()
  (interactive *tic-outer-meta*))

;; ------------------------------------------------------------

(defun build-fmem-table ()
  (pad-fmem-table 16)
  (setf (aref *ccode-list* 1)
        (with-output-to-string (s)
          (let ((nwrds (length *fmem*)))
            (declare (ignore nwrds))
            (format s "~%int32 f_mem[4096];~%#if 0~%")
            (format s "~%int32 f_mem[4096] = {")
            (let ((lst (um:group (coerce *fmem* 'list) 8))
                  (cnt 0))
              (dolist (grp lst)
                (format s "~%  /* ~4D */ ~{~12D,~}" cnt grp)
                (incf cnt 8))
              ))
          (format s "~%};~%#endif~%~%")
          )))

(defun build-fn-table ()
  (with-output-to-string (s)
    (let ((nfns (length *cfn-list*)))
      (format s "~%typedef void (*void_funcp_t)();")
      (format s "~%void_funcp_t f_funcs[~D] = {" nfns)
      (dotimes (ix nfns)
        (format s "~%  ~A," (aref *cfn-list* ix)))
      (format s "~%};~%~%"))))

(defun dump-fn-table ()
  (vector-push-extend
   (build-fn-table)
   *ccode-list*))

(defvar *working-folder* (merge-pathnames "tools/Forth/"
                                          (translate-logical-pathname "PROJECTS:LISP;")))

(defun dump-c-code ()
  (build-fmem-table)
  (with-open-file (f
                   (merge-pathnames "vtuning-fcode.cpp"
                                    *working-folder*)
                   :direction :output
                   :if-exists :supersede
                   :if-does-not-exist :create)
    (let ((ngrps (length *ccode-list*)))
      (dotimes (ix ngrps)
        (princ (aref *ccode-list* ix) f)))))

(fli:define-c-union byte-quad
  (l :int32)
  (b (:foreign-array (:unsigned :byte) (4))))

(defun dump-fmem ()
  (with-open-file (f
                   (merge-pathnames "fmem-array.dat"
                                    *working-folder*)
                   :direction :output
                   :if-exists :supersede
                   :if-does-not-exist :create
                   :element-type '(unsigned-byte 8))
    (fli:with-dynamic-foreign-objects ((v byte-quad))
      (loop for ix from 0 below (array-total-size *fmem*) do
            (setf (fli:foreign-slot-value v 'l) (aref *fmem* ix))
            (write-byte (fli:foreign-aref (fli:foreign-slot-pointer v 'b) 0) f)
            (write-byte (fli:foreign-aref (fli:foreign-slot-pointer v 'b) 1) f)
            (write-byte (fli:foreign-aref (fli:foreign-slot-pointer v 'b) 2) f)
            (write-byte (fli:foreign-aref (fli:foreign-slot-pointer v 'b) 3) f) ))))

(defun init-meta-kernel ()
  (setf *fstack*          nil
        *tic-flit*        nil
        
        *tic-meta-lit32i* nil
        *tic-meta-lit64f* nil
        *tic-meta-inner*  nil
        *tic-meta-step*   nil
        *tic-outer-meta*  nil

        *fmem*     (make-array 4096
                               :element-type    '(signed-byte 32)
                               :initial-element 0
                               :fill-pointer    64 ;; reserve room for 64 entry points
                               :adjustable      t)
        *ccode-list* (make-array 16
                                 :initial-element nil
                                 :fill-pointer 0
                                 :adjustable t)
        *cfn-list*   (make-array 16
                                 :initial-element nil
                                 :fill-pointer 0
                                 :adjustable   t)
        *m_funcs*    (make-array 128
                                 :adjustable t
                                 :fill-pointer 0) ))

;; --------------------------------------------------------------------------------

(defun load-meta-kernel ()
  (load (merge-pathnames "forth-itc-metacompiler-forthcode.lisp"
                         *working-folder*)))
;; (load-meta-kernel)

(defun reload ()
  (labels ((ld (fname)
             (load (merge-pathnames fname *working-folder*))))
    (dolist (file '("forth-itc-rpl-ro-forthcode.lisp"
                    "forth-itc-ro-metacompiler-forthcode.lisp"
                    "forth-itc-meta-primitives.lisp"))
      (ld file))))
