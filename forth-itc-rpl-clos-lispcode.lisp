;; forth.lisp -- Forth with Cons-threading in Lisp
;; Equivalent of ITC
;; DM/RAL  03/09
;; --------------------------------------------------------------------

;; ------------------------------------------------------------------
(in-package #:forthrpl)
;; ------------------------------------------------------------------

(defparameter *init-fns*
  (make-array 16
              :adjustable   t
              :fill-pointer 0))

(defun do-add-init (fn)
  (vector-push-extend fn *init-fns*))

(defmacro add-init (&body body)
  `(do-add-init (lambda ()
                  ,@body)))

(defun initialize ()
  (map nil 'funcall *init-fns*))

;; ------------------------------------------------------------------
(defparameter *meta-present* nil)
;; --------------------------------------------------------------------

;; forward refs
(defparameter *tic-exit*  nil)
(defparameter *tic-lit*   nil)
(defparameter *tic-cnop*  nil)
(defparameter *tic-outer* nil)

(add-init
 (setf *meta-present* nil
       *tic-exit*     nil
       *tic-lit*      nil
       *tic-cnop*     nil
       *tic-outer*    nil))

;; -----------------------------------------------------

(defclass <code-def> ()
  ((cfa       :accessor fw-cfa    :initarg :cfa)
   (nfa       :accessor fw-nfa    :initarg :nfa)
   (lfa       :accessor fw-lfa    :initarg :lfa)
   (immed     :accessor is-immed  :initarg :immed)
   (verb-type :accessor verb-type :allocation :class :initform "CODE")
   (has-data? :accessor has-data? :allocation :class :initform nil)
   )
  (:default-initargs
   :cfa   'no-behvior
   :nfa   "<ANON>"
   :lfa   (last-def)
   :immed nil))

(defun no-behavior (self)
  (error "No behavior: ~A" (fw-nfa self)))

(defmethod print-object ((self <code-def>) out-stream)
  (print-unreadable-object (self out-stream :type t :identity nil)
    (princ (fw-nfa self) out-stream)))

(defclass <scode-def> (<code-def>)
  ((dfa       :accessor fw-dfa  :initarg :dfa)
   (verb-type :initform ";CODE")
   (has-data? :initform t)
   ))

;; --------------------------------------------------------

(defmethod print-name ((self <code-def>))
  (princ (fw-nfa self)))

(defmethod print-name ((obj list))
  (princ "(")
  (dolist (item obj)
    (print-name item)
    (princ #\space))
  (princ ")"))

(defmethod print-name (obj)
  (write obj))

;; -----------------------------------------------------

(defparameter *skip-words* nil)

(add-init
 (setf *skip-words* nil))

(defmethod decompile ((obj <code-def>))
  (format t "~A ~A" (verb-type obj) (fw-nfa obj))
  (when (is-immed obj)
    (princ " IMMEDIATE")))

(defmethod decompile ((obj <scode-def>))
  (format t "~A ~A := ~A" (verb-type obj) (fw-nfa obj) (fw-dfa obj)))
  
;; -----------------------------------------------------------

(defmacro fcell (name &optional (ncells 1))
  `(defparameter ,name (make-array ,ncells)))

(defmacro @fcell (name &optional (index 0))
  `(aref ,name ,index))

(defmacro !fcell (name val &optional (index 0))
  `(setf (aref ,name ,index) ,val))

;; Forth accessible system variables
(fcell *context*) ;; points to dfa of a vocabulary 
(fcell *current*) ;; points to dfa of a vocabulary
(fcell *compiling*)
(fcell *base*)       (!fcell *base* #10r10)
(defparameter *gild*  nil) ;; contains a cons of dfa of a vocabulary and a last def

;; Forth VM registers
(defparameter *reg-i*   nil) ;; ITC instruction ptr
(defparameter *pstack*  nil) ;; paramater stack
(defparameter *rstack*  nil) ;; return stack
(defparameter *frstack* nil) ;; for runtime locals frames

(defvar *next-word-fn* #'do-nothing)

(add-init
  (setf *context*      (vector nil)
        *current*      (vector nil)
        *compiling*    (vector nil)
        *base*         (vector 10.)
        *gild*         nil
        *reg-i*        nil
        *pstack*       nil
        *rstack*       nil
        *frstack*      nil
        *next-word-fn* #'do-nothing))

;; ------------------------------------------------------

(defun compiling? ()
  (@fcell *compiling*))

(defun set-compile (t/f)
  (!fcell *compiling* t/f))

;; ------------------------------------------------------

(defun forth-lookup-from-word (name w)
  (nlet iter ((last w))
    (when last
      (if (string-equal (string (fw-nfa last)) name)
          last
        ;; else
        (go-iter (fw-lfa last))) )))

(defun forth-globals-lookup (w &optional (voc (@fcell *context*)))
  (when-let (name (ignore-errors (string w))) ;; e.g., fails on numbers
    (when voc
      (forth-lookup-from-word name (@fcell voc)))))

;; -------------------------------------------------------------------
;; Local Vars...

(defstruct frame
  def
  locals
  icode-arena)

;; display - a stack of local frames
;; each frame is (cons compile-state . locals)
;; first one applies to toplevel non-compiling state
(defparameter *display* (list (make-frame)))

(add-init
  (setf *display* (list (make-frame))))

(define-symbol-macro %cur-icode% (frame-icode-arena (car *display*)))
(define-symbol-macro %cur-def%   (frame-def (car *display*)))

(defun make-nested-frame (&rest args)
  (apply 'make-frame :def %cur-def% args))

(defun toplevel? ()
  (null (cdr *display*)))

(defun forth-locals-lookup (w)
  (nlet iter ((frames *display*)
              (lvl    0))
    (when frames
      (destructuring-bind (hd . tl) frames
        (unless (frame-locals hd)
          (go-iter tl lvl))
        (if-let (pos (position w (frame-locals hd)
                               :test #'string-equal))
            (values lvl pos)
          ;; else
          (go-iter tl (1+ lvl)))
        ))))

;; -----------------------------------------------------------------------

(defun #1=forth-lookup (w &optional (voc (@fcell *context*)))
  (when (compiling?)
    (multiple-value-bind (lvl pos)
        (forth-locals-lookup w)
      (when lvl
        (return-from #1# (make-local-accessor lvl pos)))
      ))
  (forth-globals-lookup w voc))

(defun must-find (w)
  (or (forth-globals-lookup w)
      (error "Not found: ~A" w)))

(defun set-current-context ()
  (!fcell *context* (@fcell *current*)))

(defun forth-compile-words (wds)
  (set-current-context)
  (um:accum acc
    (dolist (wd wds)
      (let ((v  (forth-globals-lookup wd)))
        (cond (v
               (acc v))
                  
              ((and (consp wd)
                    (eq 'quote (car wd)))
               (acc *tic-lit*)
               (acc (cadr wd)))
                  
              (t
               (acc *tic-lit*)
               (acc wd))
              )))
    (acc *tic-exit*)))
      
;; --------------------------------------
(defvar *tracing* nil)

(defun trace+ ()
  (setf *tracing* t))

(defun trace- ()
  (setf *tracing* nil))

(defun print-current-word (reg-w)
  (format t "~vT~A" (length *rstack*) (fw-nfa reg-w)))

(defun execute-word (w)
  (funcall (fw-cfa w) w))

(defun inner-interpreter (w)
  (nlet iter ((reg-w w))
    (when *tracing*
      (print-current-word reg-w))
    (execute-word reg-w)
    (when *reg-i*
      (go-iter (pop *reg-i*)))
    ))

;; --------------------------------------------------
;; wtypes

(defun docol (self)
  (push *reg-i* *rstack*)
  (setf *reg-i* (fw-ifa self)))

(defun doval (self)
  (push (fw-dfa self) *pstack*))

;; ----------------------------------------------------
;; defining words

(defun last-def ()
  (when-let (voc (@fcell *current*))
    (@fcell voc)))

(defun link (w)
  (format t "Defining: ~A~&" (fw-nfa w))
  (when-let (voc (@fcell *current*))
    (!fcell voc w))
  w)

(defun immediate ()
  (when-let (last-def (last-def))
    (setf (is-immed last-def) t)))

(defun derive-word (parent &rest props)
  (setf %cur-def% (apply 'make-instance parent props)))

(defun link-derived-word (parent &rest parms)
  (link (apply #'derive-word parent parms)))

;; ---------------------------------------------

(defclass <vocabulary> (<scode-def>)
  ((verb-type :initform "VOCABULARY"))
  (:default-initargs
   :cfa   (lambda (self)
            (!fcell *context* (fw-dfa self)))
   :immed t))

(defmethod initialize-instance :after ((self <vocabulary>) &key &allow-other-keys)
  (setf (fw-dfa self) (vector self)))
   
(defmacro vocabulary (name)
  (format t "vocabulary: ~A~&" name)
  `(link-derived-word '<vocabulary>
                      :nfa (string ',name)
                      ))

;; ---------------------------------------------

(defmacro code (name &body body)
  (format t "code: ~A~&" name)
  `(link-derived-word '<code-def>
                      :nfa  (string ',name)
                      :cfa  (lambda (self)
                              (declare (ignorable self))
                              ,@body)
                      ))

;; ---------------------------------------------

(defclass <colon-def> (<code-def>)
  ((ifa       :accessor fw-ifa  :initarg :ifa)
   (verb-type :initform ":"))
  (:default-initargs
   :cfa  'docol
   :ifa  nil))

(defmacro colon (name &rest iwords)
  (format t "colon: ~A~&" name)
  `(link-derived-word '<colon-def>
                      :nfa   (string ',name)
                      :ifa   (forth-compile-words ',iwords)
                      ))

;; ---------------------------------------------

(defclass <constant> (<scode-def>)
  ((verb-type :initform "CONSTANT"))
  (:default-initargs
   :cfa 'doval
   ))

(defmacro const (name cval)
  (format t "const: ~A~&" name)
  `(link-derived-word '<constant>
                      :nfa  (string ',name)
                      :dfa  ,cval
                      ))

(defclass <scolon-def> (<scode-def> <colon-def>)
  ((verb-type :initform ";:"))
  (:default-initargs
   :cfa  (lambda (self)
           (doval self)
           (docol self))
   ))

;; ---------------------------------------------

(defclass <local-accessor> (<scode-def>)
  ((verb-type :initform "LOCAL"))
  (:default-initargs
   :cfa (lambda (self)
          (destructuring-bind (lvl pos) (fw-dfa self)
            (push (aref (nth lvl *frstack*) pos) *pstack*)))
   ))

(defparameter *local-accessor-cache*
  (make-hash-table :test 'equalp))

(add-init
  (setf *local-accessor-cache* (make-hash-table :test 'equalp)))

(defun make-local-accessor (lvl pos)
  (let ((key (list lvl pos)))
    (or (gethash key *local-accessor-cache*)
        (setf (gethash key *local-accessor-cache*)
              (make-instance '<local-accessor>
                             :dfa  key))
        )))

;; ---------------------------------------------

(defmethod decompile ((obj <constant>))
  (format t "~A ~A := ~A" (verb-type obj) (fw-nfa obj) (fw-dfa obj)))
  
(defmethod decompile ((obj <colon-def>))
  (format t "~A ~A" (verb-type obj) (fw-nfa obj))
  (decompile-ifa obj))

(defmethod decompile ((obj <scolon-def>))
  (call-next-method)
  (decompile-ifa obj))

(defun decompile-ifa (obj)
  (nlet iter ((vs  (fw-ifa obj)))
    (when vs
      (let ((v   (first vs))
            (vtl (rest vs)))
        (princ #\space)
        (cond ((and (endp vtl)
                    (eql v *tic-exit*))
               (princ ";"))

              ((is-immed v)
               (format t "[COMPILE] ~A" (fw-nfa v)))
              
              (t (print-name v))
              )
        (when (eql v *tic-lit*)
          (princ #\space)
          (print (pop vtl)))
        (go-iter (if (member v *skip-words*)
                     (cdr vtl)
                   vtl)))
      ))
  (when (is-immed obj)
    (princ " IMMEDIATE")))

;; ----------------------------------------------------

(defmacro define-unary-ops (&rest ops)
  `(progn
     ,@(mapcar #`(code ,(if (consp a1)
                            (car a1)
                          a1)
                   (setf (car *pstack*)
                         (,(if (consp a1)
                               (cadr a1)
                             a1)
                          (car *pstack*))))
               ops)))

(defmacro define-binary-ops (&rest ops)
  `(progn
     ,@(mapcar #`(code ,(if (consp a1)
                            (car a1)
                          a1)
                   (let ((opnd2 (pop *pstack*)))
                     (setf (car *pstack*)
                           (,(if (consp a1)
                                 (cadr a1)
                               a1)
                            (car *pstack*) opnd2))))
               ops)))

(defun dfloat (x)
  (float x 1d0))

(defun not-zerop (x)
  (not (zerop x)))

(defun roll (n lst)
  ;; destructive roll of list with no consing
  (labels ((stack-empty ()
             (error "stack empty")))
    (cond ((plusp n)
           (nlet iter ((n  n)
                       (l  lst)
                       (p  nil))
             (if (zerop n)
                 (progn
                   (unless l
                     (stack-empty))
                   (setf (cdr p) (cdr l)
                         (cdr l) lst)
                   l)
               ;; else
               (go-iter (1- n) (cdr l) l))))
          
          ((minusp n)
           (let ((ans (cdr lst)))
             (nlet iter ((n  n)
                         (l  ans)
                         (p  lst))
               (if (zerop n)
                   (progn
                     (unless p
                       (stack-empty))
                     (setf (cdr lst) l
                           (cdr p)   lst)
                     ans)
                 ;; else
                 (go-iter (1+ n) (cdr l) l)))))
          
          (t lst)
          )))

(defun compile-lisp-text (text)
  (let ((text (concatenate 'string
                           "(lambda (self)"
                           "(declare (ignorable self))"
                           text
                           ")")))
    (compile nil (read-from-string text))))

;; ---------------------------------------------------
 
(defun run-interpreter (w)
  (catch 'done
    (loop do
          (inner-interpreter w)
          )))

(defun run-interactive-interpreter (w)
  ;; make the interactive interpreter immune to bomb-outs
  (um:nlet iter ()
    (restart-case
        (run-interpreter w)
      (continue-in-forth ()
        (reset-interpreter)
        (go-iter))
      )))

(defun reset-interpreter ()
  (setf *reg-i*   nil
        *rstack*  nil
        *frstack* nil ;; leave *pstack* alone for now...
        *display* (list (make-frame)))
  (set-compile nil)
  (reset-buffer))

(defmethod init-interpreter () ;; defmethod, to allow for :after methods in metacompiler
  (reset-interpreter)
  (setf *pstack*  nil))

;; -------------------------------------------------------------------

(defun whitespace-char-p (c)
  (or (not (graphic-char-p c))
      (char= c #\space)))

(defun reset-buffer()
  (funcall *next-word-fn* :reset-buffer))

(defun refill-buffer ()
  (funcall *next-word-fn* :refill-buffer))

(defun next-blank-delimited-word (buf pos)
  (nlet iter ()
    (nlet refill ()
      (when (or (null pos)
                (>= pos (length buf)))
        (setf buf (refill-buffer)
              pos 0)
        (unless (eq buf :eof)
          (go-refill))))
    (unless (eq buf :eof)
      (if (setf pos (position-if (complement #'whitespace-char-p) buf
                                 :start pos))
          (let* ((end   (position-if #'whitespace-char-p buf
                                     :start (1+ pos)))
                 (endp1 (when end
                          (if (char/= (char buf end) #\newline)
                              (1+ end)
                            end))))
            (values (subseq buf pos end) endp1))
        ;; else
        (go-iter)))))


(defun word-to-end-of-line (buf pos)
  (unless (or (eq buf :eof)
              (null pos)
              (>= pos (length buf)))
    (let ((end (position-if (curry #'char= #\newline) buf
                            :start pos)))
      (values (subseq buf pos end) (and end
                                        (1+ end))))))

(defun word-to-delimiter (delim buf pos)
  (let ((test-fn (curry #'char= delim))
        (str  ""))
    (nlet iter ()
      (nlet refill ()
        (when (or (null pos)
                  (>= pos (length buf)))
          (when pos
            (setf str (concatenate 'string str (list #\newline))))
          (setf buf (refill-buffer)
                pos 0)
          (unless (eq buf :eof)
            (go-refill))))
      (if (eq buf :eof)
          str
        ;; else
        (let ((start pos))
          (setf pos (position-if test-fn buf
                                 :start start))
          (setf str (concatenate 'string str (subseq buf start pos)))
          (if pos
              (values str (1+ pos))
            (go-iter)))))))

(defun next-word (delim buf pos)
  (case delim
    (#\space
     (next-blank-delimited-word buf pos))
    (#\newline
     (word-to-end-of-line buf pos))
    (t
     (word-to-delimiter delim buf pos))
    ))

;; -------------------------------------------------------------------

(defun make-interactive-word-reader ()
  (let ((buf  nil)
        (pos  nil))
    (dlambda
      (:refill-buffer ()
       (when (eq buf :eof)
         (error "EOF Error"))
       (let ((new-buffer (progn
                           (format t (if (compiling?) "~&] " "~&OK "))
                           (read-line *standard-input* nil :eof))))
         (if (or (eq new-buffer :eof)
                 (and (= 3 (length new-buffer))
                      (string-equal "bye" new-buffer)))
             (setf pos nil
                   buf :eof)
           ;; else
           (setf buf new-buffer))))

      (:reset-buffer ()
       (setf buf nil
             pos nil))

      (t (delim)
         (multiple-value-bind (str new-pos)
             (next-word delim buf pos)
           (setf pos new-pos)
           str))
      )))

(defun interactive (&optional (w *tic-outer*))
  (princ "Type BYE to exit...")
  (init-interpreter)
  (let ((*next-word-fn* (make-interactive-word-reader)))
    (run-interactive-interpreter w)))

;; -------------------------------------------------------------------

(defun make-string-reader (&rest bufs)
  (let ((buf  nil)
        (pos  nil))
    (dlambda
      (:refill-buffer ()
       (when (eq buf :eof)
         (error "EOF Error"))
       (if-let (new-buffer (pop bufs))
           (setf buf new-buffer)
         ;; else
         (setf pos nil
               buf :eof)))

      (:reset-buffer ()
       (setf buf nil
             pos nil))

      (t (delim)
         (multiple-value-bind (substr new-pos)
             (next-word delim buf pos)
           (setf pos new-pos)
           substr))
      )))
    
(defun interpret (verbs-string &optional (w *tic-outer*))
  (init-interpreter)
  (let ((*next-word-fn* (make-string-reader verbs-string)))
    (run-interpreter w)))

;; ---------------------------------------------------------------------

(defun forth-compile-in (word)
  (if (compiling?)
      (cond ((eq (car %cur-icode%) *tic-cnop*)
             (setf (car %cur-icode%) word))
            
            (t (push word %cur-icode%)))
    ;; else
    (let ((w (last-def)))
      (if (and w
               (has-data? w)
               (vectorp (fw-dfa w)))
          (setf (fw-dfa w) (concatenate 'vector (fw-dfa w) (vector word)))
        (error "Can't use \",\" here"))
      )))

(defun dbg (w)
  (let ((*print-level* 2)
        (*print-length* 10))
    (format t "------------------------~&")
    (format t "~A~&" (fw-nfa w))
    (format t "  pstack:~&")
    (print *pstack*)
    (format t "  rstack:~&")
    (print *rstack*)
    (format t "  state = ~A~&" (compiling?))
    ))

;; -------------------------------

(defun basic-compile-literal (v)
  (forth-compile-in *tic-lit*)
  (forth-compile-in v))

(defun basic-push-literal (v)
  (push v *pstack*))

;; -------------------------------
;; ... in anticipation of separate treatment of rationals and floats

(defmethod compile-literal (v)
  (basic-compile-literal v))

(defmethod push-literal (v)
  (basic-push-literal v))

;; -------------------------------

(defun handle-found (word wrd-compile-fn)
  (if (and (compiling?)
           (not (is-immed word)))
      (funcall wrd-compile-fn word)
    ;; else
    (execute-word word)))

(defun not-found (str)
  (error "Not found: ~A" str))

(defun do-with-forth-standard-input (fn)
  (let ((*read-default-float-format* 'double-float)
        ;; (*read-eval* nil)
        (*read-base* (@fcell *base*)))
    (funcall fn)))

(defmacro with-forth-standard-input (&body body)
  `(do-with-forth-standard-input (lambda ()
                                   ,@body)))

(defun try-convert-to-number (str)
  ;; str stripped of #\_ and #\, separators
  (let ((len (length str)))
    (um:nlet iter ((pos 0))
      (when (< pos len)
        (case (char str pos)
          ((#\-)
           (- (iter (1+ pos))))
          ((#\+)
           (go-iter (1+ pos)))
          ((#\~)
           (lognot (iter (1+ pos))))
          (t
           (let* ((tail (subseq str pos))
                  (val (ignore-errors
                         (read-from-string tail))))
             (if (numberp val)
                 val
               (try-harder-convert-to-number tail))
             ))
          )))))

(defun try-harder-convert-to-number (str)
  ;; str stripped of separators and leading sign
  (let ((len (length str)))
    (um:nlet convert-with-base ((*read-base* *read-base*))
      (um:nlet iter ((pos   0)
                     (ipart 0)
                     (base  *read-base*))
        (if (< pos len)
            (let* ((ch  (char str pos))
                   (wt  (digit-char-p ch *read-base*)))
              (cond
               (wt
                ;; valid digit
                (iter (1+ pos)
                      (+ (* ipart base) wt)
                      *read-base*))
               
               ((char= ch #\:)
                ;; sexagisimal number
                (iter (1+ pos) ipart 6.))
               
               ((char= ch #\.)
                ;; decimal or float
                (if (= *read-base* 10.)
                    (multiple-value-bind (val pos)
                        (read-from-string
                         (concatenate 'string "0."
                                      (subseq str (1+ pos))))
                      (when (>= pos len)
                        (+ ipart val)))
                  ;; else - redo with decimal
                  (go-convert-with-base 10.)))
               
               (t
                (error "Invalid number syntax"))
               ))
          ;; else - end of string
          ipart
          ))
      )))

#|
 ;; interesting idioms
 (1+ x) := (- (lognot x))
 (1- x) := (lognot (- x))
|#

(defun trim-numeric-separators (str)
  (remove-if (um:rcurry #'member '(#\_ #\,)) str))

(defun handle-not-found (str lit-compile-fn)
  ;; using the Lisp reader as much as possible
  (with-forth-standard-input
    (flet
        ((try-as-number ()
           (ignore-errors
             (try-convert-to-number
              (trim-numeric-separators str))))
         (handle-it (val)
           (if (compiling?)
               (funcall lit-compile-fn val)
             (push-literal val))))
      (let ((v  (ignore-errors
                  (multiple-value-bind (obj pos)
                      (read-from-string str)
                    (when (>= pos (length str))
                      obj)
                    ))))
        (cond ((and (consp v)
                    (eq (car v) 'quote))
               (handle-it (cadr v)))
              
              ((symbolp v)
               (if-let (ans (try-as-number))
                   (handle-it ans)
                 (not-found str)))
              
              (t
               (handle-it v))
              )))))
  
(defun forth-handle-found (word)
  (handle-found word #'forth-compile-in))

(defun forth-handle-not-found (str)
  (handle-not-found str #'compile-literal))

;; -----------------------------------------------

(defun vlist ()
  (when-let (voc (@fcell *context*))
    (nlet iter ((p (@fcell voc)))
      (when p
        (princ (fw-nfa p))
        (princ #\space)
        (go-iter (fw-lfa p)))
      ))
  (values))

;; -------------------------------------------------

