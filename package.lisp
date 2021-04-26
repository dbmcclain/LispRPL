
(in-package :user)

(defpackage :forthrpl
  (:use #:common-lisp)
  (:import-from #:useful-macros
   #:if-let
   #:when-let
   #:nlet
   #:do-nothing
   #:curry
   #:dlambda)
  (:export
   #:interpret
   #:interactive
   ))
