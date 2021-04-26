
(asdf:defsystem "forthrpl"
  :description "forth: ITC Forth in Lisp"
  :version     "1.0"
  :author      "D.McClain <david@acudora.com>"
  :license     "Copyright (c) 2011-2012 by Acudora, Inc. All rights reserved."
  :components  ((:file "package")
                (:file "forth-itc-rpl-clos-lispcode")
                (:file "forth-itc-rpl-clos-forthcode"))
  :serial       t
  :depends-on   ("useful-macros"
                 "data-objects"))

