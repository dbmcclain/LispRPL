(asdf:defsystem "forth-metacompiler"
  :description "forth-metacompiler: ITC Forth + MetaCompiler Support"
  :version     "1.0"
  :author      "D.McClain <david@acudora.com>"
  :license     "Copyright (c) 2011-2012 by Acudora, Inc. All rights reserved."
  :components  ((:file "forth-itc-clos-metacompiler-lispcode")
		(:file "forth-itc-clos-metacompiler-forthcode")
		(:file "forth-itc-meta-primitives"))
  :serial       t
  :depends-on   ("forthrpl"))

