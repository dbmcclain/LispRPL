;; forth-itc-meta-primitives.lisp -- basic ITC Forth primitives
;; DM/Acudora  10/12

;; This file should be manually loaded by the application meta-code
;; module

;; ------------------------------------------------------------------
(in-package #:forthrpl)
;; ------------------------------------------------------------------

;; (load "./tools/Forth/forth-itc-metacompiler-forthcode.lisp")

;; -----------------------------------------------------
;; Metacompiled Code
;; -----------------------------------------------------

(mcode "<r"
       :cname f_rpush
       :ccode  #>.end
       _f_rpush(_f_spop());
       .end
       :does "{ rpush }")

(mcode "r>"
       :cname f_rpop
       :ccode #>.end
       _f_spush(_f_rpop());
       .end
       :does "{ rpop }")

(mcode "i"
       :cname f_i
       :ccode
       #>.end
       _f_spush(rtos);
       .end
       :does "{ rpop dup rpush }")

(mcode "swap"
       :cname f_swap
       :ccode #>.end
       int32 x = nos;
       nos = tos;
       tos = x;
       .end
       :does "{ swap }")

(mcode "dup"
       :cname f_dup
       :ccode #>.end
       _f_spush(tos);
       .end
       :does "{ dup }")

(mcode "drop"
       :cname f_drop
       :ccode #>.end
       --f_reg_s;
       .end
       :does "{ drop }")

(mcode "over"
       :cname f_over
       :ccode #>.end
       _f_spush(nos);
       .end
       :does "{ over }")

(mcode "rot"
       :cname f_rot
       :ccode #>.end
       int32 x = nnos;
       nnos = nos;
       nos = tos;
       tos = x;
       .end
       :does "{ rot }")

(mcode "-rot"
       :cname f_mrot
       :ccode #>.end
       int32 x = tos;
       tos = nos;
       nos = nnos;
       nnos = x;
       .end
       :does "{ -rot }")

(mcode "pick"
       :cname f_pick
       :ccode #>.end
       int32 off = tos;
       tos = f_sstack[f_reg_s - 2 - off];
       .end
       :does "{ pick }")

(mcode "float"
       :cname f_float
       :ccode #>.end
       int32 x = _f_spop();
       _f_fpush((float64)x);
       .end
       :does "{ float }")

(mcode "fix"
       :cname f_fix
       :ccode #>.end
       _f_spush((int32)_f_fpop());
       .end
       :does "{ ftruncate }")

(mcode "fround"
       :cname f_round
       :ccode #>.end
       _f_spush((int32)round(_f_fpop()));
       .end
       :does "{ fround }")


(mcode "fswap"
       :cname f_fswap
       :ccode #>.end
       float64 x = ftos;
       ftos = fnos;
       fnos = x;
       .end
       :does "{ fswap }")

(mcode "fover"
       :cname f_fover
       :ccode #>.end
       _f_fpush(fnos);
       .end
       :does "{ fover }")

(mcode "fdrop"
       :cname f_fdrop
       :ccode #>.end
       --f_reg_f;
       .end
       :does "{ fdrop }")

(mcode "fdup"
       :cname f_fdup
       :ccode #>.end
       _f_fpush(ftos);
       .end
       :does "{ fdup }")

(mcode "frot"
       :cname f_frot
       :ccode #>.end
       float64 x = fnnos;
       fnnos = fnos;
       fnos = ftos;
       ftos = x;
       .end
       :does "{ frot }")

(mcode "-frot"
       :cname f_mfrot
       :ccode #>.end
       float64 x = ftos;
       ftos = fnos;
       fnos = fnnos;
       fnnos = x;
       .end
       :does "{ -frot }")

(mcode "fpick"
       :cname f_fpick
       :ccode #>.end
       int32 off = _f_spop();
       _f_fpush(f_fstack[f_reg_f - 1 - off]);
       .end
       :does "{ fpick }")


(mcode "+"
       :cname f_add
       :ccode #>.end
       int32 op2 = _f_spop();
       tos += op2;
       .end
       :does "{ + }")

(mcode "-"
       :cname f_sub
       :ccode #>.end
       int32 op2 = _f_spop();
       tos -= op2;
       .end
       :does "{ - }")

(mcode "*"
       :cname f_mul
       :ccode #>.end
       int32 op2 = _f_spop();
       tos *= op2;
       .end
       :does "{ * }")

(mcode "/"
       :cname f_div
       :ccode #>.end
       int32 op2 = _f_spop();
       tos /= op2;
       .end
       :does "{ / }")

(mcode "mod"
       :cname f_mod
       :ccode #>.end
       int32 op2 = _f_spop();
       tos %= op2;
       .end
       :does "{ mod }")

(mcode "or"
       :cname f_or
       :ccode #>.end
       int32 op2 = _f_spop();
       tos |= op2;
       .end
       :does "{ or }")

(mcode "xor"
       :cname f_xor
       :ccode #>.end
       int32 op2 = _f_spop();
       tos ^= op2;
       .end
       :does "{ xor }")

(mcode "not"
       :cname f_not
       :ccode #>.end
       tos = ! tos;
       .end
       :does "{ not }")

(mcode "com"
       :cname f_com
       :ccode #>.end
       tos = ~ tos;
       .end
       :does "{ com }")

(mcode "="
       :cname f_eq
       :ccode #>.end
       int32 op2 = _f_spop();
       tos = (tos == op2);
       .end
       :does "{ = }")

(mcode "/="
       :cname f_grt
       :ccode #>.end
       int32 op2 = _f_spop();
       tos = (tos != op2);
       .end
       :does "{ /= }")

(mcode ">"
       :cname f_gt
       :ccode #>.end
       int32 op2 = _f_spop();
       tos = (tos > op2);
       .end
       :does "{ > }")

(mcode ">="
       :cname f_ge
       :ccode #>.end
       int32 op2 = _f_spop();
       tos = (tos >= op2);
       .end
       :does "{ >= }")

(mcode "<"
       :cname f_lt
       :ccode #>.end
       int32 op2 = _f_spop();
       tos = (tos < op2);
       .end
       :does "{ < }")

(mcode "<="
       :cname f_le
       :ccode #>.end
       int32 op2 = _f_spop();
       tos = (tos <= op2);
       .end
       :does "{ <= }")


(mcode "f+"
       :cname f_fadd
       :ccode #>.end
       float64 op2 = _f_fpop();
       ftos += op2;
       .end
       :does "{ f+ }")

(mcode "f-"
       :cname f_fsub
       :ccode #>.end
       float64 op2 = _f_fpop();
       ftos -= op2;
       .end
       :does "{ f- }")

(mcode "f*"
       :cname f_fmul
       :ccode #>.end
       float64 op2 = _f_fpop();
       ftos *= op2;
       .end
       :does "{ f* }")

(mcode "f/"
       :cname f_fdiv
       :ccode #>.end
       float64 op2 = _f_fpop();
       ftos /= op2;
       .end
       :does "{ f/ }")

(mcode "f="
       :cname f_feq
       :ccode #>.end
       float64 op2 = _f_fpop();
       float64 op1 = _f_fpop();
       _f_spush(op1 == op2);
       .end
       :does "{ f= }")

(mcode "f/="
       :cname f_fne
       :ccode #>.end
       float64 op2 = _f_fpop();
       float64 op1 = _f_fpop();
       _f_spush(op1 != op2);
       .end
       :does "{ f/= }")

(mcode "f<"
       :cname f_flt
       :ccode #>.end
       float64 op2 = _f_fpop();
       float64 op1 = _f_fpop();
       _f_spush(op1 < op2);
       .end
       :does "{ f< }")

(mcode "f<="
       :cname f_fle
       :ccode #>.end
       float64 op2 = _f_fpop();
       float64 op1 = _f_fpop();
       _f_spush(op1 <= op2);
       .end
       :does "{ f<= }")

(mcode "f>"
       :cname f_fgt
       :ccode #>.end
       float64 op2 = _f_fpop();
       float64 op1 = _f_fpop();
       _f_spush(op1 > op2);
       .end
       :does "{ f> }")

(mcode "f>="
       :cname f_fge
       :ccode #>.end
       float64 op2 = _f_fpop();
       float64 op1 = _f_fpop();
       _f_spush(op1 >= op2);
       .end
       :does "{ f>= }")

(mcode "neg"
       :cname f_neg
       :ccode #>.end
       tos = - tos;
       .end
       :does "{ neg }")

(mcode "fneg"
       :cname f_fneg
       :ccode #>.end
       ftos = - ftos;
       .end
       :does "{ fneg }")

(mcode "abs"
       :cname f_abs
       :ccode #>.end
       tos = (tos < 0 ? - tos : tos);
       .end
       :does "{ abs }")

(mcode "fabs"
       :cname f_fabs
       :ccode #>.end
       ftos = (ftos < 0.0 ? - ftos : ftos);
       .end
       :does "{ fabs }")

(mcode "fsqrt"
       :cname f_fsqrt
       :ccode #>.end
       ftos = sqrt(ftos);
       .end
       :does "{ fsqrt }")

(mcode "fsin"
       :cname f_fsin
       :ccode #>.end
       ftos = sin(ftos);
       .end
       :does "{ fsin }")

(mcode "fcos"
       :cname f_fcos
       :ccode #>.end
       ftos = cos(ftos);
       .end
       :does "{ fcos }")

(mcode "ftan"
       :cname f_ftan
       :ccode #>.end
       ftos = tan(ftos);
       .end
       :does "{ ftan }")

(mcode "fasin"
       :cname f_fasin
       :ccode #>.end
       ftos = asin(ftos);
       .end
       :does "{ fasin }")

(mcode "facos"
       :cname f_facos
       :ccode #>.end
       ftos = acos(ftos);
       .end
       :does "{ facos }")

(mcode "fatan"
       :cname f_fatan
       :ccode #>.end
       ftos = atan(ftos);
       .end
       :does "{ fatan }")

(mcode "flog"
       :cname f_flog
       :ccode #>.end
       ftos = log(ftos);
       .end
       :does "{ flog }")

(mcode "fexp"
       :cname f_fexp
       :ccode #>.end
       ftos = exp(ftos);
       .end
       :does "{ fexp }")

(mcode "fatan2"
       :cname f_fatan2
       :ccode #>.end
       float64 y = _f_fpop();
       ftos = atan2(y,ftos);
       .end
       :does "{ fatan2 }")

(mcode "fexpt"
       :cname f_fexpt
       :ccode #>.end
       float64 expon = _f_fpop();
       ftos = pow(ftos, expon);
       .end
       :does "{ fexpt }")

(mcode "@"
       :cname f_fetch
       :ccode #>.end
       tos = f_mem[tos];
       .end
       :does "{ @mem }")

(mcode "!"
       :cname f_store
       :ccode #>.end
       int32 off = _f_spop();
       f_mem[off] = _f_spop();
       .end
       :does "{ !mem }")

(mcode "f@"
       :cname f_ffetch
       :ccode #>.end
       int32 off = _f_spop();
       dbl_int_t x;
       x.i[0] = f_mem[off];
       x.i[1] = f_mem[off+1];
       _f_fpush(x.d);
       .end
       :does "{ dup @mem swap 1+ @mem assemble-float }")

(mcode "f!"
       :cname f_fstore
       :ccode #>.end
       int32 off = _f_spop();
       dbl_int_t x;
       x.d = _f_fpop();
       f_mem[off] = x.i[0];
       f_mem[off+1] = x.i[1];
       .end
       :does "{ split-float rot swap over 1+ !mem !mem }")

(mcode "asl"
       :cname f_asl
       :ccode #>.end
       int32 nsh = _f_spop();
       tos <<= nsh;
       .end)

(mcode "asr"
       :cname f_asr
       :ccode #>.end
       int32 nsh = _f_spop();
       tos >>= nsh;
       .end)

(mcode "lsr"
       :cname f_lsr
       :ccode #>.end
       int32 nsh = _f_spop();
       tos = (int32)((uint32)tos >> nsh);
       .end)

(mcode ">phys"
       :cname f_tophys
       :ccode #>.end
       tos *= sizeof(int32);
       tos += (int32)&f_mem;
       .end
       :does "{ dup drop }")

(mcode "<phys"
       :cname f_fromphys
       :ccode #>.end
       tos -= (int32)&f_mem;
       tos /= sizeof(int32);
       .end)

(mcode "p@"
       :cname f_physfetch
       :ccode #>.end
       int32 *p = (int32*)tos;
       tos = *p;
       .end)

(mcode "p!"
       :cname f_physstore
       :ccode #>.end
       int32 *p = (int32*)_f_spop();
       *p = _f_spop();
       .end)

(mcode "pf@"
       :cname f_fphysfetch
       :ccode #>.end
       float64 *p = (float64*)_f_spop();
       _f_fpush(*p);
       .end)

(mcode "pf!"
       :cname f_fphysstore
       :ccode #>.end
       float64 *p = (float64*)_f_spop();
       *p = _f_fpop();
       .end)

