;; forth-itc-vtuning.lisp -- MetaForth Code for VTuning Processing
;; DM/Acudora 10/12
;;
;; To metacompile this code, load into editor and then perform
;; "Evaluate Buffer" in the command area.
;;
;; This produces a C-source file plus a file containing the fmem array
;; encoded in binary. The binary encoding is completely position
;; independent and can be used as an encrypted runtime loadable
;; payload.
;;------------------------------------------------------------------
(in-package #:forthrpl)
;; ------------------------------------------------------------------

;; (load "./tools/Forth/forth-itc-meta-primitives.lisp")

;; ---------------------------------------------------
;; ---------------------------------------------------
;; Target Application Code

(meta-compile #>.end
  meta definitions

   0 constant  0
   1 constant  1
   2 constant  2
   4 constant  4
   8 constant  8
  -1 constant -1
  
  -1.0  facos fconstant pi
   0.0  fconstant 0.0
   1.0  fconstant 1.0
   2.0  fconstant 2.0
  10.0  fconstant 10.0
  20.0  fconstant 20.0
   0.5  fconstant 0.5
   
  .stack

  : 1+     1 + ;
  : 1-     1 - ;
  
  : 2*     2 * ;
  : 2/     2 / ;
  
  : !i     + ! ;
  : @i     + @ ;
  
  : fcells 2* ;
  : fcell  fcells + ;
  : f!i    fcell f! ;
  : f@i    fcell f@ ;

  : bytes  4 * ;
  : byte   bytes + ;
  : p@i    byte p@ ;
  : p!i    byte p! ;
  
  : dbytes 8 * ;
  : dbyte  dbytes + ;
  : pf@i   dbyte pf@ ;
  : pf!i   dbyte pf! ;

  : fsq    fdup f* ;                 
  : magsq  fsq fswap fsq f+ ;
  : cabs   magsq fsqrt ;
  : finv   1.0 fswap f/ ;

  10.0 flog finv fconstant 1/ln10
  
  : log10  flog 1/ln10 f* ;
  : db10   log10 10.0 f* ;
  : db20   log10 20.0 f* ;
  
  : alog10 10.0 fswap fexpt ;
  : ampl10 0.1  f* alog10 ;
  : ampl20 0.05 f* alog10 ;

  : 2dup   over over ;
  : 2fdup  fover fover ;
  : 2drop  drop drop ;
  : 2fdrop fdrop fdrop ;
  : fmax  2fdup f< if fswap then fdrop ;
  : fmin  2fdup f> if fswap then fdrop ;
  : 0>    0 > ;
  : min   2dup > if swap then drop ;
  : max   2dup < if swap then drop ;
  : f0>   0.0 f> ;
  : f0<   0.0 f< ;
  : f0=   0.0 f= ;
  : f0<=  0.0 f<= ;
  : fclip ( val low hi -- clipped-val )
      frot fmin fmax ;
  : +!    ( val addr -- )
      swap over @ + swap ! ;
  : f+!   ( fval addr -- )
      dup f@ f+ f! ;

  .stack
  
  ;;
  ;; Crescendo compression curves
  ;;
  structure-template gfit-struct
    ffield fit-range
    ffield coff1
    ffield coff2
    ffield coff3
    ffield coff4
    ffield coff5

  0 array gfits
  ( 0 dB) -80.0 f,
          0.0 f, 0.0 f, 0.0 f,
          0.0 f, 0.0 f,
  ;;       
  ;; (2,2) fits from NML
  ;; unrestricted domain fits 20 dBSPL to 100 dBSPL
  ;;
  
  (  5 dB) -80.000000 f,
           0.012153932845 f, -0.027972072658 f, 0.020234172436 f,
           1.106218356485 f, 0.395151170592 f,
  ( 10 dB) -80.000000 f,
           0.050195789141 f, -0.111617678367 f, 0.078211292363 f,
           1.136573472741 f, 0.420641059795 f,
  ( 15 dB) -80.000000 f,
           0.161335644299 f, -0.333041916426 f, 0.218357161984 f,
           1.181995855308 f, 0.460606334581 f,
  ( 20 dB) -80.000000 f,
           0.395090449522 f, -0.767315342693 f, 0.470643549457 f,
           1.189576745240 f, 0.476954296066 f,
  ( 25 dB) -80.000000 f,
           0.729531631616 f, -1.393947278250 f, 0.833516862035 f,
           1.146557413417 f, 0.461619378482 f,
  ( 30 dB) -80.000000 f,
           1.168306433997 f, -2.234778748792 f, 1.326413323836 f,
           1.078196616528 f, 0.434322803072 f,
  ( 35 dB) -80.000000 f,
           1.756814693160 f, -3.373932478990 f, 1.993065280096 f,
           0.992069976176 f, 0.402011673342 f,
  ( 40 dB) -80.000000 f,
           2.555796160098 f, -4.919994039434 f, 2.886270086186 f,
           0.887762017845 f, 0.365618234421 f,
  ( 45 dB) -80.000000 f,
           3.634032175130 f, -6.987899941065 f, 4.054920582166 f,
           0.764540813057 f, 0.325257725544 f,
  ( 50 dB) -80.000000 f,
           5.061765619606 f, -9.677313941142 f, 5.527783196897 f,
           0.624093143413 f, 0.281860954703 f,
  ( 55 dB) -80.000000 f,
           6.900453426629 f, -13.051866897679 f, 7.304307850380 f,
           0.470569813788 f, 0.237132455000 f,
  ( 60 dB) -80.000000 f,
           9.192293573511 f, -17.102019260069 f, 9.326713532491 f,
           0.311587671121 f, 0.193715803621 f,
  ( 65 dB) -80.000000 f,
           11.949868915007 f, -21.770617692341 f, 11.525134322195 f,
           0.153794964781 f, 0.153476845029 f,
  ( 70 dB) -80.000000 f,
           15.155610254241 f, -26.928113554838 f, 13.789208033938 f,
           0.004699965880 f, 0.118201401328 f,
  ( 75 dB) -80.000000 f,
           18.765714945524 f, -32.411640615103 f, 16.007719527784 f,
           -0.130068664218 f, 0.088779516867 f,
  ( 80 dB) -80.000000 f,
           22.719979993526 f, -38.048453196509 f, 18.081404185623 f,
           -0.246995723140 f, 0.065333859211 f,
  ( 85 dB) -80.000000 f,
           26.952568848659 f, -43.680698577395 f, 19.935687509170 f,
           -0.344735165018 f, 0.047387263449 f,
  ( 90 dB) -80.000000 f,
           31.400741776793 f, -49.181772902765 f, 21.526279829902 f,
           -0.423735506702 f, 0.034112523180 f,

  : gfit ( n -- gfit[n] )
      gfit-struct * gfits + ;
      
  .stack
  
  ;;
  ;; Bark Coefficient Records
  ;;
  
  structure-template bark-coff-struct
    ffield  interp-frac
     field  pcoff1
     field  pcoff2
     
  25 constant nfbands
   4 constant nsubbands
   nfbands nsubbands * 3 + constant ntotbands
  
  ntotbands bark-coff-struct * array bark-coffs

  : bark-coff  ( n -- bark-coff[n] )
      bark-coff-struct * bark-coffs + ;

  .stack
  
  ;;
  ;; Crescendo corrections
  ;;
  
  30.0 fconstant foldback-level
  24.0 fconstant max-gain
  
  : maybe-foldback ( dbpwr -- foldback-dbpwr )
      fdup foldback-level f<
      if
        foldback-level fdup f+ fswap f-
      then ;

  : range-reduce ( gfit dbpwr -- x )
      100.0 f-
      dup fit-range f@ fmax
      0.0 fmin
      2.0 f*
      fit-range f@ f/
      1.0 fswap f- ;

  : approx-numerator ( gfit x -- numerator )
      dup coff3 f@
      fover f*
      dup coff2 f@ f+
      f*
      coff1 f@ f+ ;

  : approx-denominator ( gfit x -- denominator )
      dup coff5 f@
      fover f*
      coff4 f@ f+
      f*
      1.0 f+ ;

  .stack
   
  : approx ( gfit dbpwr -- gain )
      dup range-reduce
      dup fdup approx-numerator
      fswap approx-denominator f/ ;

  : interpolate-gain ( pbark dbpwr -- gain )
     dup interp-frac f@ f0=
     if
       pcoff1 @ approx
     else
        dup fdup pcoff1 @ approx
        1.0 dup interp-frac f@ f- f*
        dup pcoff2 @ fswap approx
        interp-frac f@ f* f+
     then ;
        
  : compute-hcgain ( ixbark fdbpwr -- fgain )
      bark-coff fdup f0>
      if
        maybe-foldback
        interpolate-gain
        max-gain fmin
      else
        fdrop drop 0.0
      then ;

  .stack
      
  ;;
  ;; VTuning threshold elevation
  ;;
  
  : set-subband ( fdf ifit iband -- )
      over gfit over bark-coff pcoff1 !
      swap 1+ gfit over bark-coff pcoff2 !
      bark-coff interp-frac f! ;

  : fdivrem ( f1 f2 -- n df )
      f/ fdup fix dup float f- ;
      
  : set-vtuning ( fvt -- )
      nsubbands float f/
      2.5 nsubbands float f* fround
      dup 0 do
        0.0 0 i set-subband
      loop
      ntotbands over do
        i 21 nsubbands * min
        over - fdup float f*
        0.0 80.0 fclip
        5.0 fdivrem
        i set-subband
      loop drop fdrop ;

  ." 2.5 set-vtuning" cr
  2.5 set-vtuning

  ;;
  ;; Conversion between dBFS and dBPhon
  ;;
  
  77.0 fvariable CaldBSPL
 -20.0 fvariable CaldBFS
 
  : set-CaldBSPL ( f -- )
     CaldBSPL f! ;
    
  : set-CaldBFS ( f -- )
     CaldBFS f! ;
    
  : adj-fletch ( fath -- f )
     fdup f0<
     if
        240.0 f/ 1.0 f+
     else
        1.0 fswap 120.0 f/ f-
     then ;
     
  : dbfs-to-dbhl ( fpwr fath -- f )
      fswap CaldBSPL f@ CaldBFS f@ 3.0 f- f- f+
      fover f-
      fswap adj-fletch f/ ;

  : gdbhl-to-gdbspl ( fgain fath -- f )
      adj-fletch f* ;

  ;;
  ;; Fletcher-Munson ATH by Bark Frequency
  ;;
  
  0 array ath
   (  0.0  ) 36.607040586379284   f,
   (  0.25 ) 25.814769124709002   f,
   (  0.5  ) 19.583829825772057   f,
   (  0.75 ) 15.751949903789566   f,
   (  1.0  ) 13.218653604658158   f,
   (  1.25 ) 11.277773368732724   f,
   (  1.5  )  9.801565253057348   f,
   (  1.75 )  8.60981654133721    f,
   (  2.0  )  7.640869063618908   f,
   (  2.25 )  6.827122301769009   f,
   (  2.5  )  6.13842123655003    f,
   (  2.75 )  5.543539746801542   f,
   (  3.0  )  5.026229587199509   f,
   (  3.25 )  4.570006107720943   f,
   (  3.5  )  4.165365617661266   f,
   (  3.75 )  3.8099820040941808  f,
   (  4.0  )  3.476225862325933   f,
   (  4.25 )  3.132186368628126   f,
   (  4.5  )  2.8081075573208665  f,
   (  4.75 )  2.5228007499265175  f,
   (  5.0  )  2.263677085859044   f,
   (  5.25 )  2.030652712411154   f,
   (  5.5  )  1.8086699922363607  f,
   (  5.75 )  1.579706663572935   f,
   (  6.0  )  1.3605851357049374  f,
   (  6.25 )  1.1623414334382431  f,
   (  6.5  )  0.9781637061923902  f,
   (  6.75 )  0.8085381198676203  f,
   (  7.0  )  0.6440728236675568  f,
   (  7.25 )  0.4729006679199159  f,
   (  7.5  )  0.30551700965779105 f,
   (  7.75 )  0.14931750937196853 f,
   (  8.0  )  0.0                 f,
   (  8.25 ) -0.14176545192580647 f,
   (  8.5  ) -0.282878348047646   f,
   (  8.75 ) -0.43097275588496586 f,
   (  9.0  ) -0.5841109021291544  f,
   (  9.25 ) -0.7447144598926485  f,
   (  9.5  ) -0.9083913315623278  f,
   (  9.75 ) -1.0677337712276938  f,
   ( 10.0  ) -1.231435106050327   f,
   ( 10.25 ) -1.4074538197702537  f,
   ( 10.5  ) -1.5950029204739167  f,
   ( 10.75 ) -1.7975342028364452  f,
   ( 11.0  ) -2.011036166528797   f,
   ( 11.25 ) -2.2271178253774053  f,
   ( 11.5  ) -2.4550644221857     f,
   ( 11.75 ) -2.701883055810086   f,
   ( 12.0  ) -2.9731665146687902  f,
   ( 12.25 ) -3.2843149216076455  f,
   ( 12.5  ) -3.6204081077064387  f,
   ( 12.75 ) -3.9571235079715166  f,
   ( 13.0  ) -4.314276365717376   f,
   ( 13.25 ) -4.713060489051813   f,
   ( 13.5  ) -5.136576775386715   f,
   ( 13.75 ) -5.566844493358531   f,
   ( 14.0  ) -6.008521126685437   f,
   ( 14.25 ) -6.466547026042377   f,
   ( 14.5  ) -6.908790891606429   f,
   ( 14.75 ) -7.294538042294093   f,
   ( 15.0  ) -7.650313300924353   f,
   ( 15.25 ) -7.987252787948506   f,
   ( 15.5  ) -8.22982331107552    f,
   ( 15.75 ) -8.341386768632091   f,
   ( 16.0  ) -8.329078298628687   f,
   ( 16.25 ) -8.156111768150055   f,
   ( 16.5  ) -7.808639602632553   f,
   ( 16.75 ) -7.351922989820849   f,
   ( 17.0  ) -6.756611521473388   f,
   ( 17.25 ) -5.932490757680554   f,
   ( 17.5  ) -5.026619609240782   f,
   ( 17.75 ) -4.226697604716605   f,
   ( 18.0  ) -3.4854992195670462  f,
   ( 18.25 ) -2.775356969968726   f,
   ( 18.5  ) -2.21098962422397    f,
   ( 18.75 ) -1.815539109425103   f,
   ( 19.0  ) -1.498294321222133   f,
   ( 19.25 ) -1.1937805508549388  f,
   ( 19.5  ) -0.8872677584433148  f,
   ( 19.75 ) -0.5716314158771496  f,
   ( 20.0  ) -0.20242491073685187 f,
   ( 20.25 )  0.2681145733449739  f,
   ( 20.5  )  0.8572431234816378  f,
   ( 20.75 )  1.5816609829554125  f,
   ( 21.0  )  2.507996710880434   f,
   ( 21.25 )  3.7779295063320433  f,
   ( 21.5  )  5.377062440067519   f,
   ( 21.75 )  7.103787922940413   f,
   ( 22.0  )  9.340813210043805   f,
   ( 22.25 ) 12.963265260812605   f,
   ( 22.5  ) 17.865538195724838   f,
   ( 22.75 ) 23.32041455234321    f,
   ( 23.0  ) 30.29976449959615    f,
   ( 23.25 ) 40.500393500289576   f,
   ( 23.5  ) 54.75728587300147    f,
   ( 23.75 ) 59.9                 f,
   ( 24.0  ) 59.9                 f,
   ( 24.25 ) 59.9                 f,
   ( 24.5  ) 59.9                 f,
   ( 24.75 ) 59.9                 f,
   ( 25.0  ) 59.9                 f,


  : compute-spl-gain ( fpwr bark-ix -- fgaindb )
      ath over f@i
      fswap db10 fover dbfs-to-dbhl
      compute-hcgain
      fswap gdbhl-to-gdbspl ;

  .stack

  ;;
  ;; Data windowing for power estimation
  ;;

  256  constant  blksize
  128  constant  hblksize
   64  constant  qblksize
   
   ;;
   ;; double size in case: blksize <- 512
   ;;
   
   16 align
   512 farray data-window
   256 farray hdata-window
   
  : window-value
      float blksize float f/ pi f* fsin fdup f* ;

  : init-data-window
      0.0 hdata-window 0 f!i
      1.0 hdata-window qblksize f!i
      qblksize 1 do
        i 2* window-value
        fdup hdata-window i f!i
             hdata-window hblksize i - f!i
      loop
      
      0.0 data-window 0 f!i
      1.0 data-window hblksize f!i
      ;;
      ;; make symmetric about hblksize
      ;; window is blksize
      ;;
      
      hblksize 1 do
        i window-value
        fdup data-window i f!i
             data-window blksize i - f!i
      loop
      
      hdata-window >phys
      data-window >phys ;

  ;;
  ;; Interpolation of power between FFT and Bark frequency
  ;;

  48e3 fconstant sample-rate

  : set-sample-rate ( frate -- )
     fdup ['] sample-rate f!
     50e3 f> if 512 else 256 then
     dup    ['] blksize !
     2/ dup ['] hblksize !
     2/     ['] qblksize ! ;
  ." 48e3 set-sample-rate" cr
  48e3 set-sample-rate
  ." init-data-window" cr
  init-data-window 2drop
     
  : cbr      ( fkhz -- fbark )
      26.81 fswap
      1.960 fswap f/ 1.0 f+ f/ 0.53 f- 0.0 fmax ;

  129 array  ixbk
  129 farray fxbk

  : fill-ft-tables ( -- ixbk fxbk )
      0 ixbk 0 !i
      0.0 fxbk 0 f!i
      129 1 do
         i float 1e-3 f* sample-rate f* blksize float f/
         cbr nsubbands float f*
         fdup fix dup ixbk i !i
         float f- fxbk i f!i
      loop
      ixbk >phys fxbk >phys ;
  ." fill-ft-tables" cr
  fill-ft-tables 2drop
         
  : inv-cbr  ( fbark -- fkhz )
      1.960 fswap
      26.81 fswap
      0.53 f+ f/ 1.0 f- f/ ;
  
  ntotbands array  ixft
  ntotbands farray fxft

  : fill-bark-tables ( -- ixft fxft )
      0 ixft 0 !i
      0.0 fxft 0 f!i
      ntotbands 1 do
         i float nsubbands float f/ inv-cbr
         1e3 f* blksize float f* sample-rate f/
         fdup 128.0 f>= if fdrop 127.99 then
         fdup fix dup ixft i !i
         float f- fxft i f!i
      loop
      ixft >phys fxft >phys ;
  ." fill-bark-tables" cr
  fill-bark-tables 2drop

  ;;
  ;; Jump Vector
  ;;
  
  ' set-vtuning           cfa 0 !
  ' set-CaldBSPL          cfa 1 !
  ' set-CaldBFS           cfa 2 !
  ' compute-spl-gain      cfa 3 !
  ' fill-bark-tables      cfa 4 !
  ' fill-ft-tables        cfa 5 !
  ' set-sample-rate       cfa 6 !
  ' init-data-window      cfa 7 !
  ;; ------------------------------------------
  ;; 0 variable tst -1 , -2 , -3 ,
  ;; " this is supposed to be a string" cr .
  ;; ( this is a test of comments )
  ;; cr pi f.
  
  .stack
  .end)

;; -----------------------
;; generate the C-code for the primitive dispatch table
(dump-fn-table)
;; -----------------------

;; --------------------------------------
;; C-code interface to the Forth ITC code
;;

(c-code #>.end
// -------------------------------------------------------
// Basic Engine
// -------------------------------------------------------

void f_init_inner()
{
  // f_reg_s = 0;
  // f_reg_f = 0;
}

inline void f_step(int32 val)
{
  f_reg_w = val;
  int32 cfa = f_mem[f_reg_w++];
  (*f_funcs[cfa])();
}
 
void f_inner(int32 startix)
{
  // f_reg_r = 0;
  // f_reg_i = 0;
  f_step(f_mem[startix]);
  while(f_reg_i)
    f_step(nxtop);
}

// -------------------------------------------------------
// VTuning
// -------------------------------------------------------

#define X_SET_VTUNING           0
#define X_SET_CALDBSPL          1
#define X_SET_CALDBFS           2
#define X_COMPUTE_SPL_GAIN      3
#define X_FILL_BARK_TABLES      4
#define X_FILL_FT_TABLES        5
#define X_SET_SAMPLE_RATE       6
#define X_INIT_DATA_WINDOW      7

void f_set_vtuning(float64 vt)
{
  // f_init_inner();
  _f_fpush(vt);
  f_inner(X_SET_VTUNING);
}

void f_set_CaldBSPL(float64 dbspl)
{
  // f_init_inner();
  _f_fpush(dbspl);
  f_inner(X_SET_CALDBSPL);
}

void f_set_CaldBFS(float64 dbfs)
{
  // f_init_inner();
  _f_fpush(dbfs);
  f_inner(X_SET_CALDBFS);
}

float64 f_compute_spl_gain(uint32 ixbark, float64 dbpwr)
{
  // f_init_inner();
  _f_fpush(dbpwr);
  _f_spush(ixbark);
  f_inner(X_COMPUTE_SPL_GAIN);
  return _f_fpop();
}

void f_set_sample_rate(float64 fsamp)
{
  // f_init_inner();
  _f_fpush(fsamp);
  f_inner(X_SET_SAMPLE_RATE);
}

void f_fill_bark_tables(uint32 **ixft, float64 **fxft)
{
  // f_init_inner();
  f_inner(X_FILL_BARK_TABLES);
  *fxft = (float64*)_f_spop();
  *ixft = (uint32*)_f_spop();
}

void f_fill_ft_tables(uint32 **ixbk, float64 **fxbk)
{
  // f_init_inner();
  f_inner(X_FILL_FT_TABLES);
  *fxbk = (float64*)_f_spop();
  *ixbk = (uint32*) _f_spop();
}

void f_init_data_window(float64 **pwin, float64 **pwin2)
{
  // f_init_inner();
  f_inner(X_INIT_DATA_WINDOW);
  *pwin  = (float64*)_f_spop();
  *pwin2 = (float64*)_f_spop();
}

void f_get_fmem(void** pbuf, long* plen)
{
   *pbuf = (void*)f_mem;
   *plen = sizeof(f_mem);
}

.end)

;; ----------------------------------------
;; dump the C-source file
;; and the binary fmem array
(when t
  (dump-c-code)
  (dump-fmem))
;; ----------------------------------------


#|
diff ./tools/Forth/vtuning-fcode.cpp ~/projects/Lispworks/tools/Forth/vtuning-fcode.cpp
diff ./tools/Forth/fmem-array.dat ~/projects/Lispworks/tools/Forth/fmem-array.dat
|#
