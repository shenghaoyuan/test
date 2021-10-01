module Jump_to_cpu

open Words_t
open Arm_def
open Arm_semantics
open Valid
open FStar.List.Tot.Base
open Shift
open Properties

val ins_in_code: c:code -> f:nat -> Tot (list ins) (decreases %[f; size_code c f])

let rec ins_in_code c f =
  match c with
  | Ins i -> [i]
  | Block l -> 
    (match l with
    | [] -> []
    | hd :: tl -> append (ins_in_code hd f) (ins_in_code (Block tl) f))
  | IfElse ifCond ifTrue ifFalse ->
    append (ins_in_code ifTrue f) (ins_in_code ifFalse f)
  | While whileCond body -> if f = 0 then [] else ins_in_code body (f-1)
    

let i0 : ins = LDR R1 R0 (OConst 0l)
let i1 : ins = MOV SP (OReg R1)
let i2 : ins = LDR R0 R0 (OConst 1l)
let i3 : ins = ORR R0 R0 (OConst 1l)
let i4 : ins = BX R0
let cplist = [i0; i1; i2; i3; i4]


val memory_safety: st:arm_state -> Lemma
  (requires (st.ok=true /\ (list_cond_ok cplist st)))
  (ensures  (let st1 = eval_list_ins cplist st in
             st1.ok = true))
let memory_safety st = list_memory_safety cplist st  

open FStar.Int


val functional_correctness_aux2_0: st:arm_state -> Lemma
  (requires (st.ok=true))
  (ensures  (let st0 = eval_cond_ins i0 st in
             let r0' = eval_reg R0 st in
             let r0  = eval_reg R0 st0 in
             let r1_0 = eval_reg R1 st0 in
               r1_0 == (eval_mem r0' st) /\
               r0 == r0'
             ))
let functional_correctness_aux2_0 st = ()

val functional_correctness_aux2_1: st:arm_state -> Lemma
  (requires (st.ok=true))
  (ensures  (let st1 = eval_cond_ins i1 st in
             let r0' = eval_reg R0 st in
             let r0  = eval_reg R0 st1 in
             let r1' = eval_reg R1 st in
             let r1 = eval_reg R1 st1 in
             let sp = eval_reg SP st1 in
               sp == r1 /\
               r1 == r1' /\
               r0 == r0'
             ))
let functional_correctness_aux2_1 st = ()

val functional_correctness_aux2_2: st:arm_state -> Lemma
  (requires (st.ok=true))
  (ensures  (let st2 = eval_cond_ins i2 st in
             let r0' = eval_reg R0 st in
             let r0 = eval_reg R0 st2 in
             let r1' = eval_reg R1 st in
             let r1 = eval_reg R1 st2 in
             let addr = Int32.int_to_t (add_mod (Int32.v r0') (Int32.v 1l)) in
             let sp' = eval_reg SP st in             
             let sp = eval_reg SP st2 in
              r0 == eval_mem addr st /\
              r1 == r1' /\
              sp' == sp
             ))
let functional_correctness_aux2_2 st = ()

val functional_correctness_aux2_3: st:arm_state -> Lemma
  (requires (st.ok=true))
  (ensures  (let st3 = eval_cond_ins i3 st in
             let r0' = eval_reg R0 st in
             let r0 = eval_reg R0 st3 in
             let r1' = eval_reg R1 st in
             let r1 = eval_reg R1 st3 in
             let sp' = eval_reg SP st in             
             let sp = eval_reg SP st3 in
               bit_n (Int32.v r0) 31 == true /\
               r0  == Int32.int_to_t (logor (Int32.v r0') (Int32.v 1l)) /\
               r1 == r1' /\
               sp' == sp
             ))           
#push-options "--ifuel 50 --fuel 50 --z3rlimit 320"
let functional_correctness_aux2_3 st = ()
#pop-options

val functional_correctness_aux2_4: st:arm_state -> Lemma
  (requires (st.ok=true /\
             (let r0 = eval_reg R0 st in
              bit_n (Int32.v r0) 31 == true)
              ))
  (ensures  (let st4 = eval_cond_ins i4 st in
             let pc  = eval_reg PC st4 in
             let r0'  = eval_reg R0 st in
             let r0  = eval_reg R0 st4 in
             let r1' = eval_reg R1 st in
             let r1 = eval_reg R1 st4 in
             let sp' = eval_reg SP st in             
             let sp = eval_reg SP st4 in
              st4.mem_mode == Thumb16 /\
              sp == sp' /\
              r0 == r0' /\
              r1 == r1' /\
              pc == r0
             ))
let functional_correctness_aux2_4 st = ()


val functional_correctness_aux1: st:arm_state -> Lemma
  (requires (st.ok = true))
  (ensures  (let st' = eval_list_ins cplist st in 
             let st0 = eval_cond_ins i0 st in
             let st1 = eval_cond_ins i1 st0 in
             let st2 = eval_cond_ins i2 st1 in
             let st3 = eval_cond_ins i3 st2 in
             let st4 = eval_cond_ins i4 st3 in
               st' == st4
              ))
let functional_correctness_aux1 st = ()

val functional_correctness_aux2: st:arm_state -> Lemma
  (requires (st.ok = true))
  (ensures  (let st0 = eval_cond_ins i0 st in
             let st1 = eval_cond_ins i1 st0 in
             let st2 = eval_cond_ins i2 st1 in
             let st3 = eval_cond_ins i3 st2 in
             let st4 = eval_cond_ins i4 st3 in
             let r0' = eval_reg R0 st in
             let addr = Int32.int_to_t (add_mod (Int32.v r0') (Int32.v 1l)) in
             let sp = eval_reg SP st4 in
             let r1 = eval_mem r0' st in
             let pc  = eval_reg PC st4 in
             let r0  = eval_reg R0 st4 in
              st4.mem_mode == Thumb16 /\
              sp == r1 /\
              r0 == Int32.int_to_t (logor (Int32.v (eval_mem addr st)) (Int32.v 1l)) /\
              pc == r0               
              ))
#push-options "--ifuel 50 --fuel 50 --z3rlimit 320"
let functional_correctness_aux2 st = 
  let st0 = eval_cond_ins i0 st in
  let st1 = eval_cond_ins i1 st0 in
  let st2 = eval_cond_ins i2 st1 in
  let st3 = eval_cond_ins i3 st2 in
    functional_correctness_aux2_0 st;
    functional_correctness_aux2_1 st0;
    functional_correctness_aux2_2 st1;
    functional_correctness_aux2_3 st2;
    functional_correctness_aux2_4 st3
#pop-options

val functional_correctness: st:arm_state -> Lemma
  (requires (st.ok=true))
  (ensures  (let st1 = eval_list_ins cplist st in
             let r0' = eval_reg R0 st in
             let sp = eval_reg SP st1 in
             let r0 = eval_reg R0 st1 in
             let addr = Int32.int_to_t (add_mod (Int32.v r0') (Int32.v 1l)) in
             let pc = eval_reg PC st1 in
             let r1 = eval_mem r0' st in
               r0 == Int32.int_to_t (logor (Int32.v (eval_mem addr st)) (Int32.v 1l)) /\
               sp == r1 /\
               pc == r0
               ))
let functional_correctness st =
   functional_correctness_aux1 st;functional_correctness_aux2 st

val memory_unmodified: st:arm_state -> Lemma
  (requires (st.ok=true))
  (ensures (let st1 = eval_list_ins cplist st in
            st.mem == st1.mem))
#push-options "--ifuel 50 --fuel 50 --z3rlimit 320"
let memory_unmodified st = ()
#pop-options
