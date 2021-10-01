module Properties

open Arm_def
open Arm_semantics
open Valid
open Shift

(* property isolation: 
    A processor in one instruction set state cannot execute instructions from another instruction set.
 *)

val isolation_property: i:ins -> st:arm_state -> Lemma
(requires (st.ok=true /\ valid_ins i st))
  (ensures  (let st1 = eval_cond_ins i st in 
            match i with
            | ORN _ _ _ |ORNc _ _ _ _ |ORNs _ _ _ | ORNsc _ _ _ _  -> st.mem_mode == Thumb32 <==> st1.ok == true
            | _ -> st1.ok == true))

#push-options "--ifuel 50 --fuel 50 --z3rlimit 320"
let isolation_property i st = ()
#pop-options

(* property branch: 
    Transformations between different modes only depend on the jump in- struction [i.e. BX in the paper].
 *)

val branch_property_arm: i:ins ->st0:arm_state -> Lemma
  (requires (let st1 = eval_cond_ins i st0 in 
              st0.ok == true /\
              valid_ins i st0 == true /\
              st0.mem_mode == ARM /\
              st1.mem_mode =!= ARM))
  (ensures  (match i with
             | BX _ | BXc _ _ -> True
             | _ -> False))

#push-options "--ifuel 50 --fuel 50 --z3rlimit 320"
let branch_property_arm i st0 = ()
#pop-options

val branch_property: i:ins ->st0:arm_state -> Lemma
  (requires (let st1 = eval_cond_ins i st0 in 
              st0.ok == true /\
              valid_ins i st0 == true /\
              st0.mem_mode =!= st1.mem_mode))
  (ensures  (match i with
             | BX _ | BXc _ _ -> True
             | _ -> False))

#push-options "--ifuel 50 --fuel 50 --z3rlimit 320"
let branch_property i st0 = 
  let m = st0.mem_mode in
    match m with
   | ARM -> branch_property_arm i st0
   | _ -> ()
#pop-options

(* property no-effect: 
    If the condition test of a conditional instruction fails, the instruction has no effect.

 *)

val nop_equiv_nopc: st0:arm_state -> Lemma
  (requires (st0.ok = true))
  (ensures  (forall c. eval_cond_ins NOP st0 == eval_cond_ins (NOPc c) st0))
let nop_equiv_nopc st0 = ()

val nopc_skip: st0:arm_state -> Lemma
  (requires (st0.ok = true))
  (ensures  (forall c . let st1 = eval_cond_ins (NOPc c) st0 in
             update_pc1 st0 == st1))
let nopc_skip st0 = ()

val nopc_flags: st0:arm_state -> Lemma
  (requires (st0.ok = true))
  (ensures  (forall c. let st1 = eval_cond_ins (NOPc c) st0 in
             st0.flags == st1.flags))
let nopc_flags st0 = ()

val nopc_memory_safe: st0:arm_state -> Lemma
  (requires (st0.ok = true))
  (ensures  (forall c. let st1 = eval_cond_ins (NOPc c) st0 in
             st0.ok == st1.ok))
let nopc_memory_safe st0 = () 

val getCondition: i:ins -> st:arm_state -> bool
let getCondition i st = 
  match i with
  | ADCc c _ _ _  | ADCsc c _ _ _ | ADDc c _ _ _ | ADDsc c _ _ _ 
  | ANDc c _ _ _  | ANDsc c _ _ _ | ASRc c _ _ _ | ASRsc c _ _ _
  | BXc  c _      | CMPc  c _ _   | CMNc c _ _
  | EORc c _ _ _  | EORsc c _ _ _ | LDRc c _ _ _  
  | LSLc c _ _ _  | LSLsc c _ _ _ | LSRc c _ _ _ | LSRsc c _ _ _ 
  | MOVc c _ _    | MOVsc c _ _   | MULc c _ _ _ | MULsc c _ _ _
  | NEGc c _ _    | NOPc  c       | ORNc c _ _ _ | ORNsc c _ _ _
  | ORRc c _ _ _  | ORRsc c _ _ _ | RORc c _ _ _ | RORsc c _ _ _ 
  | STRc c _ _ _  | SUBc  c _ _ _ | SUBsc c _ _ _ -> eval_flags c st
  
  | ADC _ _ _  | ADCs _ _ _ | ADD _ _ _ | ADDs _ _ _ 
  | AND _ _ _  | ANDs _ _ _ | ASR _ _ _ | ASRs _ _ _
  | BX  _      | CMP  _ _   | CMN _ _
  | EOR _ _ _  | EORs _ _ _ | LDR _ _ _  
  | LSL _ _ _  | LSLs _ _ _ | LSR _ _ _ | LSRs _ _ _ 
  | MOV _ _    | MOVs _ _   | MUL _ _ _ | MULs _ _ _
  | NEG _ _    | NOP        | ORN _ _ _ | ORNs _ _ _
  | ORR _ _ _  | ORRs _ _ _ | ROR _ _ _ | RORs _ _ _ 
  | STR _ _ _  | SUB _ _ _  | SUBs _ _ _ -> true

val cond_fails_equiv_nop: i:ins -> st:arm_state -> Lemma
  (requires (st.ok = true /\ 
            (valid_ins i st = true) /\
            (getCondition i st = false)))
  (ensures  (let st1 = eval_cond_ins i st in
             let st2 = eval_cond_ins NOP st in
             st1.ok = true /\
             update_pc1 st == st1 /\
             st1 == st2))

#push-options "--ifuel 50 --fuel 50 --z3rlimit 320"
let cond_fails_equiv_nop i st = ()
#pop-options


(* lemma1: list_memory_safety *)

open FStar.List.Tot.Base

val list_cond_ok: l:list ins -> st:arm_state -> Tot bool
let rec list_cond_ok l st =
  match l with
  | [] -> true
  | hd::tl -> if valid_ins hd st then
    let st' = eval_ins hd st in
      list_cond_ok tl st'
    else false

val list_memory_safety: l:list ins -> st:arm_state -> Lemma
  (requires (st.ok=true /\ (list_cond_ok l st)))
  (ensures  (let st1 = eval_list_ins l st in
             st1.ok = true))
let rec list_memory_safety l st =
  match l with
  | [] -> ()
  | hd :: tl -> let st' = eval_ins hd st in
    list_memory_safety tl st'

(* lemma2: load after store *)

val load_after_store_aux: rd: reg -> rn:reg -> o: operand -> st0:arm_state -> ins*ins*arm_state*arm_state
let load_after_store_aux rd rn o st0 = 
 let i0 = STR rd rn o in
 let i1 = LDR rd rn o in
 let st1 = eval_cond_ins i0 st0 in
 let st2 = eval_cond_ins i1 st1 in
  (i0, i1, st1, st2)

val load_after_store: rd: reg -> rn:reg -> o: operand -> st0:arm_state -> Lemma
  (requires (let (i0, i1, st1, st2) = load_after_store_aux rd rn o st0 in
              valid_ins i0 st0 == true /\
              valid_ins i1 st1 == true /\
              st0.ok == true))
  (ensures  (let (i0, i1, st1, st2) = load_after_store_aux rd rn o st0 in
              eval_reg rd st0 == eval_reg rd st1 /\
              eval_reg rd st1 == eval_reg rd st2))
let load_after_store rd rn o st0 = ()
