module Arm_semantics

open Words_t
open Arm_def

open Shift
open Valid

open FStar.Mul
open FStar.Int.Cast
open FStar.Int

(*****************************************************)
(*                       Update                      *)
(*****************************************************)

val update_reg: reg -> int32 -> arm_state -> Tot arm_state
let update_reg r v s = {s with regs = regs_make (fun (r':reg) -> if r = r' then v else s.regs r') }

val update_mem: int32 -> int32 -> arm_state -> Tot arm_state
let update_mem addr v s = {s with mem = store_mem addr v s.mem}

val update_mem_mode: mode -> arm_state -> Tot arm_state
let update_mem_mode m s = {s with mem_mode = m}

(*val eval_reg: reg -> arm_state -> int32*)

unfold let eval_reg (r:reg) (s:arm_state) : Tot int32 = s.regs r

unfold let eval_mem (addr: int32) (s:arm_state) : Tot int32 = load_mem addr s.mem

val eval_operand: operand -> arm_state -> Tot int32 
let eval_operand op s = 
  match op with
  | OConst n -> n
  | OReg r -> eval_reg r s
  | OShift r sh -> let er = eval_reg r s in (match sh with
                  | LSLshift n -> Int32.int_to_t (tshift_left (Int32.v er) n)
                  | LSRshift n -> Int32.int_to_t (tshift_right (Int32.v er) n)
                  | ASRshift n -> Int32.int_to_t (tshift_arithmetic_right (Int32.v er) n)
                  | RORshift n -> Int32.int_to_t (rotate_right (Int32.v er) n))
(*  | OSymbol s -> *)

let eval_shift (sh:shift) : Tot (natN 32) =
  match sh with
  | LSLshift n -> n
  | LSRshift n -> n
  | ASRshift n -> n
  | RORshift n -> n

val eval_flags: condition -> arm_state -> Tot bool
let eval_flags c s =
  let f = s.flags in
  match c with
  | EQ -> f.z
  | NE -> not (f.z)
  | CS -> f.c
  | CC -> not (f.c)
  | MI -> f.n
  | PL -> not (f.n)
  | VS -> f.v
  | VC -> not (f.v)
  | LT -> f.n <> f.v
  | LE -> f.z && (f.n <> f.v)
  | GT -> (not (f.z)) && (f.n = f.v)
  | GE -> f.n = f.v
  | AL -> true

val eval_bool: bool -> int32
let eval_bool b = if b then 1l else 0l

val update_arithmetic_conditions: re:int -> arm_state -> Tot arm_state
let update_arithmetic_conditions re st =
  let tf = st.flags in
  let tn = if re < 0 then true else false in 
  let tz = if re = 0 then true else false in
  let tc = if re > pow2 32 then true else false in
  let tv = if re >= pow2 31 || re < (- pow2 31) then true else false in
  let tf1 = {tf with n = tn; z = tz; c = tc; v = tv;} in
    {st with flags = tf1;}

(* C is set in one of the following ways:
 *  For an addition, including the comparison instruction CMN, 
 *   C is set to 1 if the addition produced a carry (that is, an unsigned overflow), and to 0 otherwise.
 *  For a subtraction, including the comparison instruction CMP, 
 *   C is set to 0 if the subtraction produced a borrow (that is, an unsigned underflow), and to 1 otherwise.
 *  For non-addition/subtractions that incorporate a shift operation, 
 *   C is set to the last bit shifted out of the value by the shifter.
 *  For other non-addition/subtractions, C is normally left unchanged, 
     but see the individual instruction descriptions for any special cases.
 * Overflow occurs if the result of a signed add, subtract, or compare 
 *  is greater than or equal to 231, or less than –231.
 *)

val update_logical_conditions: re:int -> op:operand -> arm_state -> Tot arm_state
let update_logical_conditions re op st =
  let tf = st.flags in
  let tn = if re < 0 then true else false in 
  let tz = if re = 0 then true else false in
  let tc = match op with
           | OConst n -> if FStar.Int32.gte n 255l then (bit_n (Int32.v n) 0) else tf.c
           | _ -> tf.c in
  let tf1 = {tf with n = tn; z = tz; c = tc;} in
    {st with flags = tf1;}

(* Updates the N and Z flags according to the result.
 * Can update the C flag during the calculation of Operand2.
 * Does not affect the V flag.
 *)

(*How to update the C flag during the calculation of Operand2: 
 * When an Operand2 constant is used with the instructions MOVS, MVNS, ANDS, ORRS, ORNS, EORS, BICS, TEQ or TST, 
 * the carry flag is updated to bit[31] of the constant, if 
 *  the constant is greater than 255 and can be produced by shifting an 8-bit value. 
 *  These instructions do not affect the carry flag if Operand2 is any other constant.
 * Note: here bit[31] is the bit[0] in F*, because F* uses the big endian while ARM uses the little endian!!!
 *)


val update_shift_conditions: re:int -> rn:reg -> sh:shift -> arm_state -> Tot arm_state
let update_shift_conditions re rn sh st =
  let tf = st.flags in
  let tn = if re < 0 then true else false in 
  let tz = if re = 0 then true else false in
  let tc = match sh with
          | LSLshift n -> if n = 0 then tf.c else (bit_n (Int32.v (eval_reg rn st)) (n-1)) 
          | LSRshift n | ASRshift n | RORshift n -> if n = 0 then tf.c else (bit_n (Int32.v (eval_reg rn st)) (32-n))
                           in
  let tf1 = {tf with n = tn; z = tz; c = tc;} in
    {st with flags = tf1;}
(* If S is specified, the ASR instruction updates the N and Z flags according to the result.
 * The C flag is unaffected if the shift value is 0. Otherwise, the C flag is updated to the last bit shifted out.
 *)

val eval_conditions: ins -> arm_state -> Tot arm_state
let eval_conditions i st =
  let tf = st.flags in
  let i32v = FStar.Int32.v in
  match i with
  | ADC rd rn op2   | ADCc _ rd rn op2 | ADCs rd rn op2 | ADCsc _ rd rn op2 -> 
    let re:int = i32v (eval_operand rn st) + i32v (eval_operand op2 st) + (i32v (eval_bool tf.c)) in
     update_arithmetic_conditions re st
  | ADD rd rn op2   | ADDc _ rd rn op2 | ADDs rd rn op2 | ADDsc _ rd rn op2 -> 
    let re:int = i32v (eval_reg rn st) + i32v (eval_operand op2 st) in
     update_arithmetic_conditions re st
  | AND rd rn op2   | ANDc _ rd rn op2 | ANDs rd rn op2 | ANDsc _ rd rn op2 -> 
    let re:int = i32v (FStar.Int32.logand (eval_reg rn st) (eval_operand op2 st)) in
     update_logical_conditions re op2 st
  | ASR rd rn rs    | ASRc _ rd rn rs  | ASRs rd rn rs  | ASRsc _ rd rn rs  -> 
    let re:int = i32v (FStar.Int32.int_to_t (tshift_arithmetic_right (i32v (eval_reg rn st)) (eval_shift rs))) in
     update_shift_conditions re rn rs st
  | BX  rm          | BXc _  rm        -> st (*The BX instruction does not change the flags.*)
  | CMP rn op2      | CMPc _ rn op2    -> 
    let re:int = i32v (eval_reg rn st) - i32v (eval_operand op2 st) in
     update_arithmetic_conditions re st
  | CMN rn op2      | CMNc _ rn op2    -> 
    let re:int = i32v (eval_reg rn st) + i32v (eval_operand op2 st) in
     update_arithmetic_conditions re st
  | EOR rd rn op2   | EORc _ rd rn op2 | EORs rd rn op2 | EORsc _ rd rn op2  -> 
    let re:int = i32v (FStar.Int32.logxor (eval_reg rn st) (eval_operand op2 st)) in
     update_logical_conditions re op2 st
  | LDR rt rn o     | LDRc _ rt rn o   -> st
  | LSL rd rn rs    | LSLc _ rd rn rs  | LSLs rd rn rs | LSLsc _ rd rn rs    -> 
    let re:int = i32v (FStar.Int32.int_to_t (tshift_left (i32v (eval_reg rn st)) (eval_shift rs))) in
     update_shift_conditions re rn rs st
  | LSR rd rn rs    | LSRc _ rd rn rs  | LSRs rd rn rs | LSRsc _ rd rn rs    -> 
    let re:int = i32v (FStar.Int32.int_to_t (tshift_right (i32v (eval_reg rn st)) (eval_shift rs))) in
     update_shift_conditions re rn rs st
  | MOV rd op2      | MOVc _ rd op2    | MOVs rd op2    | MOVsc _ rd op2     -> 
    let re:int = i32v (eval_operand op2 st) in
     update_arithmetic_conditions re st (*Can update the C flag during the calculation of Operand2*)
  | MUL rd rn rm    | MULc _ rd rn rm  | MULs rd rn rm  | MULsc _ rd rn rm   -> 
    let re:int = (i32v (eval_reg rn st)) * (i32v (eval_reg rm st)) in
     update_arithmetic_conditions re st
  | NEG rd rm       | NEGc _ rd rm     -> 
    let re:int = 0 - (i32v (eval_reg rm st)) in
     update_arithmetic_conditions re st
  | NOP             | NOPc _          -> st
  | ORN rd rn op2   | ORNc _ rd rn op2 | ORNs rd rn op2 | ORNsc _ rd rn op2  -> 
    let re:int = i32v (FStar.Int32.logor (eval_reg rn st) (FStar.Int32.lognot (eval_operand op2 st))) in
     update_logical_conditions re op2 st
  | ORR rd rn op2   | ORRc _ rd rn op2 | ORRs rd rn op2 | ORRsc _ rd rn op2  -> 
    let re:int = i32v (FStar.Int32.logor (eval_reg rn st) (eval_operand op2 st)) in
     update_logical_conditions re op2 st
  | ROR rd rm rs    | RORc _ rd rm rs  | RORs rd rm rs | RORsc _ rd rm rs    -> 
    let re:int = i32v (FStar.Int32.int_to_t (rotate_right (i32v (eval_reg rm st)) (eval_shift rs))) in
     update_shift_conditions re rm rs st
  | STR rt rn op2   | STRc _ rt rn op2 -> st
  | SUB rd rn op2   | SUBc _ rd rn op2 | SUBs rd rn op2 | SUBsc _ rd rn op2  -> 
    let re:int = i32v (eval_reg rn st) - i32v (eval_operand op2 st) in
     update_arithmetic_conditions re st 

val update_pc1: arm_state -> Tot arm_state
let update_pc1 st = 
  let oldpc:int32 = eval_reg PC st in
  let add1:int32 = Int32.int_to_t (add_mod (Int32.v oldpc) 1) in
  update_reg PC add1 st

(*each time, after run an instruction, the pc normally will add 1, assume the add opration is add_mod*)
(*In ARM processors, all instructions take up one word (4 bytes). Hence incrementing the PC actually adds 4 to its value as memory addresses are given in bytes but aligned on word boundaries.*)

val eval_ocmp: cond:ocmp -> st:arm_state -> Tot bool
let eval_ocmp cond st =
  match cond with
  | OEq o1 o2 -> eval_operand o1 st = eval_operand o2 st
  | ONe o1 o2 -> eval_operand o1 st <> eval_operand o2 st
  | OLe o1 o2 -> Int32.lte (eval_operand o1 st) (eval_operand o2 st)
  | OGe o1 o2 -> Int32.gte (eval_operand o1 st)  (eval_operand o2 st)
  | OLt o1 o2 -> Int32.lt (eval_operand o1 st) (eval_operand o2 st)
  | OGt o1 o2 -> Int32.gt (eval_operand o1 st) (eval_operand o2 st)

(*****************************************************)
(*                     Semantics                     *)
(*****************************************************)

val eval_adc: rd:reg -> rn:operand -> op2:operand -> st:arm_state -> Tot arm_state
let eval_adc rd rn op2 st =
  let tf = st.flags in
  let rn' = Int32.v (eval_operand rn st) in
  let op2' = Int32.v (eval_operand op2 st) in
  let b' = Int32.v (eval_bool tf.c) in
  let re:int32 = Int32.int_to_t (add_mod (add_mod rn' op2') b') in
    update_reg rd re st

val eval_add: rd:reg -> rn:reg -> op2:operand -> st:arm_state -> Tot arm_state 
let eval_add rd rn op2 st =
  let rn' = Int32.v (eval_reg rn st) in
  let op2' = Int32.v (eval_operand op2 st) in
  let re:int32 = Int32.int_to_t (add_mod rn' op2') in
    update_reg rd re st

val eval_and: rd:reg -> rn:reg -> op2:operand -> st:arm_state -> Tot arm_state
let eval_and rd rn op2 st =
  let rn' = Int32.v (eval_reg rn st) in
  let op2' = Int32.v (eval_operand op2 st) in
  let re:int32 = Int32.int_to_t (logand rn' op2') in
    update_reg rd re st

val eval_asr: rd:reg -> rn:reg -> rs:shift -> st:arm_state -> Tot arm_state
let eval_asr rd rn rs st =
  let rn' = Int32.v (eval_reg rn st) in
  let re:int32 = Int32.int_to_t (tshift_arithmetic_right rn' (eval_shift rs)) in
    update_reg rd re st

val eval_bx : rm:reg -> st:arm_state -> Tot arm_state
let eval_bx rm st =
  let rm' = eval_reg rm st in
  let fm: bool = (bit_n (Int32.v rm') 31) in
  let m: mode = if fm then Thumb16 else ARM in
  let st1 = update_reg PC rm' st in
    {st1 with mem_mode = m;}

val eval_eor: rd:reg -> rn:reg -> op2:operand -> st:arm_state -> Tot arm_state
let eval_eor rd rn op2 st =
  let rn' = Int32.v (eval_reg rn st) in
  let op2' = Int32.v (eval_operand op2 st) in
  let re:int32 = Int32.int_to_t (logxor rn' op2') in
    update_reg rd re st

val eval_ldr: rt:reg -> rn:reg -> offset:operand -> st:arm_state -> Tot arm_state
let eval_ldr rt rn offset st = 
  let rn' = Int32.v (eval_reg rn st) in
  let offset' = Int32.v (eval_operand offset st) in
  let addr:int32 = Int32.int_to_t (add_mod rn' offset') in
  let re:int32 = eval_mem addr st in 
    update_reg rt re st

val eval_lsl: rd:reg -> rn:reg -> rs:shift -> st:arm_state -> Tot arm_state
let eval_lsl rd rn rs st =
  let rn' = Int32.v (eval_reg rn st) in
  let re:int32 = Int32.int_to_t (tshift_left rn' (eval_shift rs)) in
    update_reg rd re st

val eval_lsr: rd:reg -> rn:reg -> rs:shift -> st:arm_state -> Tot arm_state
let eval_lsr rd rn rs st =
  let rn' = Int32.v (eval_reg rn st) in
  let re:int32 = Int32.int_to_t (tshift_right rn' (eval_shift rs)) in
    update_reg rd re st 

val eval_mov: rd:reg -> op2:operand -> st:arm_state -> Tot arm_state
let eval_mov rd op2 st =
  let re:int32 = Int32.int_to_t (Int32.v (eval_operand op2 st)) in
    update_reg rd re st

val eval_mul: rd:reg -> rn:reg -> rm:reg -> st:arm_state -> Tot arm_state
let eval_mul rd rn rm st =
  let rn' = Int32.v (eval_reg rn st) in
  let rm' = Int32.v (eval_reg rm st) in
  let re:int32 = Int32.int_to_t (mul_mod rn' rm') in
    update_reg rd re st

val eval_neg: rd:reg -> rm:reg -> st:arm_state -> Tot arm_state
let eval_neg rd rm st =
  let rm' = Int32.v (eval_reg rm st) in
  let re:int32 = Int32.int_to_t (sub_mod 0 rm') in
    update_reg rd re st

val eval_orn: rd:reg -> rn:reg -> op2:operand -> st:arm_state -> Tot arm_state
let eval_orn rd rn op2 st =
  let rn' = Int32.v (eval_reg rn st) in
  let op2' = Int32.v (eval_operand op2 st) in
  let re:int32 = Int32.int_to_t (logor rn' (lognot op2')) in
    update_reg rd re st 

val eval_orr: rd:reg -> rn:reg -> op2:operand -> st:arm_state -> Tot arm_state
let eval_orr rd rn op2 st =
  let rn' = Int32.v (eval_reg rn st) in
  let op2' = Int32.v (eval_operand op2 st) in
  let re:int32 = Int32.int_to_t (logor rn' op2') in
    update_reg rd re st

val eval_ror: rd:reg -> rm:reg -> rs:shift -> st:arm_state -> Tot arm_state
let eval_ror rd rm rs st =
  let rm' = Int32.v (eval_reg rm st) in
  let re:int32 = Int32.int_to_t (rotate_right rm' (eval_shift rs)) in
    update_reg rd re st

val eval_str: rt:reg -> rn:reg -> offset:operand -> st:arm_state -> Tot arm_state
let eval_str rt rn offset st =
  let rn' = Int32.v (eval_reg rn st) in
  let offset' = Int32.v (eval_operand offset st) in
  let addr: int32 = Int32.int_to_t (add_mod rn' offset') in
  let var: int32 = eval_reg rt st in
    update_mem addr var st

val eval_sub: rd:reg -> rn:reg -> op2:operand -> st:arm_state -> Tot arm_state
let eval_sub rd rn op2 st =
  let rn' = Int32.v (eval_reg rn st) in
  let op2' = Int32.v (eval_operand op2 st) in
  let re:int32 = Int32.int_to_t (sub_mod rn' op2') in
    update_reg rd re st


val eval_ins: ins -> arm_state -> Tot arm_state
let eval_ins i st = 
  let tf = st.flags in
  match i with
  | ADC rd rn op2 ->
    let st1 = eval_adc rd rn op2 st in
      update_pc1 st1
  | ADCc cond rd rn op2 ->
    let st1 = if eval_flags cond st then eval_adc rd rn op2 st else st in
      update_pc1 st1
  | ADCs rd rn op2 ->
    let st1 = eval_adc rd rn op2 st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | ADCsc cond rd rn op2 ->    
    let st1 = if eval_flags cond st then 
      let st2 = eval_adc rd rn op2 st in
       eval_conditions i st2
    else st in    
      update_pc1 st1

  | ADD rd rn op2 ->
    let st1 = eval_add rd rn op2 st in
      update_pc1 st1
  | ADDc cond rd rn op2 ->
    let st1 = if eval_flags cond st then eval_add rd rn op2 st else st in
      update_pc1 st1
  | ADDs rd rn op2 ->
    let st1 = eval_add rd rn op2 st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | ADDsc cond rd rn op2 ->   
    let st1 = if eval_flags cond st then 
      let st2 = eval_add rd rn op2 st in
       eval_conditions i st2
    else st in    
      update_pc1 st1


  | AND rd rn op2 ->
    let st1 = eval_and rd rn op2 st in
      update_pc1 st1
  | ANDc cond rd rn op2 ->
    let st1 = if eval_flags cond st then eval_and rd rn op2 st else st in
      update_pc1 st1
  | ANDs rd rn op2 ->
    let st1 = eval_and rd rn op2 st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | ANDsc cond rd rn op2 ->  
    let st1 = if eval_flags cond st then 
      let st2 = eval_and rd rn op2 st in
       eval_conditions i st2
    else st in    
      update_pc1 st1

  
  | ASR rd rn rs  ->
    let st1 = eval_asr rd rn rs st in
      update_pc1 st1  
  | ASRc cond rd rn rs  ->
    let st1 = if eval_flags cond st then eval_asr rd rn rs st else st in
      update_pc1 st1
  | ASRs rd rn rs ->
    let st1 = eval_asr rd rn rs st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | ASRsc cond rd rn rs  ->  
    let st1 = if eval_flags cond st then 
      let st2 = eval_asr rd rn rs st in
       eval_conditions i st2
    else st in    
      update_pc1 st1

  | BX  rm ->
    eval_bx rm st 
  | BXc cond rm ->
   if eval_flags cond st then 
     eval_bx rm st 
   else
     update_pc1 st
  
  
  | CMN rn op2 | CMP rn op2 -> 
    let st1 = eval_conditions i st in
      update_pc1 st1
    
  | CMNc cond rn op2 | CMPc cond rn op2 ->  
    let st1 = if eval_flags cond st then eval_conditions i st else st in
      update_pc1 st1


  | EOR rd rn op2 ->
    let st1 = eval_eor rd rn op2 st in
      update_pc1 st1
  | EORc cond rd rn op2 ->
    let st1 = if eval_flags cond st then eval_eor rd rn op2 st else st in
      update_pc1 st1
  | EORs rd rn op2 ->
    let st1 = eval_eor rd rn op2 st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | EORsc cond rd rn op2 ->
    let st1 = if eval_flags cond st then 
      let st2 = eval_eor rd rn op2 st in
       eval_conditions i st2
    else st in    
      update_pc1 st1
  

  | LDR rt rn o -> 
    let st1 = eval_ldr rt rn o st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | LDRc cond rt rn o -> 
    let st1 = if eval_flags cond st then eval_ldr rt rn o st else st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2


  | LSL rd rn rs  ->
    let st1 = eval_lsl rd rn rs st in
      update_pc1 st1   
  | LSLc cond rd rn rs ->
    let st1 = if eval_flags cond st then eval_lsl rd rn rs st else st in
      update_pc1 st1
  | LSLs rd rn rs ->
    let st1 = eval_lsl rd rn rs st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | LSLsc cond rd rn rs -> 
    let st1 = if eval_flags cond st then 
      let st2 = eval_lsl rd rn rs st in
       eval_conditions i st2
    else st in    
      update_pc1 st1
  
 
  | LSR rd rn rs  ->
    let st1 = eval_lsr rd rn rs st in
      update_pc1 st1   
  | LSRc cond rd rn rs ->
    let st1 = if eval_flags cond st then eval_lsr rd rn rs st else st in
      update_pc1 st1
  | LSRs rd rn rs ->
    let st1 = eval_lsr rd rn rs st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | LSRsc cond rd rn rs -> 
    let st1 = if eval_flags cond st then 
      let st2 = eval_lsr rd rn rs st in
       eval_conditions i st2
    else st in    
      update_pc1 st1


  | MOV rd op2 ->
    let st1 = eval_mov rd op2 st in
      update_pc1 st1  
  | MOVc cond rd op2 ->  
    let st1 = if eval_flags cond st then eval_mov rd op2 st else st in
      update_pc1 st1
  | MOVs rd op2 ->
    let st1 = eval_mov rd op2 st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2 
  | MOVsc cond rd op2 ->
    let st1 = if eval_flags cond st then 
      let st2 = eval_mov rd op2 st in
       eval_conditions i st2
    else st in    
      update_pc1 st1


  | MUL rd rn rm ->
    let st1 = eval_mul rd rn rm st in
      update_pc1 st1 
  | MULc cond rd rn rm -> 
    let st1 = if eval_flags cond st then eval_mul rd rn rm st else st in
      update_pc1 st1 
  | MULs rd rn rm ->
    let st1 = eval_mul rd rn rm st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2 
  | MULsc cond rd rn rm ->
    let st1 = if eval_flags cond st then 
      let st2 = eval_mul rd rn rm st in
       eval_conditions i st2
    else st in    
      update_pc1 st1


  | NEG rd rm -> 
    let st1 = eval_neg rd rm st in
      update_pc1 st1   
  | NEGc cond rd rm ->
    let st1 = if eval_flags cond st then eval_neg rd rm st else st in
      update_pc1 st1 


  | NOP             
  | NOPc _   -> update_pc1 st


  | ORN rd rn op2  -> 
    let st1 = eval_orn rd rn op2 st in
      update_pc1 st1
  | ORNc cond rd rn op2 ->
    let st1 = if eval_flags cond st then eval_orn rd rn op2 st else st in
      update_pc1 st1  
  | ORNs rd rn op2 -> 
    let st1 = eval_orn rd rn op2 st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2 
  | ORNsc cond rd rn op2 -> 
    let st1 = if eval_flags cond st then 
      let st2 = eval_orn rd rn op2 st in
       eval_conditions i st2
    else st in    
      update_pc1 st1


  | ORR rd rn op2 ->
    let st1 = eval_orr rd rn op2 st in
      update_pc1 st1 
  | ORRc cond rd rn op2 ->
    let st1 = if eval_flags cond st then eval_orr rd rn op2 st else st in
      update_pc1 st1
  | ORRs rd rn op2 ->
    let st1 = eval_orr rd rn op2 st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | ORRsc cond rd rn op2  -> 
    let st1 = if eval_flags cond st then 
      let st2 = eval_orr rd rn op2 st in
       eval_conditions i st2
    else st in    
      update_pc1 st1


  | ROR rd rm rs -> 
    let st1 = eval_ror rd rm rs st in
      update_pc1 st1 
  | RORc cond rd rm rs -> 
    let st1 = if eval_flags cond st then eval_ror rd rm rs st else st in
      update_pc1 st1
  | RORs rd rm rs ->
    let st1 = eval_ror rd rm rs st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | RORsc cond rd rm rs ->
    let st1 = if eval_flags cond st then 
      let st2 = eval_ror rd rm rs st in
       eval_conditions i st2
    else st in    
      update_pc1 st1

  
  | STR rt rn op2 ->   
    let st1 = eval_str rt rn op2 st in
      update_pc1 st1 
  | STRc cond rt rn op2 ->
    let st1 = if eval_flags cond st then eval_str rt rn op2 st else st in
      update_pc1 st1

  
  | SUB rd rn op2  ->
    let st1 = eval_sub rd rn op2 st in
      update_pc1 st1 
  | SUBc cond rd rn op2 ->
    let st1 = if eval_flags cond st then eval_sub rd rn op2 st else st in
      update_pc1 st1
  | SUBs rd rn op2 ->
    let st1 = eval_sub rd rn op2 st in
    let st2 = eval_conditions i st1 in
      update_pc1 st2
  | SUBsc cond rd rn op2 ->
    let st1 = if eval_flags cond st then 
      let st2 = eval_sub rd rn op2 st in
       eval_conditions i st2
    else st in    
      update_pc1 st1

val eval_cond_ins:ins -> arm_state -> Tot arm_state
let eval_cond_ins i st = 
  if valid_ins i st then
    eval_ins i st
  else 
    {st with ok = false;}
    

val size_code: c:code -> fuel:nat -> Tot nat
let rec size_code c fuel = 
  match c with
  | Ins i -> 0
  | Block block -> 1+ size_codes block fuel
  | IfElse cond ifTrue ifFalse -> 1 + size_code ifTrue fuel + size_code ifFalse fuel
  | While cond body -> fuel
and size_codes (b:codes) (f:nat): Tot nat =
  match b with
  | [] -> 0
  | hd::tl -> 1+ size_code hd f + (size_codes tl f)


val eval_code: c:code -> fuel:nat -> st:arm_state -> Tot arm_state (decreases %[fuel ; size_code c fuel])
let rec eval_code c fuel st =
  match c with
  | Ins i -> eval_ins i st
  | Block block ->
    (match block with
    | [] -> st
    | hd :: tl -> 
      let st' = eval_code hd fuel st in    
      if st'.ok = false then st
      else
        eval_code (Block tl) fuel st')

  | IfElse cond ifTrue ifFalse ->
    (*if valid_ocmp cond then*)
      if eval_ocmp cond st then 
        eval_code ifTrue fuel st
      else eval_code ifFalse fuel st
    (*else {st with ok = false;}*)

  | While cond body -> 
   (* if valid_ocmp cond then *)
      if eval_ocmp cond st then
        if fuel = 0 then st else
          let st' = eval_code body (fuel - 1) st in
          if st'.ok = false then st else
            eval_code c (fuel - 1) st'
      else st
    (*else {st with ok = false;}*)

val eval_list_ins: l:list ins -> st:arm_state -> Tot arm_state

let rec eval_list_ins l st =
  match l with
  | [] -> st
  | hd :: tl -> let st1 = eval_cond_ins hd st in eval_list_ins tl st1
