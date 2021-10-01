module Valid

open Arm_def

(*we can use the refinement type to replace this valid function*)
(*
let valid_shift (sh:shift): Tot bool = 
  match sh with
  | LSLshift n -> 1 <= n && n <= 31
  | ASRshift n -> 1 <= n && n <= 32
  | LSRshift n -> 1 <= n && n <= 32
  | RORshift n -> 1 <= n && n <= 31
*)

(*
val valid_operand: operand -> Tot bool
let valid_operand op  = true
  match op with
  | OConst n -> true
  | OReg r -> true
  | OShift r' sh -> valid_shift sh
*)

(*
let valid_ocmp (c:ocmp) :bool =
  match c with
  | OEq o1 o2 -> valid_operand o1 && valid_operand o2
  | ONe o1 o2 -> valid_operand o1 && valid_operand o2
  | OLe o1 o2 -> valid_operand o1 && valid_operand o2
  | OGe o1 o2 -> valid_operand o1 && valid_operand o2
  | OLt o1 o2 -> valid_operand o1 && valid_operand o2
  | OGt o1 o2 -> valid_operand o1 && valid_operand o2
*)

val reg_not_in_operand: r:reg -> op:operand -> bool
let reg_not_in_operand r op =
  match op with
  | OConst _ -> true
  | OReg r' -> r<>r'
  | OShift r' _ -> r<>r'
(* | OSymbol _ -> true*)

val not_shift_pc: op:operand -> bool
let not_shift_pc op = 
  match op with
  | OShift r _ -> if r <> PC then true else false
  | _ -> true


val valid_ADC: m:mode -> rd:reg -> rn:operand -> op2:operand -> Tot bool
let valid_ADC m rd rn op2 =
  match m with
  | ARM     -> rd <> PC && not_shift_pc op2
  | Thumb32 | Thumb16 -> rd <> PC && (reg_not_in_operand PC op2)  && rd <> SP && (reg_not_in_operand SP op2)

(* 1. Use of PC and SP in Thumb instructions
 *    You cannot use PC (R15) for Rd, or any operand with the ADC command.
 *    You cannot use SP (R13) for Rd, or any operand with the ADC command.
 * 2. Use of PC and SP in ARM instructions
 *    You cannot use PC for Rd or any operand in any data processing instruction that has a register-controlled shift.
 *    Use of PC for any operand, in instructions without register-controlled shift, is deprecated.
 *   => so we refuse pc in operand!!!
 *)

val exception_pc: reg -> operand -> bool
let exception_pc r op =
  match r with
  | PC -> begin match op with 
         | OConst n -> (0 <= Int32.v n) && (Int32.v n <= 4095)
         | _ -> false
         end
  | _ -> true

val valid_ADD: m:mode -> rd:reg -> rn:reg -> op2:operand -> Tot bool
let valid_ADD m rd rn op2 =
  match m with
  | ARM   ->  rd <> PC && (not_shift_pc op2) && rd <> SP && rn <> SP && (reg_not_in_operand SP op2)
  | Thumb32 -> exception_pc rd op2 && rd <> SP && (reg_not_in_operand SP op2)
  | Thumb16 -> rd <> PC && (reg_not_in_operand PC op2)  && rd <> SP && (reg_not_in_operand SP op2)

(* 1. Use of PC and SP in Thumb instructions
 *    Generally, you cannot use PC (R15) for Rd, or any operand.
 *    The exceptions are:
 *    • you can use PC for Rn in 32-bit encodings of Thumb ADD instructions, with a constant Operand2 value in the range 0-4095, and no S suffix. These instructions are useful for generating PC-relative addresses. Bit[1] of the PC value reads as 0 in this case, so that the base address for the calculation is always word-aligned.
 *    • you can use PC in 16-bit encodings of Thumb ADD{cond} Rd, Rd, Rm instructions, where both registers cannot be PC. (*just forbid*)
 *    Generally, you cannot use SP (R13) for Rd, or any operand. 
 * 2. Use of PC and SP in ARM instructions
 *    You cannot use PC for Rd or any operand in any data processing instruction that has a register-controlled shift.
 *    Other uses of SP in these ARM instructions are deprecated.
 *)

val valid_AND: m:mode -> rd:reg -> rn:reg -> op2:operand -> bool
let valid_AND m rd rn op2 =
  match m with
  | ARM   -> rd <> PC && rd <> SP && rn <> PC && rn <> SP && (reg_not_in_operand PC op2) && (reg_not_in_operand SP op2)
  | Thumb32 | Thumb16 -> rd <> PC && (reg_not_in_operand PC op2)

(* 1.Use of PC in Thumb instructions
 *   You cannot use PC (R15) for Rd or any operand with the AND instruction.
 * 2.Use of PC and SP in ARM instructions
 *   You can use PC and SP with the AND ARM instruction but this is deprecated in ARMv6T2 and above.
 *   You cannot use PC for any operand in any data processing instruction that has a register-controlled shift.
 *)

val valid_ASR: m:mode -> rd:reg -> rn:reg -> rs:shift -> bool
let valid_ASR m rd rn rs = rd <> PC && rd <> SP && rn <> PC && rn <> SP (*&& valid_shift rs*)

(* 1.Restrictions in Thumb code
 *   Thumb instructions must not use PC or SP.
 * 2.Use of SP and PC in ARM instructions
 *   You can use SP in the ASR ARM instruction but this is deprecated in ARMv6T2 and above.
 *   You cannot use PC in instructions with the ASR{S}{cond} Rd, Rm, Rs syntax.
 * 3.Do not use the S suffix when using PC as Rd in User mode or System mode. 
 *)
  
val valid_CMP: m:mode  -> rn:reg -> op2:operand -> bool
let valid_CMP m rn op2 =
  match m with
  | ARM   -> reg_not_in_operand PC op2
  | Thumb32 | Thumb16 -> reg_not_in_operand PC op2

(* 1.Use of PC in ARM and Thumb instructions
 *   You cannot use PC for any operand in any data processing instruction that has a register-controlled shift.
 *   You can use PC (R15) in these ARM instructions without register controlled shift but this is deprecated in ARMv6T2 and above.
 *  => You can not use PC for any operand!!!
 *   You cannot use PC for any operand in these Thumb instructions.
 *)

val valid_EOR: m:mode -> rd:reg -> rn:reg -> op2:operand -> bool
let valid_EOR m rd rn op2 =
  match m with
  | ARM   -> rd <> PC && rd <> SP && rn <> PC && rn <> SP && (reg_not_in_operand PC op2) && (reg_not_in_operand SP op2)
  | Thumb32 | Thumb16 -> rd <> PC && (reg_not_in_operand PC op2)

(* 1.Use of PC in Thumb instructions
 *   You cannot use PC (R15) for Rd or any operand in an EOR instruction.
 * 2.Use of PC and SP in ARM instructions
 *   You can use PC and SP with the EOR instruction but they are deprecated in ARMv6T2 and above.
 *   You cannot use PC for any operand in any data processing instruction that has a register-controlled shift.
 *  => You can not use PC and SP!!!
 *)

val offset_range_arm: offset:operand -> bool
let offset_range_arm offset =
  match offset with
  | OConst n -> (-4095 <= Int32.v n) && (Int32.v n <= 4095)
  | _ -> false

val offset_range_thumb32: offset:operand -> bool
let offset_range_thumb32 offset =
  match offset with
  | OConst n -> (-255 <= Int32.v n) && (Int32.v n <= 4095)
  | _ -> false

val offset_range_thumb16: offset:operand -> bool
let offset_range_thumb16 offset =
  match offset with
  | OConst n -> (0 <= Int32.v n) && (Int32.v n <= 124)
  | _ -> false
(* for LDR, instruction: ARM, word/byte; immediate offset: [-4095,4095]
 *                       Thumb 32-bit encoding, word; immediate offset: [-255,4095]
 *                       Thumb 16-bit encoding, word: immediate offset: [0, 126]
 *)

val valid_LDR: m:mode -> rt:reg -> rn:reg -> offset:operand -> bool
let valid_LDR m rt rn offset =
  match m with
  | ARM     -> offset_range_arm offset && rt <> SP && (reg_not_in_operand PC offset) && (reg_not_in_operand SP offset)
  | Thumb32 -> offset_range_thumb32 offset && rt <> SP && (reg_not_in_operand PC offset) && (reg_not_in_operand SP offset)
  | Thumb16 -> offset_range_thumb16 offset && rt <> SP && (reg_not_in_operand PC offset) && (reg_not_in_operand SP offset)

(* 1.Use of PC
 *   In ARM code you can use PC for Rt in LDR word instructions and PC for Rn in LDR instructions.
 *   Other uses of PC are not permitted in these ARM instructions.
 *  => You can not use PC for any operand!!!
 *   In Thumb code you can use PC for Rt in LDR word instructions and PC for Rn in LDR instructions. 
 *   Other uses of PC in these Thumb instructions are not permitted.
 *  => YOu can not use PC for any operand!!!
 * 2.Use of SP
 * In Thumb code, you can use SP for Rt in word instructions only. All other use of SP for Rt in these
instructions are not permitted in Thumb code.
 *  => You can not use SP for rt or any operands!!! 
 * ===> You can not use SP for rt and can not use PC/SP for any operands!!!
*)

val shift0: s:shift -> bool
let shift0 s = 
  match s with 
  | LSLshift n -> n = 0
  | LSRshift n -> n = 0
  | ASRshift n -> n = 0
  | RORshift n -> n = 0

val not_shift0_in_operand: op:operand -> bool
let not_shift0_in_operand op =
  match op with
  | OShift r s -> not (shift0 s)
  | _ -> true

val valid_LSL: m:mode -> rd:reg -> rn:reg -> rs:shift -> bool
let valid_LSL m rd rn rs =
  match m with
  | ARM               -> rd <> SP && rn <> SP && rd <> PC && rn <> PC (*&& (valid_shift rs)*)
  | Thumb32 | Thumb16 -> rd <> SP && rd<> PC && rn <> SP && rn <> PC (*&& (valid_shift rs)*)

(* 1.Restrictions in Thumb code
 *   Thumb instructions must not use PC or SP.
 *   You cannot specify zero for the sh value in an LSL instruction in an IT block.
 * 2.Use of SP and PC in ARM instructions
 *   You can use SP in these ARM instructions but this is deprecated in ARMv6T2 and above.
 *   You cannot use PC in instructions with the LSL{S}{cond} Rd, Rm, Rs syntax.
 *   Do not use the S suffix when using PC as Rd in User mode or System mode.
 *   You cannot use PC for Rd or any operand in the LSL instruction if it has a register-controlled shift.
 *)

val valid_LSR: m:mode -> rd:reg -> rn:reg -> rs:shift -> bool
let valid_LSR m rd rn rs =
  match m with
  | ARM               -> rd <> SP && rn <> SP && rd <> PC && rn <> PC (*&& (valid_shift rs)*)
  | Thumb32 | Thumb16 -> rd <> SP && rd<> PC && rn <> SP && rd <> PC 
                      (*&& (valid_shift rs)*)

(* 1.Restrictions in Thumb code
 *   Thumb instructions must not use PC or SP.
 * 2.Use of SP and PC in ARM instructions
 *   You can use SP in these ARM instructions but they are deprecated in ARMv6T2 and above.
 *   You cannot use PC in instructions with the LSR{S}{cond} Rd, Rm, Rs syntax.
 *   Do not use the S suffix when using PC as Rd in User mode or System mode.
 *   You cannot use PC for Rd or any operand in the LSR instruction if it has a register-controlled shift.
 *)

val valid_MOV: m:mode -> rd:reg -> op2:operand -> bool
let valid_MOV m rd op2 =
  match m with
  | ARM     -> rd <> PC && not_shift_pc op2
  | Thumb32 -> rd <> PC && (reg_not_in_operand PC op2)
  | Thumb16 -> rd <> PC && (reg_not_in_operand PC op2)
(* 1.Use of PC and SP in 32-bit Thumb encodings
 *   You cannot use PC (R15) for Rd, or in Operand2, in 32-bit Thumb MOV instructions.
 * 2.Use of PC and SP in 16-bit Thumb encodings
 *   You cannot use PC or SP in any other MOV{S} 16-bit Thumb instructions.
 * 3.Use of PC and SP in ARM MOV
 *   You cannot use PC for Rd or any operand in any data processing instruction that has a register-controlled shift.
 *   You can use SP for Rd or Rm. But this is deprecated
 *  => You can not use SP for rd or rm!!!
 *)

val valid_MUL: m:mode -> rd:reg -> rn:reg -> rm:reg -> bool
let valid_MUL m rd rn rm =
  match m with
  | ARM   -> rd <> PC && rn <> PC && rm <> PC
  | Thumb32 | Thumb16 -> rd <> PC && rn <> PC && rm <> PC && rd <> SP && rn <> SP && rm <> SP 

(* 1.Register restrictions
 *   Rn must be different from Rd in architectures before ARMv6. (*we use v7*)
 *   You cannot use PC for any register.
 *   You cannot use SP in Thumb instructions.
 *)

val valid_NEG: m:mode -> rd:reg -> rm:reg -> bool
let valid_NEG m rd rm = rd <> SP && rd <> SP && rm <> SP && rm <> PC

(* 1.Register restrictions
 *   In ARM instructions, using SP or PC for Rd or Rm is deprecated. (*so we forbid*) 
 *   In Thumb instructions, you cannot use SP or PC forRdorRm.
 *)

val valid_ORN: m:mode -> rd:reg -> rn:reg -> op2:operand -> bool
let valid_ORN m rd rn op2 =
  match m with
  | ARM | Thumb16 -> false (*There is no ARM or 16-bit Thumb ORN instructio*)
  | Thumb32 -> rd <> PC && (reg_not_in_operand PC op2) (*You cannot use PC (R15) for Rd or any operand in the ORN instruction.*)

val valid_ORR: m:mode -> rd:reg -> rn:reg -> op2:operand -> bool
let valid_ORR m rd rn op2 =
  match m with
  | ARM     -> rd <> PC && rd <> SP && rn <> PC && rn <> SP && (reg_not_in_operand PC op2) && (reg_not_in_operand SP op2)
  | Thumb32 -> rd <> PC && (reg_not_in_operand PC op2)
  | Thumb16 -> true

(* 1.Use of PC in 32-bit Thumb instructions
 *   You cannot use PC (R15) for Rd or any operand with the ORR instruction.
 * 2.Use of PC and SP in ARM instructions
 *   You can use PC and SP with the ORR instruction but this is deprecated in ARMv6T2 and above.
 *   You cannot use PC for any operand in any data processing instruction that has a register-controlled shift.
 *)

val valid_ROR: m:mode -> rd:reg -> rm:reg -> rs:shift -> bool
let valid_ROR m rd rm rs =
  match m with
  | ARM               -> rd <> SP && rm <> SP && rd <> PC && rm <> PC (*&& (valid_shift rs)*)
  | Thumb32 | Thumb16 -> rd <> SP && rd<> PC && rm <> SP && rm <> PC 
                      (*&& (valid_shift rs)*)

val valid_STR: m:mode -> rt:reg -> rn:reg -> offset:operand -> bool
let valid_STR m rt rn offset =
  match m with
  | ARM   -> offset_range_arm offset && rt <> PC && rn <> PC
  | Thumb32 -> offset_range_thumb32 offset && rt <> PC && rn <> PC 
  | Thumb16 -> offset_range_thumb16 offset && rt <> PC && rn <> PC

(* 1.Offset ranges and architectures
 *   Instruction (ARM, word) Immediate offset [-4095,4095]
                 (Thumb32)                    [-255,4095]
                 (Thumb16)                    [0,124]
 * 2.Use of PC
 *   In ARM instructions you can use PC for Rt in STR word instructions and PC for Rn in STR instructions with immediate offset syntax (that is the forms that do not writeback to the Rn). However, this is deprecated in ARMv6T2 and above.
 *   Other uses of PC are not permitted in these ARM instructions. In Thumb code, using PC in STR instructions is not permitted.
 * 3.Use of SP
 *   In ARM code, you can use SP for Rt in word instructions. You can use SP for Rt in non-word instructions in ARM code but this is deprecated in ARMv6T2 and above.
 *   In Thumb code, you can use SP for Rt in word instructions only. All other use of SP for Rt in this instruction is not permitted in Thumb code.
 *)

val valid_SUB: m:mode -> rd:reg -> rn:reg -> op2:operand -> bool
let valid_SUB m rd rn op2 =
  match m with
  | ARM   -> rd <> PC && (reg_not_in_operand PC op2)  (*omiting the limitaiton of SP in ARM SUB*)
  | Thumb32 | Thumb16 -> rd <> PC && (reg_not_in_operand PC op2) && (exception_pc rn op2) && rd <> SP && (reg_not_in_operand SP op2)

(* 1.Use of PC and SP in Thumb instructions
 *   In general, you cannot use PC (R15) for Rd, or any operand. The exception is you can use PC for Rn in 32-bit Thumb SUB instructions, with a constant Operand2 value in the range 0-4095, and no S suffix. These instructions are useful for generating PC-relative addresses. Bit[1] of the PC value reads as 0 in this case, so that the base address for the calculation is always word-aligned.
 *   Generally, you cannot use SP (R13) for Rd, or any operand, except that you can use SP for Rn.
 * 2.Use of PC and SP in ARM instructions
 *   You cannot use PC for Rd or any operand in a SUB instruction that has a register-controlled shift.
 *   Other uses of SP in ARM SUB instructions are deprecated.
 *)


val valid_ins: i:ins -> arm_state  -> bool
let valid_ins i st =
  let m = st.mem_mode in
  match i with
  | ADC rd rn op2   | ADCc _ rd rn op2 | ADCs rd rn op2 | ADCsc _ rd rn op2 -> valid_ADC m rd rn op2
  
  | ADD rd rn op2   | ADDc _ rd rn op2 | ADDs rd rn op2 | ADDsc _ rd rn op2 -> valid_ADD m rd rn op2
  
  | AND rd rn op2   | ANDc _ rd rn op2 | ANDs rd rn op2 | ANDsc _ rd rn op2 -> valid_AND m rd rn op2
  
  | ASR rd rn rs    | ASRc _ rd rn rs  | ASRs rd rn rs  | ASRsc _ rd rn rs  -> valid_ASR m rd rn rs
  
  | BX  rm          | BXc _  rm                                                 -> true (*no constraints*)
  
  | CMP rn op2      | CMN rn op2       | CMPc _ rn op2    | CMNc _ rn op2       -> valid_CMP m rn op2
  
  | EOR rd rn op2   | EORc _ rd rn op2 | EORs rd rn op2 | EORsc _ rd rn op2 -> valid_EOR m rd rn op2
  
  | LDR rt rn o     | LDRc _ rt rn o                                            -> valid_LDR m rt rn o
  
  | LSL rd rn rs    | LSLc _ rd rn rs                                           -> valid_LSL m rd rn rs
  | LSLs rd rn rs | LSLsc _ rd rn rs                                        -> if m=ARM then false else valid_LSL m rd rn rs
  
  | LSR rd rn rs    | LSRc _ rd rn rs                                           -> valid_LSR m rd rn rs
  | LSRs rd rn rs | LSRsc _ rd rn rs                                        -> if m=ARM then false else valid_LSR m rd rn rs
  
  | MOV rd op2      | MOVc _ rd op2    | MOVs rd op2    | MOVsc _ rd op2    -> valid_MOV m rd op2
  | MUL rd rn rm    | MULc _ rd rn rm  | MULs rd rn rm  | MULsc _ rd rn rm  -> valid_MUL m rd rn rm
  | NEG rd rm       | NEGc _ rd rm                                              -> valid_NEG m rd rm 
  | NOP             | NOPc _                                                    -> true (*no constraints*)
  | ORN rd rn op2   | ORNc _ rd rn op2 | ORNs rd rn op2 | ORNsc _ rd rn op2 -> valid_ORN m rd rn op2
  | ORR rd rn op2   | ORRc _ rd rn op2 | ORRs rd rn op2 | ORRsc _ rd rn op2 -> valid_ORR m rd rn op2
  | ROR rd rm rs    | RORc _ rd rm rs                                           -> valid_ROR m rd rm rs 
  | RORs rd rm rs | RORsc _ rd rm rs                                        -> if m=ARM then false else valid_ROR m rd rm rs
  | STR rt rn op2   | STRc _ rt rn op2                                          -> valid_STR m rt rn op2
  | SUB rd rn op2   | SUBc _ rd rn op2 | SUBs rd rn op2 | SUBsc _ rd rn op2 -> valid_SUB m rd rn op2
