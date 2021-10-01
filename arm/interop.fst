module Interop

open Words_t
open Arm_def
open Arm_semantics
open Valid
open FStar.List.Tot.Base
open Shift
open Properties
open Jump_to_cpu

type qualifiers = | ASMVolatile | ASMInline | ASMGoto

type simp_cons = | RegOp

type modifiers = | CEq | CAdd

type var_name = string

noeq type extended_asm = {
  asm_qualifiers : qualifiers;
  asm_template   : list ins; 
  output_op      : list (option modifiers * simp_cons * var_name);
  input_op       : list (option modifiers * simp_cons * var_name);
  clobbers       : list reg;
  gotolabels     : list string;
}



let cup_jump_to_image_easm: extended_asm = {
  asm_qualifiers = ASMVolatile;
  asm_template   = cplist;
  output_op      = [];
  input_op       = [(None, RegOp, "image_addr")];
  clobbers       = [R0];
  gotolabels     = [];
}
