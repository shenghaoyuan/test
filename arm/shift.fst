module Shift

open FStar.BitVector
open FStar.Int
open FStar.Seq


let tshift_left (#n: pos) (a: int_t n) (s: nat) : Tot (int_t n) = from_vec (shift_left_vec (to_vec a) s)
(* see ARM Compiler V5.06 Figure 10-2 LSR #3 because fstar uses the big endian!!!
*) 

let tshift_right (#n: pos) (a: int_t n) (s: nat) : Tot (int_t n) = from_vec (shift_right_vec (to_vec a) s)
(* see Figure 10-3 LSL #3
 *)

(*
let tshift_arithmetic_right_vec (#n: pos) (a: bv_t n) (s: nat) : bv_t n =
  if index a 0
  then if s >= n then create n (index a (n-1)) else if s = 0 then a else append (slice a s n) (create s (index a (n-1)))
  else shift_right_vec a s
(* Checking ARM Compiler V5.06 Fig10-1 ASR #3
 * The original shift_arithmetic_right_vec is not the real definition of the ASR instruction, so we must redefine it!!! 
 *)
 *)

let tshift_arithmetic_right (#n: pos) (a: int_t n) (s: nat) : Tot (int_t n) = from_vec (shift_arithmetic_right_vec (to_vec a) s)

(*define rotate right ROR*)

let rotate_right_vec (#n: pos) (a: bv_t n) (s:nat) : bv_t n =
  let ts = s % n in
  if ts = 0 then a else append (slice a (n-ts) n) (slice a 0 (n-ts))
(*Figure 10-4 ROR #3
 *)

let rotate_right (#n: pos) (a: int_t n) (s: nat) : Tot (int_t n) = from_vec (rotate_right_vec (to_vec a) s)

(*
val bit_n_aux: #n: pos -> a: bv_t n -> s:nat{s<length a} -> Tot (bv_t 1)
let bit_n_aux #n a s = create 1 (index a s) (*if bit[n] is 0, then return 0 else return 111...11*)

val bit_n: #n: pos -> a: int_t n -> s:nat{s<n} -> Tot (int_t 1)
let bit_n #n a s = from_vec(bit_n_aux (to_vec a) s)*)

val bit_n: #n: pos -> a: int_t n -> s:nat{s<length (to_vec a)} -> Tot bool
let bit_n #n a s = index (to_vec a) s

(*
val lemma_logor_1: x:Int32.t -> Lemma
    (requires True)
    (ensures (let t1 = logor (Int32.v x) (Int32.v 1l) in
              bit_n t1 31 = true))

#push-options "--ifuel 50 --fuel 50 --z3rlimit 320"
let lemma_logor_1 x = ()
#pop-options
*)
(*
val bit_n_aux: #n: pos -> a: bv_t n -> s:nat{s<length a} -> Tot (bv_t n)
let bit_n_aux #n a s = create n (index a s) (*if bit[n] is 0, then return 0 else return 111...11*)

val bit_n: #n: pos -> a: int_t n -> s:nat{s<n} -> Tot (int_t n)
let bit_n #n a s = from_vec(bit_n_aux (to_vec a) s)
 *)
