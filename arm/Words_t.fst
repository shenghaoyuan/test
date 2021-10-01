module Words_t

open FStar.Mul

unfold let pow2_16 = 0x10000
unfold let pow2_32 = 0x100000000

let _ = assert_norm (pow2 16 = pow2_16)
let _ = assert_norm (pow2 32 = pow2_32)

let natN (n:nat) = x:nat{x < n}
let nat16 = natN pow2_16
let nat32 = natN pow2_32

val int_to_natN (n:pos) (i:int) : j:natN n {0 <= i /\ i < n ==> i == j}

//#reset-options "--z3cliopt smt.arish.nl=true"
let int_to_natN n i = i % n
//#reset-options
