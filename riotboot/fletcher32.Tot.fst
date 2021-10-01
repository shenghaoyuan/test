module Fletcher32.Tot

open FStar.Integers
open FStar.UInt
open FStar.Int.Cast

module L = FStar.List.Tot

(*
val dowhile: words:UInt16.t{words >= 0us} -> data:list UInt16.t{L.length data >= UInt16.v words} -> 
  loc_len:UInt32.t{loc_len >= 0ul /\ loc_len <= 359ul} -> base:UInt32.t{UInt32.v base + UInt32.v loc_len <= UInt16.v words} ->
  loc_index:UInt32.t{loc_index >= 0ul /\ loc_index <= loc_len} -> UInt32.t -> UInt32.t -> Tot (UInt32.t & UInt32.t) 
  (decreases (UInt32.v loc_index))

let rec dowhile words data loc_len base loc_index s1 s2 =
  match loc_index with
  | 0ul -> (s1, s2)
  | _ -> let d =  UInt32.uint_to_t (UInt16.v (L.index data (UInt32.v (base+loc_len-loc_index)))) in       
         let sum1 =UInt32.add_mod s1 d in
         let sum2 = UInt32.add_mod s2 sum1 in
           dowhile words data loc_len base (loc_index - 1ul) sum1 sum2
*)

val dowhile_loc: loc_len:nat{loc_len <= 359} -> data:list UInt16.t{L.length data = loc_len} -> 
  loc_index:nat{loc_index <= loc_len} -> UInt32.t -> UInt32.t -> 
  Tot (UInt32.t & UInt32.t) 
  (decreases loc_index)

let rec dowhile_loc loc_len data loc_index s1 s2 =
  match loc_index with
  | 0 -> (s1, s2)
  | _ -> let d =  UInt32.uint_to_t (UInt16.v (L.index data (loc_len-loc_index))) in       
         let sum1 =UInt32.add_mod s1 d in
         let sum2 = UInt32.add_mod s2 sum1 in
           dowhile_loc loc_len data (loc_index - 1) sum1 sum2

val update_sum12: sum1:UInt32.t -> sum2:UInt32.t -> Tot (UInt32.t & UInt32.t)
let update_sum12 sum1 sum2 =
  let sum11 = UInt32.logand sum1 0xfffful in
  let sum12 = sum1 >>^ 16ul in
  let sum21 = UInt32.logand sum2 0xfffful in
  let sum22 = sum2 >>^ 16ul in
  let s11 = UInt32.add_mod sum11 sum12 in
  let s22 = UInt32.add_mod sum21 sum22 in
    (s11,s22)

let rec lemma_splitAt_fst_length (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires (n <= L.length l))
    (ensures (L.length (fst (L.splitAt n l)) = n)) =
  match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_splitAt_fst_length (n - 1) l'

val while_t: words:nat -> data:list UInt16.t{L.length data >= words} -> s1:UInt32.t -> s2:UInt32.t -> 
  Tot (UInt32.t & UInt32.t) 
  (decreases words)

//#push-options "--ifuel 50 --fuel 50 --z3rlimit 320"
let rec while_t words data s1 s2 =
  match words with
  | 0 -> (s1, s2)
  | _   -> 
    let loc_len = if words > 359 then 359 else words in
    let (loc_l, tl) = L.splitAt loc_len data in (*those two lemmas are necessary!!*)
    lemma_splitAt_fst_length loc_len data; L.lemma_splitAt_snd_length loc_len data; 
    let (tsum1, tsum2) = dowhile_loc loc_len loc_l loc_len s1 s2 in
    let (sum1, sum2) = update_sum12 tsum1 tsum2 in
      while_t (words-loc_len) tl sum1 sum2
//#pop-options

val fletcher32: words:nat -> data: list UInt16.t {L.length data >= words} -> Tot UInt32.t
let fletcher32 words data =     
  let (s1,s2) = while_t words data 0xfffful 0xfffful in
  let sum1 = UInt32.add_mod (s1 &^ 0xfffful) (s1 >>^ 16ul) in
  let sum2 = UInt32.add_mod (s2 &^ 0xfffful) (s2 >>^ 16ul) in
    (sum2 <<^ 16ul) |^ sum1
