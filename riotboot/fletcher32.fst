module Fletcher32

open FStar.Integers
open FStar.Int
open FStar.Int.Cast

module B = LowStar.Buffer
module C = LowStar.Comment
module P = LowStar.Printf

open FStar.HyperStack.ST
open LowStar.BufferOps
open Riotboot

val dowhile : t:UInt32.t{t>=1ul} -> tlen:UInt32.t{tlen >= 0ul /\ tlen <= t} ->d:(B.buffer UInt16.t){ B.length d > (UInt32.v t)} -> UInt32.t -> UInt32.t ->  ST (UInt32.t & UInt32.t) 
 (requires (fun h0 -> B.live h0 d))
 (ensures (fun h0 _ h1 -> B.live h1 d /\ B.modifies B.loc_none h0 h1))
 (decreases (v tlen))

let rec dowhile t tlen d s1 s2 =
    match tlen with
    | 0ul -> (s1, s2)
    | _ -> 
        let data = UInt32.uint_to_t (UInt16.v (d.(t-tlen))) in       
        let sum1 =UInt32.add_mod s1 data in
        let sum2 = UInt32.add_mod s2 sum1 in
          dowhile t (tlen - 1ul) d sum1 sum2 

val  while_t : (words : UInt16.t{words >= 0us}) -> d: B.buffer UInt16.t{ B.length d > (UInt16.v words)} -> UInt32.t -> UInt32.t -> ST (UInt32.t & UInt32.t) 
 (requires (fun h0 -> B.live h0 d))
 (ensures (fun h0 _ h1 -> B.live h1 d /\ B.modifies B.loc_none h0 h1))
 (decreases (v words))

let rec while_t words data s1 s2 = 
  match words with
  | 0us -> (s1, s2)
  | _ -> 
    let tlen = if words > 359us then 359us else words in
    let tlen_32 = uint16_to_uint32 tlen in
    let (sum1, sum2) = dowhile tlen_32 tlen_32 data s1 s2 in
     while_t (UInt16.sub_mod words tlen) data (UInt32.add_mod (UInt32.logand sum1 0xfffful) (sum1 >>^ 16ul)) (UInt32.add_mod (UInt32.logand sum2 0xfffful) (sum2 >>^ 16ul))

val fletcher32 : words:UInt16.t{words>=0us} -> data:B.buffer UInt16.t{B.length data > UInt16.v words} -> ST UInt32.t  
 (requires (fun h0 -> B.live h0 data))
 (ensures (fun h0 _ h1 -> B.live h1 data /\ B.modifies B.loc_none h0 h1))

let fletcher32 words data =    
  let (s1,s2) = while_t words data 0xfffful 0xfffful in
  let sum1 = UInt32.add_mod (s1 &^ 0xfffful) (s1 >>^ 16ul) in
  let sum2 = UInt32.add_mod (s2 &^ 0xfffful) (s2 >>^ 16ul) in
    (sum2 <<^ 16ul) |^ sum1
