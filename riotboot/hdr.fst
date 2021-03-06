module Hdr

open FStar.Integers
open FStar.Int
open FStar.Int.Cast

module B = LowStar.Buffer
module C = LowStar.Comment
module M = LowStar.Modifies
module P = LowStar.Printf

open FStar.HyperStack.ST
open LowStar.BufferOps
open Riotboot
open Fletcher32

val rb_hdr_t2uint16_t : hdr_t -> d:B.buffer UInt16.t{B.length d > UInt16.v Riotboot.offset_chksum} -> ST unit
 (requires (fun h0 -> B.live h0 d))
 (ensures (fun h0 _ h1 -> (M.modifies (M.loc_buffer d) h0 h1) /\ B.live h1 d))

let rb_hdr_t2uint16_t s d =
  d.(0ul)<- uint32_to_uint16 (s.magic_number); (*from high to low*)
  d.(1ul)<- uint32_to_uint16 (s.magic_number >>^ 16ul);
  d.(2ul)<- uint32_to_uint16 (s.version);
  d.(3ul)<- uint32_to_uint16 (s.version >>^ 16ul);
  d.(4ul)<- uint32_to_uint16 (s.start_addr);
  d.(5ul)<- uint32_to_uint16 (s.start_addr >>^ 16ul);
  ()

val rb_hdr_checksum : b:B.buffer hdr_t{B.length b == 1} -> ST UInt32.t
 (requires (fun h0 -> B.live h0 b))
 (ensures (fun h0 _ h1 -> (M.modifies (M.loc_buffer b) h0 h1) /\ B.live h1 b /\ B.modifies B.loc_none h0 h1))

let rb_hdr_checksum b =
  push_frame ();
  let tb = B.alloca 0us 8ul in 
    rb_hdr_t2uint16_t b.(0ul) tb;
    let res = Fletcher32.fletcher32 offset_chksum tb in
  pop_frame ();
  res

val riotboot_hdr_validate : riotboot_hdr:B.buffer hdr_t{B.length riotboot_hdr == 1} -> ST bool
  (requires (fun h0 -> B.live h0 riotboot_hdr))
  (ensures (fun h0 _ h1 -> B.live h1 riotboot_hdr /\ B.modifies B.loc_none h0 h1))

let riotboot_hdr_validate riotboot_hdr = (*return `true` representing not_validate, return `false` representing validate*)
  let h1 = riotboot_hdr.(0ul) in
  let hc = rb_hdr_checksum riotboot_hdr in
  if (h1.magic_number = riotboot_magic) && (hc = h1.chksum) then 
    false 
  else 
    true
