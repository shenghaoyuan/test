module Hdr.Tot

open FStar.Integers
open FStar.UInt
open FStar.Int.Cast

module L = FStar.List.Tot.Base

open Riotboot.Tot
open Fletcher32.Tot

val rb_hdr_t2uint16_t: hdr:hdr_t -> Tot (d:list UInt16.t{L.length d = offset_chksum})
let rb_hdr_t2uint16_t hdr =
  let d0 = uint32_to_uint16 (hdr.magic_number) in (*from high to low*)
  let d1 = uint32_to_uint16 (hdr.magic_number >>^ 16ul) in
  let d2 = uint32_to_uint16 (hdr.version) in
  let d3 = uint32_to_uint16 (hdr.version >>^ 16ul)in
  let d4 = uint32_to_uint16 (hdr.start_addr) in
  let d5 = uint32_to_uint16 (hdr.start_addr >>^ 16ul) in
  [d0; d1; d2; d3; d4; d5]

val rb_hdr_checksum: b:hdr_t -> Tot UInt32.t
let rb_hdr_checksum b = 
  let l = rb_hdr_t2uint16_t b in
    fletcher32 offset_chksum l
  
val riotboot_hdr_validate : riotboot_hdr:hdr_t -> Tot bool
let rioboot_hdr_validate riotboot_hdr = 
  let hc = rb_hdr_checksum riotboot_hdr in
    if (riotboot_hdr.magic_number = riotboot_magic) && (hc = riotboot_hdr.chksum) then
      false
    else 
      true
