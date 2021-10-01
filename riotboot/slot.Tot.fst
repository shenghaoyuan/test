module Slot.Tot

open FStar.Integers
open FStar.UInt
open FStar.Int.Cast

module L = FStar.List.Tot.Base

open Fletcher32.Tot
open Hdr.Tot
open Riotboot.Tot

val riotboot_slot_validate: hdr_t -> Tot bool
let riotboot_slot_validate hdr = riotboot_hdr_validate hdr

val choose_image: hdrs_len:nat -> hdrs:list hdr_t{L.length hdrs = hdrs_len} -> Tot (option hdr_t)
let rec choose_image hdrs_len hdrs =
  match hdrs with
  | [] -> None
  | hd :: tl -> 
    let res = choose_image (hdrs_len-1) tl in 
    if riotboot_slot_validate hd then
      res
    else      
       match res with
       | None -> Some hd
       | Some h -> if hd.version <= h.version then res else Some hd

val get_all_validate_images: hdrs:list hdr_t -> Tot (list hdr_t)
let rec get_all_validate_images hdrs =
  match hdrs with
  | [] -> []
  | hd :: tl -> 
    if riotboot_slot_validate hd then
      get_all_validate_images tl 
    else
      hd :: get_all_validate_images tl
  
val lemma_choose_image_validate: hdrs_len:nat -> hdrs:list hdr_t{L.length hdrs = hdrs_len} -> Lemma (requires True)
  (ensures (let res = choose_image hdrs_len hdrs in
            let v_hdrs = get_all_validate_images hdrs in
            match res with
            | None -> v_hdrs = []
            | Some h -> L.mem h v_hdrs /\ (forall h1. L.memP h1 v_hdrs ==> h1.version <= h.version)))

let rec lemma_choose_image_validate hdrs_len hdrs =
  match hdrs with
  | [] -> ()
  | hd :: tl -> if riotboot_slot_validate hd then 
                 lemma_choose_image_validate (hdrs_len -1) tl 
               else 
                 lemma_choose_image_validate (hdrs_len -1) tl
