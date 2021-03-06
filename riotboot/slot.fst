module Slot

open FStar.Integers
open FStar.Int
open FStar.Int.Cast

module B = LowStar.Buffer
module C = LowStar.Comment
module M = LowStar.Modifies
module P = LowStar.Printf
module HS = FStar.HyperStack

open FStar.HyperStack.ST
open LowStar.BufferOps
open Fletcher32
open Hdr
open Riotboot

val riotboot_slot_validate : hdr_t ->  ST bool 
 (requires (fun h0 -> True))
 (ensures (fun h0 _ h1 -> B.modifies B.loc_none h0 h1))

let riotboot_slot_validate slot =
 push_frame ();
 let tb = B.alloca slot 1ul in
 let b:bool = Hdr.riotboot_hdr_validate tb in
 pop_frame ();
 b

(* @Kaspar
   riotboot_hdr_t *choose_image(riotboot_hdr_t **hdrs, unsigned hdrs_len)

   This function would get an array of pointers to riotboot headers and the
   length of that array, and return either the chosen image ptr, or NULL.
 *)

val choose_image_aux : hdrs_len:nat{hdrs_len == rb_slot_numof}-> hdrs:B.buffer hdr_t{hdrs_len == B.length hdrs} -> index:nat{0<=index /\ index <= hdrs_len-1} -> option hdr_t -> ST (option hdr_t)
 (requires (fun h0 -> B.live h0 hdrs))
 (ensures  (fun h0 _ h1 -> B.live h1 hdrs))
 (decreases (hdrs_len - 1 - index))

let rec choose_image_aux hdrs_len hdrs index opt =
  match (hdrs_len - 1 - index) with
  | 0 -> 
    let img = hdrs.(UInt32.uint_to_t index) in
    let b = riotboot_slot_validate img in
     if b = false then
      match opt with
      | None -> opt
      | Some t -> 
        if img.version <= t.version then (Some img) else opt
     else
       opt
  | _ -> 
    let img = hdrs.(UInt32.uint_to_t index) in
    let b = riotboot_slot_validate img in
     if b = false then
      match opt with
      | None -> choose_image_aux hdrs_len hdrs (index+1) (Some img)
      | Some t -> 
        if img.version <= t.version then 
          choose_image_aux hdrs_len hdrs (index+1) opt 
        else 
          choose_image_aux hdrs_len hdrs (index+1) (Some img)
     else choose_image_aux hdrs_len hdrs (index+1) opt

val choose_image : hdrs_len:nat{hdrs_len == rb_slot_numof}-> hdrs:B.buffer hdr_t{hdrs_len == B.length hdrs} -> ST (option UInt32.t)
 (requires (fun h0 -> B.live h0 hdrs))
 (ensures  (fun h0 r h1 -> B.live h1 hdrs))

let choose_image hdrs_len hdrs = 
  let res = choose_image_aux hdrs_len hdrs 0 None in
    match res with
   | None -> None
   | Some h -> Some h.start_addr

(*
val choose_image : hdrs_len:nat{hdrs_len == rb_slot_numof}-> hdrs:B.buffer hdr_t{hdrs_len == B.length hdrs} -> ST (B.pointer_or_null hdr_t)
 (requires (fun h0 -> B.live h0 hdrs))
 (ensures  (fun h0 r h1 -> B.live h1 hdrs /\ B.live h1 r))

let choose_image hdrs_len hdrs = 
  let re = choose_image_aux hdrs_len hdrs 0 None in
  match re with
  | None -> B.null
  | Some hdr -> 
    push_frame();
    let image:B.buffer hdr_t = B.gcmalloc HS.root hdr 1ul in
    pop_frame();
    image
*)
