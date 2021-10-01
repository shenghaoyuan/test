module Interface

open FStar.Integers
open FStar.Int
open FStar.Int.Cast

module B = LowStar.Buffer
module C = LowStar.Comment
module M = LowStar.Modifies
module P = LowStar.Printf
module HS= FStar.HyperStack

open FStar.HyperStack.ST
open LowStar.BufferOps
open Riotboot
open Hdr
open Slot

type addr_map 