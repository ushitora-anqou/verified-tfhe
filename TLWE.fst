module TLWE

#set-options "--fuel 0 --ifuel 0"

module P = Params
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module M = LowStar.Modifies
module S = TLWE.Spec

open LowStar.BufferOps
open Common

val encrypt (a s:B.lbuffer U32.t P.n) (m e:U32.t) : HST.Stack U32.t
  (requires fun h ->
    B.live h a /\
    B.live h s)
  (ensures fun h r h' ->
    B.live h' a /\
    B.live h' s /\
    M.modifies M.loc_none h h' /\
    S.encrypt (B.as_seq h a) (B.as_seq h s) m e = r)
let encrypt a s m e =
  let as = dot (U32.uint_to_t P.n) a s in
  (as `U32.add_mod` m) `U32.add_mod` e

val decrypt (a s:B.lbuffer U32.t P.n) (b:U32.t) : HST.Stack U32.t
  (requires fun h ->
    B.live h a /\
    B.live h s)
  (ensures fun h r h' ->
    B.live h' a /\
    B.live h' s /\
    M.modifies M.loc_none h h' /\
    S.decrypt (B.as_seq h a) (B.as_seq h s) b = r)
let decrypt a s b =
  let as = dot (U32.uint_to_t P.n) a s in
  b `U32.sub_mod` as
