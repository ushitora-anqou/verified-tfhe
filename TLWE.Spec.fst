module TLWE.Spec

#set-options "--fuel 0 --ifuel 0"

module P = Params
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module M = LowStar.Modifies

open Common.Spec

val encrypt (a s:Seq.lseq U32.t P.n) (m e:U32.t) : GTot U32.t
let encrypt a s m e =
  let as = dot P.n a s in
  (as `U32.add_mod` m) `U32.add_mod` e

val decrypt (a s:Seq.lseq U32.t P.n) (b:U32.t) : GTot U32.t
let decrypt a s b =
  let as = dot P.n a s in
  b `U32.sub_mod` as

val lem_u32_add_sub_comm (a b c:U32.t) : Lemma (
  (a `U32.add_mod` b) `U32.sub_mod` c = (a `U32.sub_mod` c) `U32.add_mod` b
)
#push-options "--fuel 1 --z3rlimit 0"
let lem_u32_add_sub_comm a b c = ()
#pop-options

val lem_u32_0_add (a:U32.t) : Lemma (0ul `U32.add_mod` a = a)
let lem_u32_0_add _ = ()

val lem_encrypt_decrypt (a s:Seq.lseq U32.t P.n) (m e:U32.t) : Lemma (
  let b = encrypt a s m e in
  let d = decrypt a s b in
  d `U32.sub_mod` m = e
)
#push-options "--z3rlimit 0"
let lem_encrypt_decrypt a s m e =
  let as = dot P.n a s in
  let b = (as `U32.add_mod` m) `U32.add_mod` e in
  let d = b `U32.sub_mod` as in
  calc (==) {
    // as + m + e - as - m
    (((as `U32.add_mod` m) `U32.add_mod` e) `U32.sub_mod` as) `U32.sub_mod` m;
    == {lem_u32_add_sub_comm (as `U32.add_mod` m) e as}
    // as + m - as + e - m
    (((as `U32.add_mod` m) `U32.sub_mod` as) `U32.add_mod` e) `U32.sub_mod` m;
    == {lem_u32_add_sub_comm ((as `U32.add_mod` m) `U32.sub_mod` as) e m}
    // as + m - as - m + e
    (((as `U32.add_mod` m) `U32.sub_mod` as) `U32.sub_mod` m) `U32.add_mod` e;
    == {lem_u32_add_sub_comm as m as}
    // as - as + m - m + e
    (((as `U32.sub_mod` as) `U32.add_mod` m) `U32.sub_mod` m) `U32.add_mod` e;
    == {UInt.lemma_sub_add_cancel (U32.v (as `U32.sub_mod` as)) (U32.v m)}
    // as - as + e
    (as `U32.sub_mod` as) `U32.add_mod` e;
    == {}
    0ul `U32.add_mod` e;
    == {lem_u32_0_add e}
    e;
  };
  ()
#pop-options

