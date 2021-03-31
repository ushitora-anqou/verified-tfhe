module Common.Spec

#set-options "--fuel 0 --ifuel 0"

module P = Params
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module M = LowStar.Modifies

let rec dot' (i len:nat) (lhs rhs:Seq.lseq U32.t len) : Ghost U32.t
  (requires i <= len)
  (ensures fun _ -> True)
  (decreases %[i])
=
  if i = 0 then 0ul
  else
    let open FStar.Seq in
    let head = index lhs (i - 1) `U32.mul_mod` index rhs (i - 1) in
    let rest = dot' (i - 1) len lhs rhs in
    head `U32.add_mod` rest

val dot (len:nat) (lhs rhs:Seq.lseq U32.t len) : GTot U32.t
let dot len lhs rhs =
  dot' len len lhs rhs

