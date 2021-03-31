module Common

#set-options "--fuel 0 --ifuel 0"

module P = Params
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module M = LowStar.Modifies
module S = Common.Spec

open LowStar.BufferOps

inline_for_extraction
val dot (len:U32.t) (lhs rhs:B.buffer U32.t) : HST.Stack U32.t
  (requires fun h0 ->
    B.live h0 lhs /\
    B.live h0 rhs /\
    B.length lhs = U32.v len /\
    B.length rhs = U32.v len)
  (ensures fun h0 r h1 ->
    B.live h1 lhs /\
    B.live h1 rhs /\
    M.modifies M.loc_none h0 h1 /\
    S.dot (U32.v len) (B.as_seq h1 lhs) (B.as_seq h1 rhs) = r)
#push-options "--fuel 1"
let dot len lhs rhs =
  HST.push_frame ();
  let h0 = HST.get () in
  let dst = B.alloca 0ul 1ul in
  let inv h (i:nat) =
    B.live h dst /\
    B.live h lhs /\
    B.live h rhs /\
    B.modifies (B.loc_buffer dst) h0 h /\
    i <= U32.v len /\
    S.dot' i (U32.v len) (B.as_seq h lhs) (B.as_seq h rhs) = B.get h dst 0
  in
  let body (i:U32.t{0 <= U32.v i /\ U32.v i < U32.v len}) : HST.Stack unit
    (requires fun h -> inv h (U32.v i))
    (ensures fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1))
  =
    dst.(0ul) <- dst.(0ul) `U32.add_mod` (lhs.(i) `U32.mul_mod` rhs.(i))
  in
  C.Loops.for 0ul len inv body;
  let ret = dst.(0ul) in
  HST.pop_frame ();
  ret
#pop-options

