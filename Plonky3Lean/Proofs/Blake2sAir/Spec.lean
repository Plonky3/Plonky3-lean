module

public import Plonky3Lean.Spec.Blake2s
public import P3Blake2sAir

@[expose] public section

/-!
# The RFC 7693 compression, step by step

G writes four words of the working vector and leaves the twelve others.

A round of RFC 7693 is the eight G steps that the AIR's schedule of positions lists.
-/

namespace Plonky3Lean.Proofs.Blake2sAir

open Plonky3Lean.Spec.Blake2s

/-- The four words G writes, from the words it reads and the two message words. -/
def gWords (A B C D X Y : Word) : Word × Word × Word × Word :=
  let a1 := A + B + X
  let d1 := (D ^^^ a1).rotateRight 16
  let c1 := C + d1
  let b1 := (B ^^^ c1).rotateRight 12
  let a2 := a1 + b1 + Y
  let d2 := (d1 ^^^ a2).rotateRight 8
  let c2 := c1 + d2
  (a2, (b1 ^^^ c2).rotateRight 7, c2, d2)

theorem getD_set_of_lt {l : List Word} {i : ℕ} (hi : i < l.length) (a : Word) (j : ℕ) :
    (l.set i a).getD j 0 = if i = j then a else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

/-- G at positions `a`, `4 + b`, `8 + c`, `12 + d` writes the words `gWords` computes there. -/
theorem G_getD {v : List Word} (hv : v.length = 16) {a b c d : ℕ} (ha : a < 4) (hb : b < 4)
    (hc : c < 4) (hd : d < 4) (x y : Word) (k : ℕ) :
    (G v a (4 + b) (8 + c) (12 + d) x y).getD k 0 =
      let w := gWords (v.getD a 0) (v.getD (4 + b) 0) (v.getD (8 + c) 0) (v.getD (12 + d) 0) x y
      if k = a then w.1 else if k = 4 + b then w.2.1 else if k = 8 + c then w.2.2.1
      else if k = 12 + d then w.2.2.2 else v.getD k 0 := by
  have h1 : a ≠ 4 + b := by omega
  have h2 : a ≠ 8 + c := by omega
  have h3 : a ≠ 12 + d := by omega
  have h4 : 4 + b ≠ 8 + c := by omega
  have h5 : 4 + b ≠ 12 + d := by omega
  have h6 : 8 + c ≠ 12 + d := by omega
  simp only [G, getD_set_of_lt, List.length_set, hv, show a < 16 by omega, show 4 + b < 16 by omega,
    show 8 + c < 16 by omega, show 12 + d < 16 by omega, ite_true, h1, h2, h3, h4, h5, h6, h1.symm,
    h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, ite_false, gWords]
  split_ifs <;> first | rfl | omega

theorem length_G {v : List Word} (a b c d : ℕ) (x y : Word) : (G v a b c d x y).length = v.length := by
  simp [G]

/-- G step `g` of round `r`, at the positions and with the message words the schedules give. -/
def gStep (m : List Word) (r : ℕ) (v : List Word) (g : ℕ) : List Word :=
  let sl := p3_blake2s_air.mirror.G_SCHEDULE.getD g []
  let s := p3_blake2s_air.mirror.SIGMA.getD r []
  G v (sl.getD 0 0) (4 + sl.getD 1 0) (8 + sl.getD 2 0) (12 + sl.getD 3 0)
    (m.getD (s.getD (2 * g) 0) 0) (m.getD (s.getD (2 * g + 1) 0) 0)

/-- Round `r` below ten is the eight G steps of the AIR's schedule. -/
theorem round_eq (m v : List Word) {r : ℕ} (hr : r < 10) :
    round m v r = (List.range 8).foldl (gStep m r) v := by
  have hs : p3_blake2s_air.mirror.SIGMA = SIGMA := rfl
  simp only [round, Nat.mod_eq_of_lt hr, gStep, hs, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil, p3_blake2s_air.mirror.G_SCHEDULE,
    List.getD_cons_zero, List.getD_cons_succ, Nat.reduceMul, Nat.reduceAdd]

/-- The ten rounds are the AIR's eighty G steps. -/
theorem rounds_eq (m v : List Word) :
    rounds m v 10 = (List.range 10).foldl (fun v r => (List.range 8).foldl (gStep m r) v) v := by
  rw [rounds]
  exact List.foldl_ext _ _ _ fun v r hr => round_eq m v (List.mem_range.mp hr)

/-- The working vector before the rounds, word by word. -/
theorem init_getD {h : List Word} (hh : h.length = 8) (t : ℕ) (f : Bool) (k : ℕ) :
    (init h t f).getD k 0 =
      if k = 12 then IV.getD 4 0 ^^^ BitVec.ofNat 32 t
      else if k = 13 then IV.getD 5 0 ^^^ BitVec.ofNat 32 (t / 2 ^ 32)
      else if k = 14 then (if f then ~~~IV.getD 6 0 else IV.getD 6 0)
      else (h ++ IV).getD k 0 := by
  have hl : (h ++ IV).length = 16 := by simp [hh, IV]
  have e12 : (h ++ IV).getD 12 0 = IV.getD 4 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega), hh]
  have e13 : (h ++ IV).getD 13 0 = IV.getD 5 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega), hh]
  have e14 : (h ++ IV).getD 14 0 = IV.getD 6 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega), hh]
  cases f <;> simp only [init, Bool.false_eq_true, ite_true, ite_false, getD_set_of_lt,
    List.length_set, hl, e12, e13, e14, show 12 < 16 by omega, show 13 < 16 by omega,
    show 14 < 16 by omega] <;> split_ifs <;> first | rfl | omega | (subst_vars; exact e14)

end Plonky3Lean.Proofs.Blake2sAir
