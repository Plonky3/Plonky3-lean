module

public import P3BinaryDft
public import Plonky3Lean.Proofs.BinaryDft.Network

@[expose] public section

/-!
# The domain transcriptions

The domain point of an index is point(index) of the Cantor table, and it panics exactly when the
index has a set bit at or past the bit width.

The steps table holds the sums beta_1 + ... + beta_(r+1).

The subspace polynomial is the j-th iterate of x^2 + x.
-/

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror p3_binary_dft.domain.mirror

variable {F : Type _} [Field F]

/-! ## Monadic loops that cannot fail -/

theorem foldlM_some {α β : Type _} (f : α → β → Option α) (g : α → β → α)
    (l : List β) (h : ∀ a, ∀ b ∈ l, f a b = some (g a b)) (a : α) :
    l.foldlM f a = some (l.foldl g a) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simp only [List.foldlM_cons, List.foldl_cons, h a b List.mem_cons_self, Option.bind_eq_bind,
      Option.bind_some]
    exact ih (fun a b hb => h a b (List.mem_cons_of_mem _ hb)) _

theorem foldlM_none {α β : Type _} (f : α → β → Option α) {l : List β} {b : β}
    (hb : b ∈ l) (h : ∀ a, f a b = none) (a : α) : l.foldlM f a = none := by
  induction l generalizing a with
  | nil => simp at hb
  | cons b' l ih =>
    rw [List.foldlM_cons]
    rcases List.mem_cons.mp hb with rfl | hb
    · simp [h]
    · cases f a b' <;> simp [ih hb]

theorem mapM_some {α β : Type _} (f : α → Option β) (g : α → β) (l : List α)
    (h : ∀ a ∈ l, f a = some (g a)) : l.mapM f = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.mapM_cons, h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem mapM_none {α β : Type _} (f : α → Option β) {l : List α} {a : α} (ha : a ∈ l)
    (h : f a = none) : l.mapM f = none := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rw [List.mapM_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [h]
    · cases f b <;> simp [ih ha]

/-! ## Points of the domain -/

theorem point_two_mul_add (β : ℕ → F) (a : ℕ) {b : ℕ} (hb : b < 2) :
    point β (2 * a + b) = point (fun q => β (1 + q)) a + if b = 1 then β 0 else 0 := by
  rw [← pow_one 2, point_add_mul β a 1 (by simpa using hb), point_mul_two_pow]
  interval_cases b
  · simp
  · simpa using point_two_pow β 0

theorem domain_point_loop (L : Level F) (p : F) (rem r : ℕ) :
    domain_point.loop L p rem r =
      if rem < 2 ^ (2 ^ L.logBits - r) then some (p + point (fun q => L.cantor (r + q)) rem)
      else none := by
  induction rem using Nat.strong_induction_on generalizing p r with
  | _ rem ih =>
    rw [domain_point.loop]
    by_cases h0 : rem = 0
    · simp [h0]
    simp only [h0, ↓reduceIte]
    have hrem : rem = 2 * (rem / 2) + rem % 2 := (Nat.div_add_mod rem 2).symm
    have hpt : point (fun q => L.cantor (r + q)) rem =
        point (fun q => L.cantor (r + 1 + q)) (rem / 2) + if rem % 2 = 1 then L.cantor r else 0 := by
      conv_lhs => rw [hrem]
      rw [point_two_mul_add _ _ (Nat.mod_lt _ two_pos)]
      simp [add_assoc, add_comm 1]
    by_cases hr : r < 2 ^ L.logBits
    · have hcond : rem / 2 < 2 ^ (2 ^ L.logBits - (r + 1)) ↔ rem < 2 ^ (2 ^ L.logBits - r) := by
        rw [show 2 ^ L.logBits - r = 2 ^ L.logBits - (r + 1) + 1 by omega, pow_succ]; omega
      by_cases hodd : rem % 2 = 1
      · simp only [hodd, ↓reduceIte, Level.cantorBasis, hr, Option.map_some, Option.bind_eq_bind,
          Option.bind_some]
        rw [ih _ (by omega)]
        by_cases hc : rem < 2 ^ (2 ^ L.logBits - r)
        · simp [hc, hcond.mpr hc, hpt, hodd, add_assoc, add_comm (L.cantor r)]
        · simp [hc, mt hcond.mp hc]
      · simp only [hodd, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
        rw [ih _ (by omega)]
        by_cases hc : rem < 2 ^ (2 ^ L.logBits - r)
        · simp [hc, hcond.mpr hc, hpt, hodd]
        · simp [hc, mt hcond.mp hc]
    · have hc : ¬ rem < 2 ^ (2 ^ L.logBits - r) := by rw [Nat.sub_eq_zero_of_le (by omega)]; omega
      simp only [hc, ↓reduceIte]
      by_cases hodd : rem % 2 = 1
      · simp [hodd, Level.cantorBasis, hr]
      · simp only [hodd, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
        rw [ih _ (by omega)]
        have : ¬ rem / 2 < 2 ^ (2 ^ L.logBits - (r + 1)) := by
          rw [Nat.sub_eq_zero_of_le (by omega)]; omega
        simp [this]

/-- The domain point of an index below 2^(2^b) is point(index) of the Cantor table, and any other index panics. -/
theorem domain_point_eq (L : Level F) (index : ℕ) :
    domain_point L index =
      if index < 2 ^ 2 ^ L.logBits then some (point L.cantor index) else none := by
  simp [domain_point, domain_point_loop]

/-- Entry r of the steps table is beta_1 + ... + beta_(r+1); the table panics unless every entry is in the level. -/
theorem domain_point_steps_eq (L : Level F) (count : ℕ) :
    domain_point_steps L count =
      if count < 2 ^ L.logBits then
        some ((List.range count).map fun r => ∑ q ∈ range (r + 1), L.cantor (q + 1))
      else none := by
  unfold domain_point_steps
  split_ifs with h
  · rw [foldlM_some _ (fun acc r => (acc.1 + L.cantor (r + 1), acc.2 ++ [acc.1 + L.cantor (r + 1)]))
      _ (fun a r hr => by simp [Level.cantorBasis, show r + 1 < 2 ^ L.logBits by
        simp at hr; omega])]
    simp only [Option.map_some]
    congr 1
    have key : ∀ c, (List.range c).foldl (fun (acc : F × List F) r =>
        (acc.1 + L.cantor (r + 1), acc.2 ++ [acc.1 + L.cantor (r + 1)])) (0, []) =
        (∑ q ∈ range c, L.cantor (q + 1),
          (List.range c).map fun r => ∑ q ∈ range (r + 1), L.cantor (q + 1)) := by
      intro c
      induction c with
      | zero => simp
      | succ c ih => simp [List.range_succ, List.foldl_append, ih, sum_range_succ]
    rw [key]
  · have hpos : 0 < 2 ^ L.logBits := Nat.two_pow_pos _
    rw [foldlM_none _ (b := 2 ^ L.logBits - 1) (by simp; omega)
      (fun a => by simp [Level.cantorBasis, show 2 ^ L.logBits - 1 + 1 = 2 ^ L.logBits by omega])]
    rfl

/-- The subspace polynomial is the j-th iterate of x^2 + x. -/
theorem subspace_polynomial_eq (j : ℕ) (x : F) : subspace_polynomial j x = sqAddIter j x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [subspace_polynomial, List.range_succ, List.foldl_append, ← subspace_polynomial, ih]
    exact (sqAddIter_succ j x).symm

end Plonky3Lean.Proofs.BinaryDft
