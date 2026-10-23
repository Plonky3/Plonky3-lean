module

public import P3Field.Coset
public import Plonky3Lean.Proofs.Dft.Glue
public import Plonky3Lean.Spec.Commit

@[expose] public section

/-!
# p3-field: the two-adic coset

Membership, indexing and the generator powers of the transcribed coset, against the set s H.
-/

open p3_field.coset.mirror p3_field.coset.mirror.TwoAdicMultiplicativeCoset p3_dft.mirror Plonky3Lean.Proofs.Dft Plonky3Lean.Spec.Commit

namespace Plonky3Lean.Proofs.Commit

variable {K : Type _} [Field K]

/-- With nested generators, entry k - l of the table is entry k raised to 2^l. -/
theorem gen_sub (G : Gen K) (hN : GenNested G) {k l : ℕ} (hk : k ≤ G.adicity) (hl : l ≤ k) :
    G.gen (k - l) = G.gen k ^ 2 ^ l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [← hN _ (by omega), show k - (l + 1) + 1 = k - l by omega, ih (by omega), ← pow_mul, ← pow_succ]

/-- A point of s H, raised to 2^k, gives s^(2^k). -/
theorem cosetPoints_pow {s ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (i : Fin (2 ^ k)) :
    cosetPoints s ω k i ^ 2 ^ k = s ^ 2 ^ k := by
  rw [cosetPoints, mul_pow, ← pow_mul, mul_comm i.val, pow_mul, hω.pow_eq_one, one_pow, mul_one]

/-- A point lies in s H exactly when its 2^k-th power is s^(2^k). -/
theorem inCoset_iff {s ω x : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0) :
    InCoset s ω k x ↔ x ^ 2 ^ k = s ^ 2 ^ k := by
  refine ⟨fun ⟨i, hi⟩ => hi ▸ cosetPoints_pow hω i, fun h => ?_⟩
  have h1 : (x / s) ^ 2 ^ k = 1 := by rw [div_pow, h, div_self (pow_ne_zero _ hs)]
  obtain ⟨i, hi, hx⟩ := hω.eq_pow_of_pow_eq_one h1
  exact ⟨⟨i, hi⟩, by simp [cosetPoints, hx, mul_div_cancel₀ _ hs]⟩

/-- A returned answer stays returned. -/
theorem foldl_containsStep_inr [DecidableEq K] (m : ℕ) (b : Bool) :
    (List.replicate m ()).foldl (containsStep (K := K)) (.inr b) = .inr b := by
  induction m with
  | zero => rfl
  | succ m ih => simpa [List.replicate_succ, containsStep] using ih

/-- m rounds of the membership loop return true at the first round where the powers agree. -/
theorem foldl_containsStep [DecidableEq K] (m : ℕ) (s e : K) :
    (List.replicate m ()).foldl containsStep (.inl (s, e)) =
      if ∃ j < m, e ^ 2 ^ j = s ^ 2 ^ j then .inr true else .inl (s ^ 2 ^ m, e ^ 2 ^ m) := by
  induction m generalizing s e with
  | zero => simp
  | succ m ih =>
    simp only [List.replicate_succ, List.foldl_cons, containsStep]
    by_cases he : e = s
    · simp [he, foldl_containsStep_inr]
      exact ⟨0, Nat.zero_le _⟩
    · simp only [he, ite_false, ih, ← pow_mul, ← pow_succ']
      congr 1
      · refine propext ⟨fun ⟨j, hj, h⟩ => ⟨j + 1, by omega, h⟩, fun ⟨j, hj, h⟩ => ?_⟩
        rcases j with _ | j
        · exact absurd (by simpa using h) he
        · exact ⟨j, by omega, h⟩

/-- Membership in the transcribed coset is membership in s H. -/
theorem contains_iff [DecidableEq K] {adicity : ℕ} {gen : ℕ → K} (c : TwoAdicMultiplicativeCoset K adicity gen)
    (hω : IsPrimitiveRoot (gen c.log_size) (2 ^ c.log_size)) (x : K) :
    c.contains x = true ↔ InCoset c.shift (gen c.log_size) c.log_size x := by
  rw [inCoset_iff hω c.shift_ne_zero, TwoAdicMultiplicativeCoset.contains, foldl_containsStep]
  have key : (∃ j < c.log_size, x ^ 2 ^ j = c.shift ^ 2 ^ j) → x ^ 2 ^ c.log_size = c.shift ^ 2 ^ c.log_size :=
    fun ⟨j, hj, h⟩ => by
      rw [show c.log_size = j + (c.log_size - j) by omega, pow_add, pow_mul, pow_mul, h]
  split_ifs with h
  · simpa using key h
  · simp

/-- The bit loop multiplies the accumulator by entry i raised to the exponent, while the exponent is below 2^i. -/
theorem generator_exp_loop_eq (G : Gen K) (hN : GenNested G) :
    ∀ (fuel e : ℕ) (acc : K) (i : ℕ), e ≤ fuel → e < 2 ^ i → i ≤ G.adicity →
      generator_exp_loop (gen := G.gen) fuel e acc i = acc * G.gen i ^ e
  | 0, e, acc, i, he, _, _ => by simp [generator_exp_loop, show e = 0 by omega]
  | fuel + 1, e, acc, i, he, hei, hi => by
    unfold generator_exp_loop
    by_cases h0 : e = 0
    · simp [h0]
    have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hei; omega)
    have hg : G.gen (i - 1) = G.gen i ^ 2 := by simpa using gen_sub G hN hi hi1
    simp only [h0, ↓reduceIte]
    rw [generator_exp_loop_eq G hN fuel (e / 2) _ (i - 1) (by omega)
      (by rw [show i = i - 1 + 1 by omega, pow_succ] at hei; omega) (by omega), hg, ← pow_mul]
    split_ifs
    · rw [mul_assoc, ← pow_succ']; congr 2; omega
    · congr 2; omega

/-- The generator power is the subgroup generator raised to the exponent. -/
theorem generator_exp_eq (G : Gen K) (hV : GenValid G) (hN : GenNested G)
    (c : TwoAdicMultiplicativeCoset K G.adicity G.gen) (e : ℕ) :
    c.generator_exp e = c.subgroup_generator ^ e := by
  have hlt : e % c.size < 2 ^ c.log_size := Nat.mod_lt _ (by simp [TwoAdicMultiplicativeCoset.size])
  rw [TwoAdicMultiplicativeCoset.generator_exp,
    generator_exp_loop_eq G hN _ _ _ _ le_rfl hlt c.log_size_le, one_mul,
    TwoAdicMultiplicativeCoset.subgroup_generator]
  rw [TwoAdicMultiplicativeCoset.size, (hV _ c.log_size_le).eq_orderOf, pow_mod_orderOf]

/-- Element i of the coset is the point s omega^i. -/
theorem element_eq (G : Gen K) (hV : GenValid G) (hN : GenNested G)
    (c : TwoAdicMultiplicativeCoset K G.adicity G.gen) (i : ℕ) :
    c.element i = c.shift * c.subgroup_generator ^ i := by
  rw [TwoAdicMultiplicativeCoset.element, generator_exp_eq G hV hN]

end Plonky3Lean.Proofs.Commit
