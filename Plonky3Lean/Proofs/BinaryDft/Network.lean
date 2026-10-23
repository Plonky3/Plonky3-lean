module

public import Plonky3Lean.Proofs.BinaryDft.Vanishing
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The Lin-Chung-Han network evaluates the novel basis

The forward network runs stage l - 1 first.

That stage splits sum_k d_k X_k into P_0 + W^_(l-1) P_1, with P_0 and P_1 in the first 2^(l-1) basis polynomials.

On the lower half of the domain W^_(l-1) is the twiddle t, and on the upper half it is t + 1:

```text
    lower half:   P_0 + t P_1           coefficients  u_k = d_k + t d_(k + h)
    upper half:   P_0 + (t + 1) P_1     coefficients  v_k = u_k + d_(k + h)
```

The remaining stages are the networks of the two halves, over shift and shift + beta_(l-1).

This is the recursion of Lin, Chung and Han, section III.
-/

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft

variable {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]

/-! ## Row arithmetic of one stage -/

theorem two_pow_succ' (j : ℕ) : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring

/-- Inside c blocks, a row of a lower half has its partner inside too. -/
theorem partner_lt {i c j : ℕ} (hi : i < c * 2 ^ (j + 1)) (hlo : i % 2 ^ (j + 1) < 2 ^ j) :
    i + 2 ^ j < c * 2 ^ (j + 1) := by
  have hq : i / 2 ^ (j + 1) < c := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  have h := Nat.div_add_mod i (2 ^ (j + 1))
  have : 2 ^ (j + 1) * (i / 2 ^ (j + 1) + 1) ≤ 2 ^ (j + 1) * c := Nat.mul_le_mul_left _ hq
  rw [two_pow_succ'] at *
  nlinarith

theorem stage_offset (τ : ℕ → F) (j c : ℕ) (x : ℕ → V) (i : ℕ) :
    stage τ j x (i + c * 2 ^ (j + 1)) =
      stage (fun b => τ (b + c)) j (fun r => x (r + c * 2 ^ (j + 1))) i := by
  have hm : (i + c * 2 ^ (j + 1)) % 2 ^ (j + 1) = i % 2 ^ (j + 1) := Nat.add_mul_mod_self_right _ _ _
  have hd : (i + c * 2 ^ (j + 1)) / 2 ^ (j + 1) = i / 2 ^ (j + 1) + c :=
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)
  simp only [stage, hm, hd]
  split_ifs with h
  · rw [show i + c * 2 ^ (j + 1) + 2 ^ j = i + 2 ^ j + c * 2 ^ (j + 1) by ring]
  · have : 2 ^ j ≤ i := le_trans (not_lt.mp h) (Nat.mod_le _ _)
    rw [show i + c * 2 ^ (j + 1) - 2 ^ j = i - 2 ^ j + c * 2 ^ (j + 1) by omega]

theorem istage_offset (τ : ℕ → F) (j c : ℕ) (x : ℕ → V) (i : ℕ) :
    istage τ j x (i + c * 2 ^ (j + 1)) =
      istage (fun b => τ (b + c)) j (fun r => x (r + c * 2 ^ (j + 1))) i := by
  have hm : (i + c * 2 ^ (j + 1)) % 2 ^ (j + 1) = i % 2 ^ (j + 1) := Nat.add_mul_mod_self_right _ _ _
  have hd : (i + c * 2 ^ (j + 1)) / 2 ^ (j + 1) = i / 2 ^ (j + 1) + c :=
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)
  simp only [istage, hm, hd]
  split_ifs with h
  · rw [show i + c * 2 ^ (j + 1) + 2 ^ j = i + 2 ^ j + c * 2 ^ (j + 1) by ring]
  · have : 2 ^ j ≤ i := le_trans (not_lt.mp h) (Nat.mod_le _ _)
    rw [show i + c * 2 ^ (j + 1) - 2 ^ j = i - 2 ^ j + c * 2 ^ (j + 1) by omega]

theorem stage_congr {τ τ' : ℕ → F} {j c : ℕ} {x x' : ℕ → V} (hτ : ∀ b < c, τ b = τ' b)
    (hx : ∀ i < c * 2 ^ (j + 1), x i = x' i) {i : ℕ} (hi : i < c * 2 ^ (j + 1)) :
    stage τ j x i = stage τ' j x' i := by
  have hq : i / 2 ^ (j + 1) < c := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  simp only [stage, hτ _ hq]
  split_ifs with h
  · rw [hx i hi, hx _ (partner_lt hi h)]
  · rw [hx i hi, hx _ (by omega)]

theorem istage_congr {τ τ' : ℕ → F} {j c : ℕ} {x x' : ℕ → V} (hτ : ∀ b < c, τ b = τ' b)
    (hx : ∀ i < c * 2 ^ (j + 1), x i = x' i) {i : ℕ} (hi : i < c * 2 ^ (j + 1)) :
    istage τ j x i = istage τ' j x' i := by
  have hq : i / 2 ^ (j + 1) < c := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  simp only [istage, hτ _ hq]
  split_ifs with h
  · rw [hx i hi, hx _ (partner_lt hi h)]
  · rw [hx i hi, hx _ (by omega)]

/-- The partner of a lower-half row sits in the upper half of the same block. -/
theorem partner_up {i j : ℕ} (h : i % 2 ^ (j + 1) < 2 ^ j) :
    ¬ (i + 2 ^ j) % 2 ^ (j + 1) < 2 ^ j ∧ (i + 2 ^ j) / 2 ^ (j + 1) = i / 2 ^ (j + 1) := by
  have hr : i % 2 ^ (j + 1) + 2 ^ j < 2 ^ (j + 1) := by rw [two_pow_succ'] at *; omega
  have e : i + 2 ^ j = 2 ^ (j + 1) * (i / 2 ^ (j + 1)) + (i % 2 ^ (j + 1) + 2 ^ j) := by
    have := Nat.div_add_mod i (2 ^ (j + 1)); omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hr]
  simp

/-- The partner of an upper-half row sits in the lower half of the same block. -/
theorem partner_down {i j : ℕ} (h : ¬ i % 2 ^ (j + 1) < 2 ^ j) :
    2 ^ j ≤ i ∧ (i - 2 ^ j) % 2 ^ (j + 1) < 2 ^ j ∧ (i - 2 ^ j) / 2 ^ (j + 1) = i / 2 ^ (j + 1) := by
  have hm := Nat.mod_lt i (Nat.two_pow_pos (j + 1))
  have hr : i % 2 ^ (j + 1) - 2 ^ j < 2 ^ (j + 1) := by omega
  have hle : 2 ^ j ≤ i := le_trans (not_lt.mp h) (Nat.mod_le _ _)
  have e : i - 2 ^ j = 2 ^ (j + 1) * (i / 2 ^ (j + 1)) + (i % 2 ^ (j + 1) - 2 ^ j) := by
    have := Nat.div_add_mod i (2 ^ (j + 1)); omega
  refine ⟨hle, ?_, ?_⟩
  · rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]; rw [two_pow_succ'] at hm; omega
  · rw [e, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hr]; simp

/-! ## The inverse network undoes the forward network -/

section CharTwo

variable [CharP F 2]

theorem istage_stage (τ : ℕ → F) (j : ℕ) (x : ℕ → V) : istage τ j (stage τ j x) = x := by
  funext i
  simp only [istage, stage]
  by_cases h : i % 2 ^ (j + 1) < 2 ^ j
  · obtain ⟨h2, h3⟩ := partner_up h
    simp only [h, h2, h3, ite_true, ite_false, butterfly, ibutterfly, Nat.add_sub_cancel]
    set t := τ (i / 2 ^ (j + 1))
    linear_combination (norm := module) CharTwo.two_eq_zero (R := F) •
      (t • x (i + 2 ^ j) + t • x i + (t * t) • x (i + 2 ^ j))
  · obtain ⟨hle, h2, h3⟩ := partner_down h
    simp only [h, h2, h3, ite_true, ite_false, butterfly, ibutterfly, Nat.sub_add_cancel hle]
    set t := τ (i / 2 ^ (j + 1))
    linear_combination (norm := module) CharTwo.two_eq_zero (R := F) •
      (x (i - 2 ^ j) + t • x i)

theorem stage_istage (τ : ℕ → F) (j : ℕ) (x : ℕ → V) : stage τ j (istage τ j x) = x := by
  funext i
  simp only [istage, stage]
  by_cases h : i % 2 ^ (j + 1) < 2 ^ j
  · obtain ⟨h2, h3⟩ := partner_up h
    simp only [h, h2, h3, ite_true, ite_false, butterfly, ibutterfly, Nat.add_sub_cancel]
    set t := τ (i / 2 ^ (j + 1))
    linear_combination (norm := module) CharTwo.two_eq_zero (R := F) •
      (t • (x i + x (i + 2 ^ j)))
  · obtain ⟨hle, h2, h3⟩ := partner_down h
    simp only [h, h2, h3, ite_true, ite_false, butterfly, ibutterfly, Nat.sub_add_cancel hle]
    set t := τ (i / 2 ^ (j + 1))
    linear_combination (norm := module) CharTwo.two_eq_zero (R := F) •
      (x (i - 2 ^ j) + t • (x (i - 2 ^ j) + x i))

/-- The inverse network undoes the forward network, for any twiddles. -/
theorem inetwork_network (τ : ℕ → ℕ → F) (l : ℕ) (x : ℕ → V) :
    inetwork τ l (network τ l x) = x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih => simp only [network, inetwork, ih, istage_stage]

/-- The forward network undoes the inverse network, for any twiddles. -/
theorem network_inetwork (τ : ℕ → ℕ → F) (l : ℕ) (x : ℕ → V) :
    network τ l (inetwork τ l x) = x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih =>
    simp only [network, inetwork, stage_istage]
    exact ih x

end CharTwo

/-! ## Rows a network reads -/

/-- The network only reads the twiddles of its l stages. -/
theorem network_twiddle_congr {τ τ' : ℕ → ℕ → F} {l : ℕ} (h : ∀ j < l, τ j = τ' j)
    (x : ℕ → V) : network τ l x = network τ' l x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih => simp only [network, h l (Nat.lt_succ_self l), ih fun j hj => h j (by omega)]

theorem blocks_succ {c l j : ℕ} (hj : j < l) :
    c * 2 ^ (l + 1 - 1 - j) = 2 * c * 2 ^ (l - 1 - j) := by
  rw [show l + 1 - 1 - j = l - 1 - j + 1 by omega, pow_succ]; ring

/-- The rows of c whole blocks of 2^l depend only on those rows and their blocks' twiddles. -/
theorem network_congr {τ τ' : ℕ → ℕ → F} {l c : ℕ} {x x' : ℕ → V}
    (hτ : ∀ j < l, ∀ b < c * 2 ^ (l - 1 - j), τ j b = τ' j b)
    (hx : ∀ i < c * 2 ^ l, x i = x' i) {i : ℕ} (hi : i < c * 2 ^ l) :
    network τ l x i = network τ' l x' i := by
  induction l generalizing c x x' with
  | zero => exact hx i hi
  | succ l ih =>
    have e : c * 2 ^ (l + 1) = 2 * c * 2 ^ l := by ring
    refine ih (c := 2 * c) (fun j hj b hb => hτ j (by omega) b ?_) (fun r hr => ?_) (by rwa [← e])
    · rwa [blocks_succ hj]
    · exact stage_congr (c := c) (fun b hb => hτ l (by omega) b (by simpa using hb)) hx
        (by rwa [e])

theorem inetwork_congr {τ τ' : ℕ → ℕ → F} {l c : ℕ} {x x' : ℕ → V}
    (hτ : ∀ j < l, ∀ b < c * 2 ^ (l - 1 - j), τ j b = τ' j b)
    (hx : ∀ i < c * 2 ^ l, x i = x' i) {i : ℕ} (hi : i < c * 2 ^ l) :
    inetwork τ l x i = inetwork τ' l x' i := by
  induction l generalizing c i with
  | zero => exact hx i hi
  | succ l ih =>
    have e : c * 2 ^ (l + 1) = 2 * c * 2 ^ l := by ring
    refine istage_congr (c := c) (fun b hb => hτ l (by omega) b (by simpa using hb))
      (fun r hr => ih (c := 2 * c) (fun j hj b hb => hτ j (by omega) b ?_)
        (fun r hr => hx r (by rwa [e])) (by rwa [← e])) hi
    rwa [blocks_succ hj]

/-- Past c whole blocks of 2^l, the network is that of the rows above, with the blocks renumbered. -/
theorem network_offset (τ : ℕ → ℕ → F) (l c : ℕ) (x : ℕ → V) (i : ℕ) :
    network τ l x (i + c * 2 ^ l) =
      network (fun j b => τ j (b + c * 2 ^ (l - 1 - j))) l (fun r => x (r + c * 2 ^ l)) i := by
  induction l generalizing c x with
  | zero => rfl
  | succ l ih =>
    simp only [network]
    rw [show c * 2 ^ (l + 1) = 2 * c * 2 ^ l by ring, ih,
      network_twiddle_congr (τ' := fun j b => τ j (b + c * 2 ^ (l + 1 - 1 - j))) (fun j hj => ?_)]
    · congr 1; funext r
      rw [show 2 * c * 2 ^ l = c * 2 ^ (l + 1) by ring, stage_offset]; simp
    · funext b; rw [blocks_succ hj]

theorem inetwork_twiddle_congr {τ τ' : ℕ → ℕ → F} {l : ℕ} (h : ∀ j < l, τ j = τ' j)
    (x : ℕ → V) : inetwork τ l x = inetwork τ' l x := by
  induction l generalizing x with
  | zero => rfl
  | succ l ih => simp only [inetwork, h l (Nat.lt_succ_self l), ih fun j hj => h j (by omega)]

/-- Past c whole blocks of 2^l, the inverse network is that of the rows above, with the blocks renumbered. -/
theorem inetwork_offset (τ : ℕ → ℕ → F) (l c : ℕ) (x : ℕ → V) (i : ℕ) :
    inetwork τ l x (i + c * 2 ^ l) =
      inetwork (fun j b => τ j (b + c * 2 ^ (l - 1 - j))) l (fun r => x (r + c * 2 ^ l)) i := by
  induction l generalizing c x i with
  | zero => rfl
  | succ l ih =>
    simp only [inetwork]
    rw [istage_offset]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    congr 1
    funext r
    rw [show c * 2 ^ (l + 1) = 2 * c * 2 ^ l by ring, ih,
      inetwork_twiddle_congr (τ' := fun j b => τ j (b + c * 2 ^ (l + 1 - 1 - j))) (fun j hj => ?_)]
    · rfl
    · funext b; rw [blocks_succ hj]

/-! ## The top stage of a network of 2^(l+1) rows -/

theorem stage_top_low (τ : ℕ → F) (l : ℕ) (d : ℕ → V) {k : ℕ} (hk : k < 2 ^ l) :
    stage τ l d k = d k + τ 0 • d (k + 2 ^ l) := by
  have h1 : k < 2 ^ (l + 1) := by rw [two_pow_succ']; omega
  simp [stage, Nat.mod_eq_of_lt h1, Nat.div_eq_of_lt h1, hk, butterfly]

theorem stage_top_high (τ : ℕ → F) (l : ℕ) (d : ℕ → V) {k : ℕ} (hk : k < 2 ^ l) :
    stage τ l d (k + 2 ^ l) = d k + τ 0 • d (k + 2 ^ l) + d (k + 2 ^ l) := by
  have h1 : k + 2 ^ l < 2 ^ (l + 1) := by rw [two_pow_succ']; omega
  simp [stage, Nat.mod_eq_of_lt h1, Nat.div_eq_of_lt h1, butterfly]

/-! ## Evaluations in the novel basis -/

theorem novelEval_congr (β : ℕ → F) (l : ℕ) {d d' : ℕ → V} (h : ∀ k < 2 ^ l, d k = d' k)
    (x : F) : novelEval β l d x = novelEval β l d' x :=
  sum_congr rfl fun k hk => by rw [h k (mem_range.mp hk)]

/-- Splitting the novel basis at bit l: sum_k d_k X_k = P_0 + W^_l P_1. -/
theorem novelEval_succ (β : ℕ → F) (l : ℕ) (d : ℕ → V) (x : F) :
    novelEval β (l + 1) d x =
      novelEval β l d x + normalized β l x • novelEval β l (fun k => d (k + 2 ^ l)) x := by
  rw [novelEval, two_pow_succ', sum_range_add, novelEval, novelEval, smul_sum]
  congr 1
  · exact sum_congr rfl fun k hk => by rw [novel_succ_low β l (mem_range.mp hk)]
  · refine sum_congr rfl fun k hk => ?_
    rw [add_comm (2 ^ l) k, novel_succ_high β l (mem_range.mp hk), smul_smul, mul_comm]

theorem novelEval_add_smul (β : ℕ → F) (l : ℕ) (a b : ℕ → V) (t x : F) :
    novelEval β l (fun k => a k + t • b k) x = novelEval β l a x + t • novelEval β l b x := by
  simp only [novelEval, smul_add, sum_add_distrib, smul_sum, smul_comm t]

/-! ## The network computes the additive NTT -/

section CharTwo

variable [CharP F 2]

omit [CharP F 2] in
/-- The twiddles of the upper half are those of the coset shifted by beta_l. -/
theorem twiddle_upper (β : ℕ → F) (shift : F) {l j b : ℕ} (hj : j < l)
    (hb : b < 2 ^ (l - 1 - j)) :
    twiddle β shift j (b + 1 * 2 ^ (l - 1 - j)) = twiddle β (shift + β l) j b := by
  have e : (b + 1 * 2 ^ (l - 1 - j)) * 2 ^ (j + 1) = b * 2 ^ (j + 1) + 2 ^ l := by
    rw [one_mul, add_mul, ← pow_add, show l - 1 - j + (j + 1) = l by omega]
  have hlt : b * 2 ^ (j + 1) < 2 ^ l := by
    calc b * 2 ^ (j + 1) < 2 ^ (l - 1 - j) * 2 ^ (j + 1) :=
          Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
      _ = 2 ^ l := by rw [← pow_add, show l - 1 - j + (j + 1) = l by omega]
  rw [twiddle, twiddle, e, point_add_two_pow β hlt]
  congr 1; ring

/-- Lin, Chung and Han, section III: the network of the twiddles W^_j at the block points
evaluates sum_k d_k X_k on the coset shift + S_l, for an independent basis. -/
theorem network_ntt (β : ℕ → F) {n l : ℕ} (hβ : Independent β n) (hl : l ≤ n) (shift : F)
    (d : ℕ → V) {i : ℕ} (hi : i < 2 ^ l) :
    network (twiddle β shift) l d i = ntt β l shift d i := by
  induction l generalizing shift d i with
  | zero =>
    obtain rfl : i = 0 := by simpa using hi
    simp [network, ntt, novelEval, novel]
  | succ l ih =>
    have ht : twiddle β shift l 0 = normalized β l shift := by simp [twiddle]
    simp only [network]
    rw [ntt, novelEval_succ]
    by_cases hlo : i < 2 ^ l
    · rw [ih (by omega) shift _ hlo, ntt, normalized_shift_low β l shift hlo, ← ht,
        ← novelEval_add_smul]
      exact novelEval_congr β l (fun k hk => stage_top_low _ l d hk) _
    · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 ^ l := ⟨i - 2 ^ l, by omega⟩
      have hi' : i < 2 ^ l := by rw [two_pow_succ'] at hi; omega
      rw [← one_mul (2 ^ l), network_offset, one_mul,
        network_congr (V := V) (c := 1) (τ' := twiddle β (shift + β l))
          (fun j hj b hb => twiddle_upper β shift hj (by simpa using hb))
          (fun _ _ => rfl) (by simpa using hi'),
        ih (by omega) _ _ hi', ntt, normalized_shift_high β hβ (by omega) shift hi',
        point_add_two_pow β hi', show shift + (point β i + β l) = shift + β l + point β i by ring,
        ← novelEval_add_smul]
      refine novelEval_congr (V := V) β l (fun k hk => ?_) _
      rw [stage_top_high _ l d hk, ht, add_smul, one_smul, add_assoc]

/-- The inverse network recovers the coefficients from the values on the coset. -/
theorem inetwork_ntt (β : ℕ → F) {n l : ℕ} (hβ : Independent β n) (hl : l ≤ n) (shift : F)
    (d y : ℕ → V) (hy : ∀ i < 2 ^ l, y i = ntt β l shift d i) {i : ℕ} (hi : i < 2 ^ l) :
    inetwork (twiddle β shift) l y i = d i := by
  rw [← inetwork_network (twiddle β shift) l d]
  refine inetwork_congr (c := 1) (fun _ _ _ _ => rfl) (fun r hr => ?_) (by simpa using hi)
  rw [hy r (by simpa using hr), network_ntt β hβ hl shift d (by simpa using hr)]

end CharTwo

end Plonky3Lean.Proofs.BinaryDft
