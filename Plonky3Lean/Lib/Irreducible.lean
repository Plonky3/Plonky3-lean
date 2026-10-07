import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot

/-!
# Irreducibility of `X ^ n - a` over a prime field

mathlib proves `X ^ n - C a` irreducible for odd `n` (`X_pow_sub_C_irreducible_of_odd`)
but not for `n` a power of two, which BabyBear's quartic and octic extensions
need. `X_pow_sub_C_irreducible_of_gcd` covers every `n` over `ZMod q`, with
side conditions that are finite computations on natural numbers.

The argument: a root `α` of an irreducible factor of degree `d` lies in a field
with `q ^ d` elements, so `α ^ (q ^ d - 1) = 1`; and `α ^ n = a` with
`a ^ (q - 1) = 1` gives `α ^ (n * (q - 1)) = 1`. Hence `α` to the gcd of the two
exponents is `1`. If, for every `d < n`, that gcd divides `n * ((q - 1) / ℓ)`,
then `a ^ ((q - 1) / ℓ) = 1`, which the hypothesis `ha` excludes; so every
irreducible factor has degree `n`.
-/

open Polynomial

namespace Plonky3Lean.Lib

/-- `X ^ n - C a` is irreducible over `ZMod q` if `a ≠ 0`, `a ^ ((q - 1) / ℓ) ≠ 1`, and
for every `0 < d < n`, `gcd (q ^ d - 1) (n * (q - 1))` divides `n * ((q - 1) / ℓ)`. -/
theorem X_pow_sub_C_irreducible_of_gcd {q : ℕ} [hq : Fact q.Prime] {n ℓ : ℕ} (hn : 0 < n)
    {a : ZMod q} (ha0 : a ≠ 0) (ha : a ^ ((q - 1) / ℓ) ≠ 1)
    (hd : ∀ d < n, 0 < d → Nat.gcd (q ^ d - 1) (n * (q - 1)) ∣ n * ((q - 1) / ℓ)) :
    Irreducible (X ^ n - C a : (ZMod q)[X]) := by
  set f : (ZMod q)[X] := X ^ n - C a with hf
  have hf0 : f ≠ 0 := (monic_X_pow_sub_C a hn.ne').ne_zero
  have hfdeg : f.natDegree = n := natDegree_X_pow_sub_C
  have hfu : ¬ IsUnit f := by
    intro hu
    have := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg, hgf⟩ := WfDvdMonoid.exists_irreducible_factor hfu hf0
  -- Every irreducible factor has degree at least `n`.
  have hdeg : n ≤ g.natDegree := by
    by_contra hlt
    rw [not_le] at hlt
    have hg0 : g ≠ 0 := hg.ne_zero
    have hdpos : 0 < g.natDegree := Irreducible.natDegree_pos hg
    haveI : Fact (Irreducible g) := ⟨hg⟩
    let L := AdjoinRoot g
    let pb := AdjoinRoot.powerBasis hg0
    haveI : Module.Finite (ZMod q) L := pb.finite
    haveI : Finite L := Module.finite_of_finite (ZMod q)
    letI : Fintype L := Fintype.ofFinite L
    have hcard : Fintype.card L = q ^ g.natDegree := by
      rw [Module.card_eq_pow_finrank (K := ZMod q), ZMod.card, pb.finrank,
        AdjoinRoot.powerBasis_dim]
    set α : L := AdjoinRoot.root g
    have hinj : Function.Injective (AdjoinRoot.of g) := (AdjoinRoot.of g).injective
    have hαn : α ^ n = AdjoinRoot.of g a := by
      have h0 : AdjoinRoot.mk g f = 0 := AdjoinRoot.mk_eq_zero.mpr hgf
      rw [hf, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
      exact h0
    have hα0 : α ≠ 0 := by
      intro h
      rw [h, zero_pow hn.ne'] at hαn
      exact ha0 (hinj (by rw [← hαn, map_zero]))
    have h1 : α ^ (q ^ g.natDegree - 1) = 1 := by
      rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one α hα0
    have h2 : α ^ (n * (q - 1)) = 1 := by
      rw [pow_mul, hαn, ← map_pow, ZMod.pow_card_sub_one_eq_one ha0, map_one]
    have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    obtain ⟨k, hk⟩ := hd g.natDegree hlt hdpos
    have h4 : α ^ (n * ((q - 1) / ℓ)) = 1 := by rw [hk, pow_mul, h3, one_pow]
    rw [pow_mul, hαn, ← map_pow] at h4
    exact ha (hinj (by rw [h4, map_one]))
  obtain ⟨h, hgh⟩ := hgf
  rw [hgh] at hf0 hfdeg ⊢
  have hh0 : h ≠ 0 := by rintro rfl; simp at hf0
  have hdegs := natDegree_mul hg.ne_zero hh0
  have hh : h.natDegree = 0 := by omega
  have hhu : IsUnit h := by
    rw [eq_C_of_natDegree_eq_zero hh]
    exact isUnit_C.mpr (Ne.isUnit (by
      intro hc; apply hh0; rw [eq_C_of_natDegree_eq_zero hh, hc, map_zero]))
  exact (irreducible_mul_isUnit hhu).mpr hg

end Plonky3Lean.Lib
