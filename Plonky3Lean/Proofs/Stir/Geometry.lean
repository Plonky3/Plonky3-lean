module

public import Plonky3Lean.Proofs.Stir.Ood
public import Plonky3Lean.Proofs.Stir.Virtual

@[expose] public section

/-!
# The domains of a round

A round on L = s <g>, |L| = 2^n, folds by k = 2^a onto L^k = s^k <g^k>.

It commits on L' = s^k w <g^2>, where w is the field's generator.

When w^(2^adicity) != 1, L' meets neither L^k nor any out-of-domain point the filter accepted.

So the next round never reads the virtual oracle at an interpolation point.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset p3_stir.mirror p3_stir.utils.mirror p3_stir.verifier.mirror p3_dft.mirror
open Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- The round's geometry: arity 2^a, fold domain (n - a, s^(2^a)), next domain (n - 1, s^(2^a) w).

It panics for a > n or n = 0. -/
theorem round_geometry_eq (w s : F) (n a : ℕ) :
    round_geometry w s n a =
      if a ≤ n ∧ 1 ≤ n then some (2 ^ a, s ^ 2 ^ a, n - a, n - 1, s ^ 2 ^ a * w) else none := by
  unfold round_geometry fold_domain_params next_domain_shift subChecked
  by_cases ha : a ≤ n <;> by_cases h1 : 1 ≤ n <;> simp [ha, h1]

/-- The point of query j on L^k is (s g^j)^k. -/
theorem fold_point_eq (G : Gen F) (hN : GenNested G) {a n : ℕ} (ha : a ≤ n) (hn : n ≤ G.adicity)
    (s : F) (j : ℕ) :
    s ^ 2 ^ a * G.gen (n - a) ^ j = (s * G.gen n ^ j) ^ 2 ^ a := by
  rw [mul_pow, ← pow_mul, mul_comm j, pow_mul, ← nested_pow hN (k := n - a) (a := a) (by omega),
    show n - a + a = n by omega]

/-- The next domain s^k w <G_m> and the fold domain s^k <G_p> are disjoint when w^(2^adicity) != 1. -/
theorem next_domain_disjoint (G : Gen F) (hG : GenValid G) {w t : F}
    (hw : w ^ 2 ^ G.adicity ≠ 1) (ht : t ≠ 0) {m p : ℕ} (hm : m ≤ G.adicity) (hp : p ≤ G.adicity)
    (i j : ℕ) : t * w * G.gen m ^ i ≠ t * G.gen p ^ j := by
  intro h
  have hm0 : G.gen m ≠ 0 := (hG m hm).ne_zero (by positivity)
  have hw' : w = G.gen p ^ j / G.gen m ^ i := by
    rw [eq_div_iff (pow_ne_zero _ hm0)]
    exact mul_left_cancel₀ ht (by rw [← mul_assoc, h])
  apply hw
  have h1 : ∀ q ≤ G.adicity, ∀ e, (G.gen q ^ e) ^ 2 ^ G.adicity = 1 := fun q hq e => by
    rw [← pow_mul, mul_comm, pow_mul, show 2 ^ G.adicity = 2 ^ q * 2 ^ (G.adicity - q) by
      rw [← pow_add]; congr 1; omega, pow_mul, (hG q hq).pow_eq_one, one_pow, one_pow]
  rw [hw', div_pow, h1 p hp, h1 m hm, div_one]

/-- A point of the next domain is neither an accepted out-of-domain point nor a query point. -/
theorem next_point_not_mem (G : Gen F) (hG : GenValid G) {w s : F} (hw : w ^ 2 ^ G.adicity ≠ 1)
    (hs : s ≠ 0) {a n : ℕ} (ha : a ≤ n) (hn : n ≤ G.adicity)
    (ood qs : List EF)
    (hood : ∀ z ∈ ood, z ^ 2 ^ (n - 1) ≠ algebraMap F EF (s ^ 2 ^ a * w) ^ 2 ^ (n - 1))
    (hq : ∀ y ∈ qs, ∃ j, y = algebraMap F EF (s ^ 2 ^ a * G.gen (n - a) ^ j)) (i : ℕ) :
    algebraMap F EF (s ^ 2 ^ a * w * G.gen (n - 1) ^ i) ∉ ood ++ qs := by
  rw [List.mem_append, not_or]
  constructor
  · intro hz
    apply hood _ hz
    rw [← map_pow, ← map_pow, mul_pow (s ^ 2 ^ a * w), ← pow_mul, mul_comm i, pow_mul,
      (hG (n - 1) (by omega)).pow_eq_one, one_pow, mul_one]
  · intro hy
    obtain ⟨j, hj⟩ := hq _ hy
    exact next_domain_disjoint G hG hw (pow_ne_zero _ hs) (by omega) (by omega) i j
      ((algebraMap F EF).injective hj)

end Plonky3Lean.Proofs.Stir
