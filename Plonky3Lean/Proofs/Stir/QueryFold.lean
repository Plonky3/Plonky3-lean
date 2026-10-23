module

public import Plonky3Lean.Proofs.Stir.Fold
public import Plonky3Lean.Proofs.Stir.FoldPaper
public import Plonky3Lean.Proofs.Stir.Virtual

@[expose] public section

/-!
# The verifier's fold of one query

Query j of a round on L = s <g>, |L| = 2^n, opens the fiber of k = 2^a points s g^(j + l M), M = 2^(n - a).

The verifier reads the fiber through the previous round's virtual oracle and interpolates it at gamma / s.

That value is Fold(f, k, gamma) of Definition 4.8 at (s g^j)^k, the queried point of L^k.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset p3_stir.mirror p3_stir.utils.mirror p3_stir.verifier.mirror p3_dft.mirror
open Plonky3Lean.Proofs.Dft Plonky3Lean.Spec.Stir

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

theorem lift_some_bind {α β : Type} (x : α) (f : α → VM β) :
    (ExceptT.lift (some x) >>= f : VM β) = f x := rfl

theorem lift_some {α : Type} (x : α) : (ExceptT.lift (some x) : VM α) = pure x := rfl

/-- The fiber nodes the verifier builds: g^j (g^M)^l = g^(j + l M). -/
theorem fiber_nodes (g : F) (j M l : ℕ) : g ^ j * (g ^ M) ^ l = g ^ (j + l * M) := by
  rw [← pow_mul, ← pow_add, mul_comm M l]

/-- The interpolation of fiber values at the verifier's nodes, evaluated at gamma / s, is Definition 4.8's fold. -/
theorem lagrange_fiber_eq_fold (G : Gen F) (hG : GenValid G) {a n : ℕ} (ha : a ≤ n)
    (hn : n ≤ G.adicity) (h2 : (2 : F) ≠ 0) {shift : F} (hs : shift ≠ 0) {j : ℕ}
    (hj : j < 2 ^ (n - a)) (vals : List EF) (hvals : vals.length = 2 ^ a) (f : EF → EF)
    (hf : ∀ l < 2 ^ a, f (algebraMap F EF shift * algebraMap F EF (G.gen n) ^ (j + l * 2 ^ (n - a))) =
      vals.getD l 0) (γ : EF) :
    lagrange_interpolate_at (shiftedPowersList (G.gen n ^ 2 ^ (n - a)) (G.gen n ^ j) (2 ^ a)) vals
        (γ * algebraMap F EF shift⁻¹) =
      some (Spec.Stir.fold (cosetSet (algebraMap F EF shift) (algebraMap F EF (G.gen n)) n) f (2 ^ a) γ
        ((algebraMap F EF shift * algebraMap F EF (G.gen n) ^ j) ^ 2 ^ a)) := by
  have hg := hG n hn
  have hζ : IsPrimitiveRoot (G.gen n ^ 2 ^ (n - a)) (2 ^ a) := by
    have := hg.pow_of_dvd (p := 2 ^ (n - a)) (by positivity) (pow_dvd_pow 2 (by omega))
    rwa [Nat.pow_div (by omega) two_pos, show n - (n - a) = a by omega] at this
  have h2a : ((2 ^ a : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_ne_zero _ h2
  have hx0 : G.gen n ^ j ≠ 0 := pow_ne_zero _ (hg.ne_zero (by positivity))
  rw [lagrange_interpolate_at_eq hζ h2a hx0 vals hvals]
  congr 1
  have hnodes : (fun l => algebraMap F EF (G.gen n ^ j * (G.gen n ^ 2 ^ (n - a)) ^ l)) =
      fun l => algebraMap F EF (G.gen n) ^ (j + l * 2 ^ (n - a)) := by
    funext l; rw [fiber_nodes, map_pow]
  rw [hnodes, map_inv₀, ← div_eq_mul_inv]
  refine interp_fiber_eq_fold (hg.map_of_injective (algebraMap F EF).injective)
    (by rw [← pow_add]; congr 1; omega) ((_root_.map_ne_zero _).2 hs) _ f hj (fun l hl => hf l hl) γ

/-- The verifier's fold of a round-0 query is Fold(f, k, gamma) at (s g^j)^k. -/
theorem query_fold_value_initial (G : Gen F) (hG : GenValid G) {a n : ℕ} (ha : a ≤ n)
    (hn : n ≤ G.adicity) (h2 : (2 : F) ≠ 0) {shift : F} (hs : shift ≠ 0) {j : ℕ}
    (hj : j < 2 ^ (n - a)) (row : List EF) (hrow : row.length = 2 ^ a) (f : EF → EF)
    (hf : ∀ l < 2 ^ a, f (algebraMap F EF shift * algebraMap F EF (G.gen n) ^ (j + l * 2 ^ (n - a))) =
      row.getD l 0) (γ : EF) (round : Option ℕ) (q : ℕ) :
    query_fold_value row j (G.gen n) (G.gen n ^ 2 ^ (n - a)) (2 ^ a) shift
        (γ * algebraMap F EF shift⁻¹) none round q =
      pure (Spec.Stir.fold (cosetSet (algebraMap F EF shift) (algebraMap F EF (G.gen n)) n) f (2 ^ a) γ
        ((algebraMap F EF shift * algebraMap F EF (G.gen n) ^ j) ^ 2 ^ a)) := by
  simp only [query_fold_value, materialize_virtual_fiber, liftO]
  rw [lift_some_bind]
  dsimp only
  rw [lagrange_fiber_eq_fold G hG ha hn h2 hs hj row hrow f hf γ, lift_some]

/-- After a round with answers ans on the points pts: a fiber meeting pts is rejected, and otherwise the fold reads the virtual oracle DegCor(Quotient). -/
theorem query_fold_value_virtual (G : Gen F) (hG : GenValid G) {a n : ℕ} (ha : a ≤ n)
    (hn : n ≤ G.adicity) (h2 : (2 : F) ≠ 0) {shift : F} (hs : shift ≠ 0) {j : ℕ}
    (hj : j < 2 ^ (n - a)) (row : List EF) (hrow : row.length = 2 ^ a) (r : EF) (ans pts : List EF)
    (f : EF → EF)
    (hf : ∀ l < 2 ^ a, f (algebraMap F EF shift * algebraMap F EF (G.gen n) ^ (j + l * 2 ^ (n - a))) =
      virtualVal r ans pts (algebraMap F EF shift * algebraMap F EF (G.gen n) ^ (j + l * 2 ^ (n - a)))
        (row.getD l 0)) (γ : EF) (round : Option ℕ) (q : ℕ) :
    query_fold_value row j (G.gen n) (G.gen n ^ 2 ^ (n - a)) (2 ^ a) shift
        (γ * algebraMap F EF shift⁻¹) (some (finish_ctx r ans pts)) round q =
      if ∃ l < 2 ^ a, algebraMap F EF shift * algebraMap F EF (G.gen n) ^ (j + l * 2 ^ (n - a)) ∈ pts then
        throw (StirError.InvalidRoundConsistency round q)
      else pure (Spec.Stir.fold (cosetSet (algebraMap F EF shift) (algebraMap F EF (G.gen n)) n) f
        (2 ^ a) γ ((algebraMap F EF shift * algebraMap F EF (G.gen n) ^ j) ^ 2 ^ a)) := by
  have hg := hG n hn
  have hζ : IsPrimitiveRoot (G.gen n ^ 2 ^ (n - a)) (2 ^ a) := by
    have := hg.pow_of_dvd (p := 2 ^ (n - a)) (by positivity) (pow_dvd_pow 2 (by omega))
    rwa [Nat.pow_div (by omega) two_pos, show n - (n - a) = a by omega] at this
  have hpt : ∀ l, algebraMap F EF (shift * (G.gen n ^ j * (G.gen n ^ 2 ^ (n - a)) ^ l)) =
      algebraMap F EF shift * algebraMap F EF (G.gen n) ^ (j + l * 2 ^ (n - a)) := fun l => by
    rw [fiber_nodes, map_mul, map_pow]
  simp only [query_fold_value, liftO]
  rw [materialize_virtual_fiber_eq hζ (by positivity) row hrow r ans pts]
  simp only [hpt]
  split_ifs with hmem
  · rfl
  · rw [lift_some_bind]
    dsimp only
    have hlen : ((List.range (2 ^ a)).map fun l =>
        virtualVal r ans pts (algebraMap F EF shift * algebraMap F EF (G.gen n) ^ (j + l * 2 ^ (n - a)))
          (row.getD l 0)).length = 2 ^ a := by simp
    rw [lagrange_fiber_eq_fold G hG ha hn h2 hs hj _ hlen f (fun l hl => by
      rw [hf l hl, getD_map_range _ _ hl]) γ, lift_some]

/-- The prover's codeword fold at gamma / s is Definition 4.8's fold of the codeword on s <g>, at every point of L^k. -/
theorem fold_codeword_fold (G : Gen F) (hG : GenValid G) (hN : GenNested G) (h2 : (2 : EF) ≠ 0)
    {a n : ℕ} (ha : a ≤ n) (hn : n ≤ G.adicity) (c : List EF) (hc : c.length = 2 ^ n) {shift : F}
    (hs : shift ≠ 0) (f : EF → EF)
    (hf : ∀ i < 2 ^ n, f (algebraMap F EF shift * algebraMap F EF (G.gen n) ^ i) = c.getD i 0) (γ : EF) :
    fold_codeword G c (γ * algebraMap F EF shift⁻¹) a n =
      some ((List.range (2 ^ (n - a))).map fun j =>
        Spec.Stir.fold (cosetSet (algebraMap F EF shift) (algebraMap F EF (G.gen n)) n) f (2 ^ a) γ
          ((algebraMap F EF shift * algebraMap F EF (G.gen n) ^ j) ^ 2 ^ a)) := by
  rw [fold_codeword_eq G hG hN h2 ha hn c hc]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [map_inv₀, ← div_eq_mul_inv]
  exact foldIdx_eq_fold ((hG n hn).map_of_injective (algebraMap F EF).injective)
    (by rw [← pow_add]; congr 1; omega) ((_root_.map_ne_zero _).2 hs) c f hf (List.mem_range.1 hj) γ

/-- The challenge passed to the fold is gamma / shift, and a zero shift panics. -/
theorem set_gamma_eq (γ : EF) (s : F) :
    set_gamma γ s = if s = 0 then none else some (γ / algebraMap F EF s) := by
  unfold set_gamma p3_stir.mirror.inverse
  split_ifs <;> simp [div_eq_mul_inv, map_inv₀]

/-- The single-fiber fold at gamma / s is Definition 4.8's fold at (s g^j)^(2^a), on L = s <g> of size 2^(m + a). -/
theorem fold_fiber_eq (G : Gen F) (hG : GenValid G) {a m : ℕ} (hn : m + a ≤ G.adicity)
    (h2 : (2 : F) ≠ 0) {shift : F} (hs : shift ≠ 0) {j : ℕ} (hj : j < 2 ^ m) (fiber : List EF)
    (hfib : fiber.length = 2 ^ a) (f : EF → EF)
    (hf : ∀ l < 2 ^ a, f (algebraMap F EF shift * algebraMap F EF (G.gen (m + a)) ^ (j + l * 2 ^ m)) =
      fiber.getD l 0) (γ : EF) :
    fold_fiber G fiber j m a (γ * algebraMap F EF shift⁻¹) =
      some (Spec.Stir.fold (cosetSet (algebraMap F EF shift) (algebraMap F EF (G.gen (m + a))) (m + a)) f
        (2 ^ a) γ ((algebraMap F EF shift * algebraMap F EF (G.gen (m + a)) ^ j) ^ 2 ^ a)) := by
  have hm : m + a - a = m := by omega
  unfold fold_fiber
  simp only [hfib, ne_eq, not_true_eq_false, ↓reduceIte, gen_get_of_le G hn, Option.bind_eq_bind,
    Option.bind_some]
  have := lagrange_fiber_eq_fold G hG (a := a) (n := m + a) (by omega) hn h2 hs (by rw [hm]; exact hj)
    fiber hfib f (by rw [hm]; exact hf) γ
  rw [hm] at this
  exact this

end Plonky3Lean.Proofs.Stir
