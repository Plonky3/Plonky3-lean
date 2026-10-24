module

public import Plonky3Lean.Proofs.UniStark.Completeness
public import Plonky3Lean.Proofs.UniStark.Zk

@[expose] public section

/-!
# The check at zeta accepts a zero-knowledge proof

The hiding commitment masks quotient chunk i by Z_i times a random polynomial.

The masks cancel in the recombination, so the verifier still recovers Q(zeta) and accepts.
-/

namespace Plonky3Lean.Proofs.UniStark

open Polynomial Finset
open p3_air.builder.mirror p3_air.air.mirror p3_air.symbolic.mirror p3_uni_stark.folder.mirror
open p3_uni_stark.prover.mirror p3_uni_stark.verifier.mirror
open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark
open Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Dft Plonky3Lean.Proofs.Air

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K] [DecidableEq K]

/-- Completeness of the identity at zeta on masked quotient chunks.

The hypotheses are those of the unmasked check, except for the chunk openings.

Each chunk opens to its interpolant plus Z_i times its mask, for any choice of the first masks.

The last mask balances the others, as the hiding commitment computes it.

Then the recombined quotient is still Q(zeta), and the check at zeta accepts it. -/
theorem honest_ood_check_masked (GK : Gen K) (hV : GenValid GK) (hN : GenNested GK) (h2 : (2 : K) ≠ 0)
    {air : Air F} (hb : air.public_boundary_io = []) (c : Coset GK) {s ω : F}
    (hcs : c.shift = algebraMap F K s) (hcg : c.subgroup_generator = algebraMap F K ω)
    (hω : IsPrimitiveRoot ω (2 ^ c.log_size)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ c.log_size) {main prep periodic : ℕ → F[X]} {pv : List F}
    (hmain : ∀ i < 2 ^ c.log_size, ∀ j, (main j).eval (s * ω ^ i) = T.main i j)
    (hprep : ∀ i < 2 ^ c.log_size, ∀ j, (prep j).eval (s * ω ^ i) = T.prep i j)
    (hpub : ∀ j, pv.getD j 0 = T.pub j)
    (hper : ∀ i < 2 ^ c.log_size, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    (hpv : pv.length = air.num_public_values)
    (hsat : SatisfiesStark (constraints air) T ω)
    (qd : Coset GK) {L : ℕ} (hqd : qd.log_size = L + c.log_size)
    (hfit : ∀ e ∈ constraints air, FitsChunks (2 ^ c.log_size) (2 ^ L)
      (constraintPoly (starkAssign s ω c.log_size main prep (pv.getD · 0) periodic) e))
    {D : ℕ} (B : Module.Basis (Fin D) F K) (α ζ : K) (t : ℕ → K[X]) (chunks : List (List K))
    (hlen : chunks.length = 2 ^ L)
    (hv : ∀ i (hi : i < 2 ^ L), from_ext_basis_coefficients B (chunks[i]'(hlen ▸ hi)) =
      some ((chunkInterp hV qd L (quotientPoly c.shift c.subgroup_generator c.log_size
        (combinedPoly α (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
          (constraints air))) i + chunkZ hV qd L i * mask hV qd L t i).eval ζ))
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ) {pl pn : Option (List K)}
    (hpre : (pl = some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
        (.prep 0) air.preprocessed_width ζ) ∧
      pn = some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
        (.prep 1) air.preprocessed_width ζ)) ∨
      (pl = none ∧ pn = none ∧ air.preprocessed_width = 0)) :
    ∃ q, recompose_quotient_from_chunks GK B ((List.range (2 ^ L)).map (chunk GK hV qd L)) chunks ζ =
        some q ∧
      verify_constraints GK air
        (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 0) air.width ζ)
        (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ)
        pl pn
        (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) .periodic
          air.num_periodic_columns ζ) pv c ζ α q = some (.ok ()) := by
  have hdeg := degree_quotient_lt (K := K) Nat.one_le_two_pow hfit α
  rw [← hcs, ← hcg, ← pow_add, ← hqd] at hdeg
  exact ⟨_, recompose_quotient_masked hV qd L B hN (by omega) _ hdeg t ζ chunks hlen hv,
    verify_constraints_complete GK hV h2 hb c hcs hcg hω hs hT hmain hprep hpub hper hpv hsat hζ α hpre⟩

end Plonky3Lean.Proofs.UniStark
