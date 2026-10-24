module

public import Plonky3Lean.Proofs.BinaryDft.Naive
public import Plonky3Lean.Proofs.Field.Binary.CantorSpec

@[expose] public section

/-!
# The tower levels, field isomorphisms and the extension

The tower level of 2^k bits has the Cantor basis the binary-field proofs build, for k up to 7.

A field isomorphism carries the transform over one basis to the transform over the image basis.

That is why running the network in the GHASH or polynomial basis gives the tower result.

The default extension interpolates on the coset, then evaluates on the coset 2^a times larger.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror p3_binary_dft.lch.mirror
  p3_binary_dft.traits.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft ConcreteBinaryTower
  p3_commit.encoder.mirror

/-! ## The tower levels -/

/-- The tower level of 2^k bits and b bytes, with the Cantor basis of the binary-field proofs. -/
def towerLevel (k b : ℕ) : Level (ConcreteBTField k) := ⟨k, b, Binary.cantorTower k⟩

theorem towerLevel_cantor {k : ℕ} (hk : k ≤ 7) (b : ℕ) : Cantor (towerLevel k b) :=
  ⟨Binary.cantorTower_zero k, fun _ hi => Binary.cantorTower_succ hk hi⟩

/-! ## Field isomorphisms -/

section Map

variable {F G : Type _} [Field F] [Field G] (φ : F →+* G)

theorem ringHom_point (β : ℕ → F) (m : ℕ) : φ (point β m) = point (φ ∘ β) m := by
  simp only [point, map_sum, Function.comp]
  exact sum_congr rfl fun r _ => by split_ifs <;> simp

theorem map_vanishing (β : ℕ → F) (i : ℕ) (x : F) :
    φ (vanishing β i x) = vanishing (φ ∘ β) i (φ x) := by
  simp [vanishing, map_prod, map_sub, ringHom_point]

theorem map_ntt (β : ℕ → F) (l : ℕ) (shift : F) (d : ℕ → F) (i : ℕ) :
    φ (ntt β l shift d i) = ntt (φ ∘ β) l (φ shift) (φ ∘ d) i := by
  simp only [ntt, novelEval, novel, smul_eq_mul, map_sum, map_mul, map_prod, Function.comp]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  refine prod_congr rfl fun j _ => ?_
  split_ifs <;> simp [normalized, map_vanishing, ringHom_point]

theorem IsCantor.map {β : ℕ → F} {n : ℕ} (h : IsCantor β n) : IsCantor (φ ∘ β) n :=
  ⟨by simp [h.1], fun i hi => by simp [← h.2 i hi]⟩

end Map

/-! ## The default extension over the transform -/

variable {F : Type _} [Field F] [DecidableEq F] [CharP F 2] {V : Type _} [AddCommGroup V]
  [Module F V] {L : Level F} (hL : Cantor L)
include hL

/-- The extension of 2^l values by a dimensions.

The input rows come back first, and the rest evaluate their interpolant. -/
theorem shifted_lde_eq {l a width : ℕ} (hla : l + a ≤ 2 ^ L.logBits) (ha : 0 < a) (hw : 0 < width)
    (har : a < 64) (hword : 2 ^ l * width * 2 ^ a < 2 ^ 64) (shift : F) (y : ℕ → V) :
    ∃ d : ℕ → V, (∀ i < 2 ^ l, ntt L.cantor l shift d i = y i) ∧
      shifted_lde_batch L (lchBackend L) width (2 ^ l) y a shift =
        some (mask (l + a) (zeroBelow (2 ^ l) d)
          (ntt L.cantor (l + a) shift (zeroBelow (2 ^ l) d))) := by
  have hl : l ≤ 2 ^ L.logBits := by omega
  set d := inetwork (twiddle L.cantor shift) l y
  have hd : ∀ i < 2 ^ l, ntt L.cantor l shift d i = y i := fun i hi => by
    rw [← network_ntt L.cantor (IsCantor.independent hL) hl shift d hi, network_inetwork]
  refine ⟨d, hd, ?_⟩
  unfold shifted_lde_batch
  simp only [log2Strict_pow, Option.bind_eq_bind, Option.bind_some,
    show ¬ 2 ^ L.logBits < l by omega, show a ≠ 0 by omega, ↓reduceIte, lchBackend,
    LchNtt.shifted_intt_batch, LchNtt.shifted_ntt_batch, padded_len]
  rw [transform_eq hL hl shift true hw, Option.bind_some, Plonky3Lean.Proofs.Commit.paddedLen_eq]
  simp only [har, hword, and_self, ↓reduceIte, Option.bind_some]
  have hh : heightOf (2 ^ l * width * 2 ^ a) width = 2 ^ (l + a) := by
    simp only [heightOf, show width ≠ 0 by omega, ↓reduceIte]
    rw [show 2 ^ l * width * 2 ^ a = 2 ^ (l + a) * width by ring, Nat.mul_div_cancel _ hw]
  have hz : zeroBelow (2 ^ l) (mask l y (lchNet L shift true l y)) = zeroBelow (2 ^ l) d := by
    funext k; simp only [zeroBelow, mask, lchNet, ↓reduceIte]; split_ifs <;> rfl
  rw [hh, hz, transform_ntt hL hla shift hw]

end Plonky3Lean.Proofs.BinaryDft
