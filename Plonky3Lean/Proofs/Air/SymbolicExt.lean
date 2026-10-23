module

public import Plonky3Lean.Proofs.Air.Symbolic
public import CompPoly.Fields.BabyBear.Ext4

@[expose] public section

/-!
# Extension expressions: meaning and degree

An extension expression denotes a polynomial over the extension field, in the base variables and the extension variables.

A base subexpression denotes its base polynomial, with coefficients moved to the extension.

An extension constant that lies in the base field folds as that base constant.

The simplifying operators then denote the ring operations, and the degree walk bounds the degree.

The quartic extension of BabyBear recognises its base field by its coordinates.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Air

open p3_air.symbolic.mirror Plonky3Lean.Spec.Air SymbolicExpr

variable {F EF : Type _} [Field F] [DecidableEq F] [Field EF] [Algebra F EF] [InBase F EF]

/-- The extension recognises exactly the embedded base elements. -/
def LawfulInBase (F EF : Type _) [Field F] [Field EF] [Algebra F EF] [InBase F EF] : Prop :=
  ∀ e c, InBase.as_base (F := F) e = some c → e = algebraMap F EF c

/-- The polynomial an extension leaf names, in the base variables and the extension variables. -/
noncomputable def extLeafPoly : ExtLeaf F EF → MvPolynomial (Var ⊕ SymbolicVariableExt) EF
  | .Base e => MvPolynomial.rename Sum.inl (MvPolynomial.map (algebraMap F EF) (toPoly e))
  | .ExtVariable v => .X (.inr v)
  | .ExtConstant c => .C c

/-- The polynomial an extension expression denotes. -/
noncomputable def toPolyExt (e : SymbolicExpressionExt F EF) :
    MvPolynomial (Var ⊕ SymbolicVariableExt) EF :=
  denote extLeafPoly e

theorem leafDen_extLeafPoly (h : LawfulInBase F EF) :
    LeafDen (A := ExtLeaf F EF) (R := MvPolynomial (Var ⊕ SymbolicVariableExt) EF) extLeafPoly where
  as_const a c ha := by
    rcases a with e | v | ef
    · rcases e with (_ | _ | _ | _ | _) | _ <;>
        simp_all [SymLeaf.as_const, extLeafPoly, toPoly, denote, leafPoly,
          MvPolynomial.algebraMap_eq]
    · simp [SymLeaf.as_const] at ha
    · simp only [SymLeaf.as_const] at ha
      simp [extLeafPoly, h ef c ha]
  from_const c := by
    simp [SymLeaf.from_const, extLeafPoly, toPoly, denote, leafPoly, MvPolynomial.algebraMap_eq]

/-- Degree bounds for an extension assignment: the base bounds, permutation columns of degree at most n - 1, and constant challenges and permutation values. -/
structure ExtDegreeBounds (σ : Var ⊕ SymbolicVariableExt → Polynomial EF) (n : ℕ) (periods : List ℕ) :
    Prop where
  base : DegreeBounds (σ ∘ Sum.inl) n periods
  perm : ∀ o i, (σ (.inr ⟨.Permutation o, i⟩)).natDegree ≤ n - 1
  challenge : ∀ i, (σ (.inr ⟨.Challenge, i⟩)).natDegree = 0
  perm_value : ∀ i, (σ (.inr ⟨.PermutationValue, i⟩)).natDegree = 0

/-- The polynomial degree walk bounds the degree of an extension constraint polynomial. -/
theorem natDegree_ext_le_poly_degree {σ : Var ⊕ SymbolicVariableExt → Polynomial EF} {n : ℕ}
    {periods : List ℕ} (hσ : ExtDegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n)
    (e : SymbolicExpressionExt F EF) :
    (MvPolynomial.aeval σ (toPolyExt e)).natDegree ≤ e.poly_degree n periods := by
  rw [toPolyExt, map_denote (MvPolynomial.aeval (R := EF) σ)]
  refine natDegree_denote_le (fun a => ?_) e
  rcases a with b | ⟨⟨o⟩ | _ | _, i⟩ | c
  · rw [extLeafPoly, MvPolynomial.aeval_rename, MvPolynomial.aeval_map_algebraMap, toPoly,
      map_denote (MvPolynomial.aeval (R := F) (σ ∘ Sum.inl))]
    exact natDegree_denote_le (natDegree_leaf_le hσ.base hp) b
  · simpa [extLeafPoly, SymLeaf.poly_degree, SymbolicVariableExt.poly_degree] using hσ.perm o i
  · simp [extLeafPoly, SymLeaf.poly_degree, SymbolicVariableExt.poly_degree, hσ.challenge]
  · simp [extLeafPoly, SymLeaf.poly_degree, SymbolicVariableExt.poly_degree, hσ.perm_value]
  · simp [extLeafPoly, SymLeaf.poly_degree]

/-- An extension expression with no extension leaf denotes its base expression's polynomial. -/
theorem toPolyExt_of_to_base {e : SymbolicExpressionExt F EF} {b : SymbolicExpression F}
    (h : SymbolicExpressionExt.to_base e = some b) :
    toPolyExt e = MvPolynomial.rename Sum.inl (MvPolynomial.map (algebraMap F EF) (toPoly b)) := by
  simp only [toPolyExt, toPoly]
  induction e generalizing b with
  | Leaf a =>
    rcases a with b' | _ | _ <;> simp_all [SymbolicExpressionExt.to_base, denote, extLeafPoly,
      toPoly]
  | Add x y d hx hy | Sub x y d hx hy | Mul x y d hx hy =>
    simp only [SymbolicExpressionExt.to_base, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨bx, hbx, by', hby, rfl⟩ := h
    simp [denote, hx hbx, hy hby]
  | Neg x d hx =>
    simp only [SymbolicExpressionExt.to_base, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨bx, hbx, rfl⟩ := h
    simp [denote, hx hbx]

/-! ## The quartic extension of BabyBear -/

/-- An element lies in the base field when its coordinates past the first vanish.

The first coordinate is then its value. -/
instance : InBase BabyBear.Field BabyBear.Ext4 where
  as_base e := if ∀ i : Fin BabyBear.ext4Params.toExtensionParams.d, (i : ℕ) ≠ 0 → e.coeff i = 0
    then some (e.coeff ⟨0, by decide⟩) else none

theorem lawfulInBase_babyBear : LawfulInBase BabyBear.Field BabyBear.Ext4 := by
  intro e c h
  simp only [InBase.as_base] at h
  split_ifs at h with hz
  cases h
  ext i
  rw [CompPoly.Extension.Ext.algebraMap_eq_ofBase, CompPoly.Extension.Ext.coeff_ofBase]
  split_ifs with hi
  · congr 1; exact Fin.ext hi
  · exact hz i hi

end Plonky3Lean.Proofs.Air
