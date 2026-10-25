module

public import Plonky3Lean.Proofs.Air.Builder
public import Plonky3Lean.Proofs.Air.Semantics

@[expose] public section

/-!
# Unread rows do not matter

An expression that never reads a leaf takes the same value whatever that leaf holds.

The proof is an induction on the expression.

Take an AIR whose symbolic constraints never read the next row of a trace.

Its constraint polynomials ignore that row.

So a verifier may put zeros in place of a next row it did not open.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Air

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror Plonky3Lean.Spec.Air

namespace SymbolicExpr

variable {A : Type _}

/-- No leaf of the expression satisfies p. -/
def Avoids (p : A → Prop) : SymbolicExpr A → Prop
  | .Leaf a => ¬ p a
  | .Add x y _ | .Sub x y _ | .Mul x y _ => Avoids p x ∧ Avoids p y
  | .Neg x _ => Avoids p x

/-- Two leaf values that agree off p give an expression that avoids p one value. -/
theorem denote_congr {F R : Type _} [SymLeaf A F] [Field F] [DecidableEq F] [CommRing R] [Algebra F R]
    {p : A → Prop} {den den' : A → R} (h : ∀ a, ¬ p a → den a = den' a) {e : SymbolicExpr A}
    (he : Avoids p e) : denote den e = denote den' e := by
  induction e <;> simp_all [Avoids, denote]

end SymbolicExpr

open SymbolicExpr

variable {F : Type _} [Field F] [DecidableEq F]

/-- The variables of the next row of a dropped trace: the main trace when dm, the preprocessed one when dp. -/
def nextRowVar (dm dp : Bool) : Var → Prop
  | .main 1 _ => dm
  | .prep 1 _ => dp
  | _ => False

/-- A base leaf reads the next row of a dropped trace. -/
def readsNextRow (dm dp : Bool) : BaseLeaf F → Prop
  | .Variable v => (v.entry = .Main 1 ∧ dm) ∨ (v.entry = .Preprocessed 1 ∧ dp)
  | _ => False

/-- An expression that never reads a dropped next row has one value at two assignments that agree off it. -/
theorem aeval_toPoly_congr {R : Type _} [CommRing R] [Algebra F R] {dm dp : Bool} {env env' : Var → R}
    (h : ∀ v, ¬ nextRowVar dm dp v → env v = env' v) {e : SymbolicExpression F}
    (he : Avoids (readsNextRow dm dp) e) :
    MvPolynomial.aeval env (toPoly e) = MvPolynomial.aeval env' (toPoly e) := by
  rw [toPoly, map_denote, map_denote]
  refine denote_congr (fun a ha => ?_) he
  rcases a with ⟨⟨_ | _ | o⟩ | ⟨_ | _ | o⟩ | _ | _, j⟩ | _ | _ | _ | c <;>
    simp_all [readsNextRow, leafPoly, varPoly, nextRowVar]

/-- The AIR's symbolic constraints never read the next row of a dropped trace.

The main trace is dropped when dm, the preprocessed trace when dp. -/
def NextRowUnread (air : Air F) (dm dp : Bool) : Prop :=
  ∀ c ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [], Avoids (readsNextRow dm dp) c

/-- **Unread rows do not matter.**

Take an AIR that never reads a dropped next row.

Each constraint polynomial has one value at two assignments that agree off that row. -/
theorem constraints_congr {R : Type _} [CommRing R] [Algebra F R] {air : Air F} {dm dp : Bool}
    (hu : NextRowUnread air dm dp) {env env' : Var → R} (h : ∀ v, ¬ nextRowVar dm dp v → env v = env' v) :
    (constraints air).map (MvPolynomial.aeval env) = (constraints air).map (MvPolynomial.aeval env') := by
  rw [constraints, ← symbolic_toPoly, List.map_map, List.map_map]
  exact List.map_congr_left fun c hc => aeval_toPoly_congr h (hu c hc)

/-- With no trace dropped, every AIR meets the condition. -/
theorem nextRowUnread_false (air : Air F) : NextRowUnread air false false := by
  rintro c -
  induction c with
  | Leaf a => rcases a <;> simp [Avoids, readsNextRow]
  | _ => simp_all [Avoids]

/-- Two windows that differ only in a dropped next row give agreeing assignments. -/
theorem windowEnv_congr {R : Type} [Field R] {dm dp : Bool} {main main' preprocessed preprocessed' : RowWindow R}
    (hmc : main.current = main'.current) (hpc : preprocessed.current = preprocessed'.current)
    (hmn : dm = false → main.next = main'.next) (hpn : dp = false → preprocessed.next = preprocessed'.next)
    (pv : List R) (first last trans : R) (periodic : List R) :
    ∀ v, ¬ nextRowVar dm dp v →
      windowEnv main preprocessed pv first last trans periodic v =
        windowEnv main' preprocessed' pv first last trans periodic v := by
  rintro (⟨o, c⟩ | ⟨o, c⟩ | _ | _ | _ | _ | _) hv <;> try rfl
  all_goals
    match o with
    | 0 => simp [windowEnv, hmc, hpc]
    | 1 => simp_all [windowEnv, nextRowVar]

end Plonky3Lean.Proofs.Air
