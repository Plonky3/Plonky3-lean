module

public import P3BatchStark
public import Plonky3Lean.Proofs.UniStark.Verifier
public import Plonky3Lean.Proofs.Lookup.Constraints
public import Plonky3Lean.Proofs.BatchStark.Soundness

@[expose] public section

/-!
# One instance's check at the out-of-domain point

The verifier folds the AIR's constraints and then the lookup constraints, with Horner's rule in alpha.

Take openings that hold an assignment of the variables at zeta.

Then the fold is the combination of the constraint values at that assignment:

- the AIR's constraint polynomials
- each lookup column's pin D f - N
- the accumulator's first-row, transition and last-row constraints.

Take the trace polynomials and the permutation columns as univariate polynomials, with the Lagrange selectors.

Then the fold is the combined constraint polynomial evaluated at zeta.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open Polynomial Finset
open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror p3_lookup.mirror
  p3_uni_stark.folder.mirror p3_uni_stark.verifier.mirror p3_batch_stark.constraints.mirror
  p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror p3_batch_stark.transcript.mirror
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark Plonky3Lean.Spec.Lookup
open Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.UniStark Plonky3Lean.Proofs.Commit
  Plonky3Lean.Proofs.Lookup Plonky3Lean.Proofs.Dft

variable {F K : Type} [Field F] [DecidableEq F] [Inhabited F] [Field K] [DecidableEq K] [Algebra F K]

/-! ## Expressions within the AIR's widths -/

/-- Every variable leaf names offset 0 or 1 and an entry within the AIR's widths. -/
def Reads (air : Air F) : SymbolicExpression F → Prop
  | .Leaf (.Variable v) =>
    match v.entry with
    | .Main 0 | .Main 1 => v.index < air.width
    | .Preprocessed 0 | .Preprocessed 1 => v.index < air.preprocessed_width
    | .Public => v.index < air.num_public_values
    | .Periodic => v.index < air.num_periodic_columns
    | _ => False
  | .Leaf _ => True
  | .Add x y _ | .Sub x y _ | .Mul x y _ => Reads air x ∧ Reads air y
  | .Neg x _ => Reads air x

theorem getElem?_of_lt {l : List K} {i : ℕ} (h : i < l.length) : l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ h]; simp [h]

/-- Resolving an expression within the widths on the verifier's folder evaluates its polynomial.

The evaluation is at an assignment the opened values hold. -/
theorem resolve_verifierFolder {air : Air F} {env : Var → K} {main preprocessed : RowWindow K}
    {pv : List F} {periodic : List K} {first last trans : K}
    (h : Holds air env main preprocessed (pv.map (algebraMap F K)) periodic first last trans) (α : K)
    (s : K) (e : SymbolicExpression F) (he : Reads air e) :
    resolve (verifierFolder main preprocessed pv periodic first last trans α) s e =
      some (MvPolynomial.aeval env (toPoly e)) := by
  have get : ∀ {l : List K} {w c : ℕ}, l.length = w → c < w → l[c]? = some (l.getD c 0) :=
    fun hl hc => getElem?_of_lt (hl ▸ hc)
  have hmc : ∀ c < air.width, main.current[c]? = some (env (.main 0 c)) := fun c hc => by
    rw [get h.shapes.main_current hc, h.main_current c hc]
  have hmn : ∀ c < air.width, main.next[c]? = some (env (.main 1 c)) := fun c hc => by
    rw [get h.shapes.main_next hc, h.main_next c hc]
  have hpc : ∀ c < air.preprocessed_width, preprocessed.current[c]? = some (env (.prep 0 c)) :=
    fun c hc => by rw [get h.shapes.prep_current hc, h.prep_current c hc]
  have hpn : ∀ c < air.preprocessed_width, preprocessed.next[c]? = some (env (.prep 1 c)) :=
    fun c hc => by rw [get h.shapes.prep_next hc, h.prep_next c hc]
  have hpv : ∀ c < air.num_public_values, (pv.map (algebraMap F K))[c]? = some (env (.pub c)) :=
    fun c hc => by rw [get h.shapes.pub hc, h.pub c hc]
  have hper : ∀ c < air.num_periodic_columns, periodic[c]? = some (env (.periodic c)) :=
    fun c hc => by rw [get h.shapes.periodic hc, h.periodic c hc]
  induction e with
  | Leaf a =>
    rcases a with ⟨⟨_ | _ | o⟩ | ⟨_ | _ | o⟩ | _ | _, j⟩ | _ | _ | _ | c <;>
      simp only [Reads] at he <;>
      simp only [resolve, toPoly, SymbolicExpr.denote, leafPoly, varPoly, verifierFolder,
        AirBuilder.is_transition_window, MvPolynomial.aeval_X, MvPolynomial.aeval_C, h.first,
        h.last, h.trans] <;>
      first
        | exact hmc _ he | exact hmn _ he | exact hpc _ he | exact hpn _ he
        | exact hpv _ he | exact hper _ he | simp
  | Add x y _ hx hy | Sub x y _ hx hy | Mul x y _ hx hy =>
    simp_all [Reads, resolve, toPoly, SymbolicExpr.denote, verifierFolder]
  | Neg x _ hx => simp_all [Reads, resolve, toPoly, SymbolicExpr.denote, verifierFolder]

/-! ## One lookup column at zeta -/

/-- A lookup's expressions read at an assignment, with the pair of its slot. -/
noncomputable def columnAt (env : Var → K) (ch : List K) (l : Lookup F) : Column K :=
  ⟨(l.flags.getD []).map (MvPolynomial.aeval env ∘ toPoly),
    l.elements.map (·.map (MvPolynomial.aeval env ∘ toPoly)),
    l.multiplicities.map (MvPolynomial.aeval env ∘ toPoly), ch.getD (2 * l.column) 0,
    ch.getD (2 * l.column + 1) 0⟩

/-- A lookup the verifier evaluates without panicking:

- one multiplicity per tuple
- no flags, or one flag per tuple
- every expression within the AIR's widths. -/
structure Fits (air : Air F) (l : Lookup F) : Prop where
  mults : l.elements.length = l.multiplicities.length
  flags : l.flags.getD [] = [] ∨ (l.flags.getD []).length = l.elements.length
  elements : ∀ e ∈ l.elements, ∀ x ∈ e, Reads air x
  multiplicities : ∀ x ∈ l.multiplicities, Reads air x
  flag_reads : ∀ x ∈ l.flags.getD [], Reads air x

/-- The combination of a concatenation: the first part is shifted by alpha^m, for m values after it. -/
theorem combine_append (α : K) (xs ys : List K) :
    combine α (xs ++ ys) = combine α xs * α ^ ys.length + combine α ys := by
  have h := UniStark.foldl_horner α 0 (xs ++ ys)
  rw [List.foldl_append, UniStark.foldl_horner, UniStark.foldl_horner] at h
  simpa using h.symm

theorem combine_cons (α x : K) (xs : List K) :
    combine α (x :: xs) = x * α ^ xs.length + combine α xs := by
  rw [← List.singleton_append, combine_append]; simp [combine]

section fold

variable {air : Air F} {env : Var → K} {main preprocessed : RowWindow K} {pv : List F}
  {periodic : List K} {first last trans : K}

/-- **One column's pin at zeta** folds D f - N into the accumulator. -/
theorem eval_fraction_verifier
    (h : Holds air env main preprocessed (pv.map (algebraMap F K)) periodic first last trans)
    (α : K) (perm : RowWindow K) (ch values : List K) (s : K) (l : Lookup F) (hl : Fits air l)
    (hch : 2 * (l.column + 1) ≤ ch.length) {f : K} (hf : perm.current[l.column + 1]? = some f) :
    eval_fraction (verifierPermFolder main preprocessed pv periodic first last trans α perm ch values)
      s l = some (s * α + ((columnAt env ch l).numDen.2 * f - (columnAt env ch l).numDen.1)) := by
  have res : ∀ x, Reads air x → (resolve (verifierFolder main preprocessed pv periodic first last
      trans α) s x).map id = some ((MvPolynomial.aeval env ∘ toPoly) x) := fun x hx => by
    rw [resolve_verifierFolder h α s x hx]; rfl
  have hev := mapM_some_of l.elements _ (·.map (MvPolynomial.aeval env ∘ toPoly)) fun e he =>
    mapM_some_of e _ _ fun x hx => res x (hl.elements e he x hx)
  have hmv := mapM_some_of l.multiplicities _ _ fun x hx => res x (hl.multiplicities x hx)
  have hfl := mapM_some_of (l.flags.getD []) _ _ fun x hx => res x (hl.flag_reads x hx)
  unfold eval_fraction
  simp only [verifierPermFolder, hl.mults, ne_eq, not_true_eq_false, ite_false, hev, hmv, hfl,
    show ¬ ch.length < 2 * (l.column + 1) by omega, getElem?_of_lt (show 2 * l.column < ch.length by omega),
    getElem?_of_lt (show 2 * l.column + 1 < ch.length by omega), hf, Option.bind_eq_bind,
    Option.bind_some]
  have hops : (⟨(· + ·), (· - ·), (· * ·), 0, 1⟩ : RingOps K) = fieldOps K := rfl
  rw [hops]
  by_cases h0 : l.flags.getD [] = []
  · simp only [h0, List.map_nil, List.isEmpty_nil, ite_true]
    rw [compute_combined_sum_terms_field _ _ _ _ (by simp [hl.mults])]
    simp [columnAt, Column.numDen, h0, rowTerms]
  · have hlen := hl.flags.resolve_left h0
    simp only [List.isEmpty_iff, List.map_eq_nil_iff, h0, ite_false]
    rw [compute_exclusive_terms_field _ _ _ _ _ (by simp [hlen]) (by simp [hl.mults])]
    simp [columnAt, Column.numDen, h0]

/-- The pins of a list of columns fold one after another, by Horner's rule. -/
theorem foldlM_fractions
    (h : Holds air env main preprocessed (pv.map (algebraMap F K)) periodic first last trans)
    (α : K) (perm : RowWindow K) (ch values : List K) (ls : List (Lookup F))
    (hl : ∀ l ∈ ls, Fits air l ∧ 2 * (l.column + 1) ≤ ch.length ∧ l.column + 1 < perm.current.length)
    (s : K) :
    ls.foldlM (fun s l => eval_fraction (verifierPermFolder main preprocessed pv periodic first last
      trans α perm ch values) s l) s =
      some (s * α ^ ls.length + combine α (ls.map fun l =>
        (columnAt env ch l).numDen.2 * perm.current.getD (l.column + 1) 0 -
          (columnAt env ch l).numDen.1)) := by
  induction ls generalizing s with
  | nil => simp [combine_nil]
  | cons l ls ih =>
    obtain ⟨h1, h2, h3⟩ := hl l List.mem_cons_self
    simp only [List.foldlM_cons, eval_fraction_verifier h α perm ch values s l h1 h2
      (getElem?_of_lt h3), Option.bind_eq_bind, Option.bind_some,
      ih fun l' hl' => hl l' (List.mem_cons_of_mem _ hl'), List.map_cons, List.length_cons]
    rw [combine_cons, List.length_map]; congr 1; ring

/-- **The accumulator at zeta** folds its three selector-gated values:

- acc times the first-row selector
- acc' - acc - sum_c f_c times the transition selector
- T - acc - sum_c f_c times the last-row selector. -/
theorem eval_accumulator_verifier (α : K) (perm : RowWindow K) (ch values : List K) (s T : K)
    (lookups : List (Lookup F)) (hcol : ∀ i (h : i < lookups.length), lookups[i].column = i)
    (hc : lookups.length < perm.current.length) (hn : 0 < perm.next.length) :
    eval_accumulator (verifierPermFolder main preprocessed pv periodic first last trans α perm ch
      values) s lookups T =
      some (((s * α + perm.current.getD 0 0 * first) * α +
        (perm.next.getD 0 0 - perm.current.getD 0 0 -
          ∑ c ∈ range lookups.length, perm.current.getD (c + 1) 0) * trans) * α +
        (T - perm.current.getD 0 0 - ∑ c ∈ range lookups.length, perm.current.getD (c + 1) 0) *
          last) := by
  have hmem : ∀ l ∈ lookups, l.column < lookups.length := fun l hl => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl; rw [hcol i hi]; exact hi
  have hsum := foldlM_row_sum (F := F) (fun l => perm.current[l.column + 1]?)
    (fun c => perm.current.getD c 0) lookups 0 fun l hl => getElem?_of_lt (by have := hmem l hl; omega)
  have hcols := sum_columns (fun c => perm.current.getD c 0) lookups hcol
  rw [hcols, zero_add] at hsum
  unfold eval_accumulator
  simp only [verifierPermFolder, gt_iff_lt, hc, not_true_eq_false, ite_false,
    getElem?_of_lt (show 0 < perm.current.length by omega), getElem?_of_lt hn, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]
  rw [hsum, Option.bind_some]
  simp [ExtensionBuilder.when, verifierFolder]

end fold

/-- The lookup constraint values of one AIR at an assignment.

There are none without lookups.

Otherwise the permutation row holds the accumulator, then one fraction per lookup. -/
noncomputable def lookupValues (env : Var → K) (ch : List K) (perm : RowWindow K) (T first last trans : K)
    (lookups : List (Lookup F)) : List K :=
  if lookups = [] then []
  else logUpConstraints (lookups.map (columnAt env ch))
    ((List.range lookups.length).map fun c => perm.current.getD (c + 1) 0)
    (perm.current.getD 0 0) (perm.next.getD 0 0) T first last trans

/-- The lookups of one AIR as the verifier lays them out:

- lookup i owns slot i
- each fits the AIR
- there are two challenges per slot. -/
structure LaidOut (air : Air F) (ch : List K) (lookups : List (Lookup F)) : Prop where
  column : ∀ i (h : i < lookups.length), lookups[i].column = i
  fits : ∀ l ∈ lookups, Fits air l
  challenges : 2 * lookups.length ≤ ch.length

/-- **The fold at zeta.**

Take openings that hold an assignment, and lookups laid out by the verifier.

Take a permutation row with the accumulator and one fraction per lookup.

When there are lookups, take one terminal.

Then the verifier's fold is the combination, in emission order, of two lists of values:

- the AIR's constraint polynomials at the assignment
- the lookup constraint values. -/
theorem eval_air_and_lookups_verifier {air : Air F} {env : Var → K} {main preprocessed : RowWindow K}
    {pv : List F} {periodic : List K} {first last trans : K}
    (h : Holds air env main preprocessed (pv.map (algebraMap F K)) periodic first last trans)
    (α : K) {ch : List K} {lookups : List (Lookup F)} (hL : LaidOut air ch lookups) (perm : RowWindow K)
    (hperm : lookups ≠ [] → lookups.length < perm.current.length ∧ 0 < perm.next.length) (T : K) :
    p3_batch_stark.checker.mirror.eval_air_and_lookups air
      (verifierPermFolder main preprocessed pv periodic first last trans α perm ch
        (if lookups = [] then [] else [T])) 0 lookups =
      some (combine α ((constraints air).map (MvPolynomial.aeval env) ++
        lookupValues env ch perm T first last trans lookups)) := by
  have hair : air.eval (verifierFolder main preprocessed pv periodic first last trans α) 0 =
      combine α ((constraints air).map (MvPolynomial.aeval env)) := verifier_accumulator h α
  unfold p3_batch_stark.checker.mirror.eval_air_and_lookups
  by_cases h0 : lookups = []
  · subst h0
    simp [verifierPermFolder, lookupValues, hair]
  · obtain ⟨hc, hn⟩ := hperm h0
    have hmem : ∀ l ∈ lookups, l.column < lookups.length := fun l hl => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl; rw [hL.column i hi]; exact hi
    have hfr := foldlM_fractions h α perm ch [T] lookups (fun l hl =>
      ⟨hL.fits l hl, by have := hmem l hl; have := hL.challenges; omega,
        by have := hmem l hl; omega⟩)
    have hpins : ((lookups.map (columnAt env ch)).zip
        ((List.range lookups.length).map fun c => perm.current.getD (c + 1) 0)).map
          (fun p => p.1.numDen.2 * p.2 - p.1.numDen.1) =
        lookups.map fun l => (columnAt env ch l).numDen.2 * perm.current.getD (l.column + 1) 0 -
          (columnAt env ch l).numDen.1 :=
      List.ext_getElem (by simp) fun i h1 h2 => by
        simp only [List.length_map] at h2
        simp [hL.column i h2]
    have hacc := eval_accumulator_verifier (main := main) (preprocessed := preprocessed) (pv := pv)
      (periodic := periodic) (first := first) (last := last) (trans := trans) α perm ch [T]
      (combine α ((constraints air).map (MvPolynomial.aeval env)) * α ^ lookups.length +
        combine α (lookups.map fun l => (columnAt env ch l).numDen.2 *
          perm.current.getD (l.column + 1) 0 - (columnAt env ch l).numDen.1)) T lookups hL.column hc hn
    have hpv : ∀ x, (verifierPermFolder main preprocessed pv periodic first last trans α perm ch
        [T]).permutation_values x = [T] := fun _ => rfl
    have hair' : air.eval (verifierPermFolder main preprocessed pv periodic first last trans α perm ch
        [T]).toAirBuilder 0 = combine α ((constraints air).map (MvPolynomial.aeval env)) := hair
    simp only [List.isEmpty_iff, h0, ite_false, eval_all, hpv, ne_eq,
      not_true_eq_false, List.getElem?_singleton, Option.bind_eq_bind, Option.bind_some, hair', hfr,
      lookupValues, logUpConstraints, hpins, combine_append, List.length_append,
      List.length_map, List.length_cons, List.length_nil, sum_map_range]
    simp only [ite_true, Option.bind_some, hacc, combine_cons, combine_nil, List.length_cons,
      List.length_nil]
    congr 1; ring

/-! ## Unread rows -/

/-- A lookup never reads the next row of a dropped trace: its flags, tuples and multiplicities avoid it. -/
def LookupUnread (dm dp : Bool) (l : Lookup F) : Prop :=
  (∀ x ∈ l.flags.getD [], SymbolicExpr.Avoids (readsNextRow dm dp) x) ∧
  (∀ e ∈ l.elements, ∀ x ∈ e, SymbolicExpr.Avoids (readsNextRow dm dp) x) ∧
  ∀ x ∈ l.multiplicities, SymbolicExpr.Avoids (readsNextRow dm dp) x

/-- Lookups that never read a dropped next row have one value at two assignments that agree off it. -/
theorem lookupValues_congr {dm dp : Bool} {lookups : List (Lookup F)} (hl : ∀ l ∈ lookups, LookupUnread dm dp l)
    {env env' : Var → K} (h : ∀ v, ¬ nextRowVar dm dp v → env v = env' v) (ch : List K) (perm : RowWindow K)
    (T first last trans : K) :
    lookupValues env ch perm T first last trans lookups = lookupValues env' ch perm T first last trans lookups := by
  have hcol : lookups.map (columnAt env ch) = lookups.map (columnAt env' ch) :=
    List.map_congr_left fun l hlm => by
      obtain ⟨hf, he, hm⟩ := hl l hlm
      have hx : ∀ x : SymbolicExpression F, SymbolicExpr.Avoids (readsNextRow dm dp) x →
          (MvPolynomial.aeval env ∘ toPoly) x = (MvPolynomial.aeval env' ∘ toPoly) x :=
        fun x hx => aeval_toPoly_congr h hx
      simp only [columnAt, List.map_congr_left fun x hm' => hx x (hf x hm'),
        List.map_congr_left fun x hm' => hx x (hm x hm'),
        List.map_congr_left fun e he' => List.map_congr_left fun x hx' => hx x (he e he' x hx')]
  simp only [lookupValues, hcol]

/-- **The check at zeta ignores an unread row.**

Take two openings of the AIR's widths that differ only in the next row of a dropped trace.

When neither the AIR nor its lookups read that row, the check returns one result on both. -/
theorem verify_constraints_with_lookups_congr (G : Gen K) {air : Air F} {dm dp : Bool}
    (hu : NextRowUnread air dm dp) {lookups : List (Lookup F)} (hl : ∀ l ∈ lookups, LookupUnread dm dp l)
    {ch : List K} (hL : LaidOut air ch lookups) {tl tn tn' pl pn pn' ml mn per : List K} {pv : List F} (T : K)
    (hperm : lookups ≠ [] → lookups.length < ml.length ∧ 0 < mn.length)
    (hs : WindowShapes air ⟨tl, tn⟩ ⟨pl, pn⟩ (pv.map (algebraMap F K)) per)
    (hs' : WindowShapes air ⟨tl, tn'⟩ ⟨pl, pn'⟩ (pv.map (algebraMap F K)) per)
    (hmn : dm = false → tn = tn') (hpn : dp = false → pn = pn') (c : Coset G) (ζ α q : K) :
    verify_constraints_with_lookups G air tl tn pl pn ml mn ch (if lookups = [] then [] else [T]) per lookups
        pv c ζ α q =
      verify_constraints_with_lookups G air tl tn' pl pn' ml mn ch (if lookups = [] then [] else [T]) per
        lookups pv c ζ α q := by
  have hfold : ∀ first last trans,
      p3_batch_stark.checker.mirror.eval_air_and_lookups air (verifierPermFolder ⟨tl, tn⟩ ⟨pl, pn⟩ pv per
        first last trans α ⟨ml, mn⟩ ch (if lookups = [] then [] else [T])) 0 lookups =
      p3_batch_stark.checker.mirror.eval_air_and_lookups air (verifierPermFolder ⟨tl, tn'⟩ ⟨pl, pn'⟩ pv per
        first last trans α ⟨ml, mn⟩ ch (if lookups = [] then [] else [T])) 0 lookups := fun first last trans => by
    have hag := windowEnv_congr (dm := dm) (dp := dp) (main := ⟨tl, tn⟩) (main' := ⟨tl, tn'⟩)
      (preprocessed := ⟨pl, pn⟩) (preprocessed' := ⟨pl, pn'⟩) rfl rfl (fun h => by rw [hmn h])
      (fun h => by rw [hpn h]) (pv.map (algebraMap F K)) first last trans per
    rw [eval_air_and_lookups_verifier (holds_windowEnv hs first last trans) α hL ⟨ml, mn⟩ hperm T,
      eval_air_and_lookups_verifier (holds_windowEnv hs' first last trans) α hL ⟨ml, mn⟩ hperm T,
      constraints_congr hu hag, lookupValues_congr hl hag]
  simp only [verify_constraints_with_lookups, hfold]

/-! ## Ring maps commute with the constraints -/

section map

variable {R S : Type _} [CommRing R] [CommRing S] (φ : R →+* S)

/-- A column with every entry mapped. -/
def mapColumn (c : Column R) : Column S :=
  ⟨c.flags.map φ, c.tuples.map (·.map φ), c.mults.map φ, φ c.alpha, φ c.beta⟩

theorem map_fingerprint (β : R) (e : List R) : φ (fingerprint β e) = fingerprint (φ β) (e.map φ) := by
  simp only [fingerprint, map_sum, map_mul, map_pow, List.length_map, ← List.map_reverse,
    getD_map_zero φ (map_zero φ)]

theorem getD_map_pair (terms : List (R × R)) (i : ℕ) :
    (terms.map (Prod.map φ φ)).getD i (1, 0) = Prod.map φ φ (terms.getD i (1, 0)) := by
  simpa using List.getD_map (f := Prod.map φ φ) (l := terms) (n := i) (d := (1, 0))

theorem map_numerator (terms : List (R × R)) :
    φ (numerator terms) = numerator (terms.map (Prod.map φ φ)) := by
  simp only [numerator, mul, den, map_sum, map_mul, map_prod, List.length_map, getD_map_pair,
    Prod.map_fst, Prod.map_snd]

theorem map_denominator (terms : List (R × R)) :
    φ (denominator terms) = denominator (terms.map (Prod.map φ φ)) := by
  simp only [denominator, den, map_prod, List.length_map, getD_map_pair, Prod.map_fst]

theorem numDen_map (c : Column R) :
    (mapColumn φ c).numDen = (φ c.numDen.1, φ c.numDen.2) := by
  have hds : ((c.tuples.map (·.map φ)).map fun e => φ c.alpha - fingerprint (φ c.beta) e) =
      (c.tuples.map fun e => c.alpha - fingerprint c.beta e).map φ := by
    simp [Function.comp_def, map_fingerprint]
  unfold Column.numDen
  simp only [mapColumn, List.map_eq_nil_iff]
  rw [hds]
  split_ifs
  · rw [List.zip_map, map_numerator, map_denominator]
  · rw [List.zip_map, List.zip_map]
    simp [map_list_sum, Function.comp_def]

theorem logUpConstraints_map (cols : List (Column R)) (fracs : List R) (acc acc' T first last trans : R) :
    (logUpConstraints cols fracs acc acc' T first last trans).map φ =
      logUpConstraints (cols.map (mapColumn φ)) (fracs.map φ) (φ acc) (φ acc') (φ T) (φ first)
        (φ last) (φ trans) := by
  simp [logUpConstraints, List.zip_map, numDen_map, map_list_sum, Function.comp_def]

end map

/-! ## The constraint polynomial -/

/-- A lookup's expressions substituted by univariate polynomials, with the pair of its slot as constants. -/
noncomputable def columnPoly (σ : Var → K[X]) (ch : List K) (l : Lookup F) : Column K[X] :=
  ⟨(l.flags.getD []).map (MvPolynomial.aeval σ ∘ toPoly),
    l.elements.map (·.map (MvPolynomial.aeval σ ∘ toPoly)),
    l.multiplicities.map (MvPolynomial.aeval σ ∘ toPoly), C (ch.getD (2 * l.column) 0),
    C (ch.getD (2 * l.column + 1) 0)⟩

/-- The lookup constraint polynomials of one AIR.

The permutation column c is the polynomial P_c: P_0 is the accumulator, P_(c + 1) the fraction of lookup c.

The next row is P_0(omega X), and the selectors are those of the assignment. -/
noncomputable def lookupPolys (σ : Var → K[X]) (ω : K) (P : ℕ → K[X]) (ch : List K) (T : K)
    (lookups : List (Lookup F)) : List K[X] :=
  if lookups = [] then []
  else logUpConstraints (lookups.map (columnPoly σ ch))
    ((List.range lookups.length).map fun c => P (c + 1)) (P 0) ((P 0).comp (C ω * X)) (C T)
    (σ .isFirstRow) (σ .isLastRow) (σ .isTransition)

/-- The permutation row opened at zeta and at omega zeta: one entry per column, or none without lookups. -/
noncomputable def permOpening (ω ζ : K) (P : ℕ → K[X]) (lookups : List (Lookup F)) : RowWindow K :=
  let w := if lookups = [] then 0 else lookups.length + 1
  ⟨(List.range w).map fun c => (P c).eval ζ, (List.range w).map fun c => (P c).eval (ω * ζ)⟩

theorem eval_combinePolys (α : K) (ps : List K[X]) (x : K) :
    (combinePolys α ps).eval x = combine α (ps.map (eval x)) := by
  simp only [combinePolys, combine, eval_finsetSum, eval_mul, eval_C, List.length_map]
  refine sum_congr rfl fun i _ => ?_
  rw [getD_map_zero _ eval_zero]

/-- At zeta, the lookup constraint polynomials take the lookup constraint values of the opened row. -/
theorem lookupPolys_eval (σ : Var → K[X]) (ω ζ : K) (P : ℕ → K[X]) (ch : List K) (T : K)
    (lookups : List (Lookup F)) :
    (lookupPolys σ ω P ch T lookups).map (eval ζ) =
      lookupValues (fun v => (σ v).eval ζ) ch (permOpening ω ζ P lookups) T ((σ .isFirstRow).eval ζ)
        ((σ .isLastRow).eval ζ) ((σ .isTransition).eval ζ) lookups := by
  unfold lookupPolys lookupValues
  split_ifs with h0
  · rfl
  · have hcol : (lookups.map (columnPoly σ ch)).map (mapColumn (evalRingHom ζ)) =
        lookups.map (columnAt (fun v => (σ v).eval ζ) ch) := by
      simp [columnPoly, columnAt, mapColumn, Function.comp_def, eval_aeval]
    have hfr : ((List.range lookups.length).map fun c => P (c + 1)).map (evalRingHom ζ) =
        (List.range lookups.length).map fun c => (permOpening ω ζ P lookups).current.getD (c + 1) 0 := by
      rw [List.map_map]
      refine List.map_congr_left fun c hc => ?_
      have := List.mem_range.1 hc
      simp [permOpening, h0, List.getD_eq_getElem?_getD, show c + 1 < lookups.length + 1 by omega]
    have := logUpConstraints_map (evalRingHom ζ) (lookups.map (columnPoly σ ch))
      ((List.range lookups.length).map fun c => P (c + 1)) (P 0) ((P 0).comp (C ω * X)) (C T)
      (σ .isFirstRow) (σ .isLastRow) (σ .isTransition)
    rw [hcol, hfr] at this
    simp only [coe_evalRingHom] at this
    rw [this]
    congr 1 <;> simp [permOpening, h0, eval_comp]

/-! ## The check at zeta -/

variable (G : Gen K)

/-- The univariate assignment of an instance on its trace coset. -/
noncomputable def instAssign (c : Coset G) (main prep periodic : ℕ → K[X]) (pv : List F) : Var → K[X] :=
  starkAssign c.shift c.subgroup_generator c.log_size main prep (fun j => algebraMap F K (pv.getD j 0))
    periodic

/-- The constraint polynomial of an instance: the AIR's constraints, then its lookup constraints. -/
noncomputable def instancePoly (air : Air F) (c : Coset G) (main prep periodic : ℕ → K[X]) (pv : List F)
    (P : ℕ → K[X]) (ch : List K) (T α : K) (lookups : List (Lookup F)) : K[X] :=
  combinePolys α ((constraints air).map (MvPolynomial.aeval (instAssign G c main prep periodic pv)) ++
    lookupPolys (instAssign G c main prep periodic pv) c.subgroup_generator P ch T lookups)

/-- Off the coset, the opened rows hold the assignment at zeta, with the selectors at zeta. -/
theorem holds_at_zeta (hV : GenValid G) (h2 : (2 : K) ≠ 0) {air : Air F} (c : Coset G)
    (main prep periodic : ℕ → K[X]) {pv : List F} (hpv : pv.length = air.num_public_values) {ζ : K}
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ) {sels : LagrangeSelectors K}
    (hsel : Coset.selectors_at_point G c ζ = some sels) :
    let σ := instAssign G c main prep periodic pv
    Holds air (fun v => (σ v).eval ζ)
      ⟨openRow σ (.main 0) air.width ζ, openRow σ (.main 1) air.width ζ⟩
      ⟨openRow σ (.prep 0) air.preprocessed_width ζ, openRow σ (.prep 1) air.preprocessed_width ζ⟩
      (pv.map (algebraMap F K)) (openRow σ .periodic air.num_periodic_columns ζ)
      sels.is_first_row sels.is_last_row sels.is_transition := by
  intro σ
  rw [selectors_at_point_some G hV h2 c ζ hζ, Option.some.injEq] at hsel
  subst hsel
  exact {
    shapes := ⟨by simp [openRow], by simp [openRow], by simp [openRow], by simp [openRow],
      by simp [hpv], by simp [openRow]⟩
    main_current := fun _ h => getD_openRow σ _ h ζ
    main_next := fun _ h => getD_openRow σ _ h ζ
    prep_current := fun _ h => getD_openRow σ _ h ζ
    prep_next := fun _ h => getD_openRow σ _ h ζ
    pub := fun j _ => by
      rw [getD_map_zero _ (map_zero _)]
      simp [σ, instAssign, starkAssign]
    periodic := fun _ h => getD_openRow σ _ h ζ
    first := by simp [σ, instAssign, starkAssign]
    last := by simp [σ, instAssign, starkAssign, lastIdx, mul_assoc]
    trans := by
      simp [σ, instAssign, starkAssign, cosetPoints, lastIdx, div_eq_inv_mul] }

/-- **The check at zeta, against the constraint polynomial.**

Take an instance with any trace coset, any trace polynomials and any permutation columns.

Open them honestly at zeta, off the coset.

Then the verifier's fold is the instance's constraint polynomial C at zeta.

So the check accepts exactly when C(zeta) s^n / Z(zeta) is the quotient value. -/
theorem verify_constraints_with_lookups_eq (hV : GenValid G) (h2 : (2 : K) ≠ 0) {air : Air F}
    (hb : air.public_boundary_io = []) (c : Coset G) (main prep periodic : ℕ → K[X]) {pv : List F}
    (hpv : pv.length = air.num_public_values) (P : ℕ → K[X]) {ch : List K}
    {lookups : List (Lookup F)} (hL : LaidOut air ch lookups) (T α q : K) {ζ : K}
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ) :
    let σ := instAssign G c main prep periodic pv
    let perm := permOpening c.subgroup_generator ζ P lookups
    verify_constraints_with_lookups G air (openRow σ (.main 0) air.width ζ)
      (openRow σ (.main 1) air.width ζ) (openRow σ (.prep 0) air.preprocessed_width ζ)
      (openRow σ (.prep 1) air.preprocessed_width ζ) perm.current perm.next ch
      (if lookups = [] then [] else [T]) (openRow σ .periodic air.num_periodic_columns ζ) lookups pv c
      ζ α q =
      some (if (instancePoly G air c main prep periodic pv P ch T α lookups).eval ζ *
          (c.shift ^ 2 ^ c.log_size / (vanishing c.shift c.subgroup_generator c.log_size).eval ζ) = q
        then .ok () else .error .OodEvaluationMismatch) := by
  intro σ perm
  obtain ⟨sels, hsel⟩ : ∃ sels, Coset.selectors_at_point G c ζ = some sels :=
    ⟨_, selectors_at_point_some G hV h2 c ζ hζ⟩
  have hiv : sels.inv_vanishing =
      c.shift ^ 2 ^ c.log_size / (vanishing c.shift c.subgroup_generator c.log_size).eval ζ := by
    rw [selectors_at_point_some G hV h2 c ζ hζ, Option.some.injEq] at hsel; rw [← hsel]
  have hZ : Coset.vanishing_poly_at_point G c ζ ≠ 0 :=
    fun h => hζ ((vanishing_poly_at_point_eq_zero G hV c ζ).1 h)
  have hH := holds_at_zeta G hV h2 c main prep periodic hpv hζ hsel
  have hfold := eval_air_and_lookups_verifier hH α hL perm
    (fun h0 => by simp [perm, permOpening, h0]) T
  have hpoly : (instancePoly G air c main prep periodic pv P ch T α lookups).eval ζ =
      combine α ((constraints air).map (MvPolynomial.aeval fun v => (σ v).eval ζ) ++
        lookupValues (fun v => (σ v).eval ζ) ch perm T sels.is_first_row sels.is_last_row
          sels.is_transition lookups) := by
    rw [instancePoly, eval_combinePolys, List.map_append, List.map_map, lookupPolys_eval, hH.first,
      hH.last, hH.trans]
    simp only [Function.comp_def, eval_aeval]; rfl
  unfold verify_constraints_with_lookups
  simp only [hb, ne_eq, not_true_eq_false, ite_false, hZ, hsel, Option.bind_eq_bind, Option.bind_some]
  rw [hfold, Option.bind_some, ← hpoly, hiv]
  split_ifs <;> simp_all

/-- A zeta on the trace coset is rejected with the domain error, whatever the openings. -/
theorem verify_constraints_with_lookups_in_domain (hV : GenValid G) {air : Air F}
    (hb : air.public_boundary_io = []) (tl tn pl pn ml mn ch vals per : List K) (lookups : List (Lookup F))
    (pv : List F) (c : Coset G) {ζ : K} (hζ : InCoset c.shift c.subgroup_generator c.log_size ζ)
    (α q : K) :
    verify_constraints_with_lookups G air tl tn pl pn ml mn ch vals per lookups pv c ζ α q =
      some (.error .OodPointInDomain) := by
  have hZ := (vanishing_poly_at_point_eq_zero G hV c ζ).2 hζ
  simp [verify_constraints_with_lookups, hb, hZ]

/-- An AIR with boundary cells panics. -/
theorem verify_constraints_with_lookups_boundary {air : Air F} (hb : air.public_boundary_io ≠ [])
    (tl tn pl pn ml mn ch vals per : List K) (lookups : List (Lookup F)) (pv : List F) (c : Coset G)
    (ζ α q : K) :
    verify_constraints_with_lookups G air tl tn pl pn ml mn ch vals per lookups pv c ζ α q = none := by
  simp [verify_constraints_with_lookups, hb]

/-- **Completeness at zeta.**

Assume the vanishing polynomial of the coset divides the instance's constraint polynomial C.

Then the honest quotient s^n C / Z, opened at zeta, passes the check. -/
theorem verify_constraints_with_lookups_complete (hV : GenValid G) (h2 : (2 : K) ≠ 0) {air : Air F}
    (hb : air.public_boundary_io = []) (c : Coset G) (main prep periodic : ℕ → K[X]) {pv : List F}
    (hpv : pv.length = air.num_public_values) (P : ℕ → K[X]) {ch : List K}
    {lookups : List (Lookup F)} (hL : LaidOut air ch lookups) (T α : K) {ζ : K}
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ)
    (hdvd : vanishing c.shift c.subgroup_generator c.log_size ∣
      instancePoly G air c main prep periodic pv P ch T α lookups) :
    let σ := instAssign G c main prep periodic pv
    let perm := permOpening c.subgroup_generator ζ P lookups
    verify_constraints_with_lookups G air (openRow σ (.main 0) air.width ζ)
      (openRow σ (.main 1) air.width ζ) (openRow σ (.prep 0) air.preprocessed_width ζ)
      (openRow σ (.prep 1) air.preprocessed_width ζ) perm.current perm.next ch
      (if lookups = [] then [] else [T]) (openRow σ .periodic air.num_periodic_columns ζ) lookups pv c
      ζ α ((quotientPoly c.shift c.subgroup_generator c.log_size
        (instancePoly G air c main prep periodic pv P ch T α lookups)).eval ζ) = some (.ok ()) := by
  intro σ perm
  have hZ : (vanishing c.shift c.subgroup_generator c.log_size).eval ζ ≠ 0 := by
    rw [eval_vanishing G hV, sub_ne_zero]
    exact fun h => hζ ((inCoset_iff (prim G hV c) c.shift_ne_zero).mpr h)
  rw [verify_constraints_with_lookups_eq G hV h2 hb c main prep periodic hpv P hL T α _ hζ,
    eval_quotientPoly hdvd hZ]
  split_ifs with h
  · rfl
  · exact absurd (by ring) h

/-- **A one-row trace.**

On a coset of one point s, the boundary selectors are the constant 1.

The transition selector is (X - s) / s, a multiple of the vanishing polynomial.

So every transition constraint vanishes on the domain.

The accumulator then only asks acc = 0 and T = acc + sum_c f_c. -/
theorem one_row_selectors (s : K) (main prep : ℕ → K[X]) (pub : ℕ → K) (periodic : ℕ → K[X]) :
    starkAssign s 1 0 main prep pub periodic .isFirstRow = 1 ∧
      starkAssign s 1 0 main prep pub periodic .isLastRow = 1 ∧
      starkAssign s 1 0 main prep pub periodic .isTransition = C s⁻¹ * vanishing s 1 0 := by
  have hl : ∀ i, lagrange s 1 0 i = 1 := fun i => by
    rw [lagrange, Lagrange.basis]
    exact Finset.prod_eq_one fun j hj => absurd (Fin.ext (by omega)) (Finset.mem_erase.1 hj).1
  refine ⟨by simp [starkAssign, hl], by simp [starkAssign, hl], ?_⟩
  simp [starkAssign, vanishing, Lagrange.nodal, cosetPoints]

/-! ## Several instances at one zeta -/

/-- **The pair a lookup reads under the batch layout.**

Lookup j of instance i, in slot j, reads two values:

- alpha + (id + 1) beta^W, with id its bus id
- beta.

So each tuple's denominator is the domain-separated denominator of its bus.

Local lookups have their own bus id, and global lookups share the id of their bus name. -/
theorem columnAt_layout {all : List (List (Lookup F))} {ids : List (List ℕ)} {st : LayoutState}
    (h : busIds all = some (ids, st)) (αL βL : K) (env : Var → K) {i j : ℕ} (hi : i < ids.length)
    (hj : j < ids[i].length) (l : Lookup F) (hl : l.column = j) :
    ∃ ch, lay_out_lookup_challenges 2 all αL βL = some ch ∧
      (columnAt env (ch.getD i []) l).alpha = αL + ((ids[i][j] : K) + 1) * βL ^ st.max_message_width ∧
      (columnAt env (ch.getD i []) l).beta = βL ∧
      ∀ e, (columnAt env (ch.getD i []) l).alpha - fingerprint (columnAt env (ch.getD i []) l).beta e =
        busDenom αL βL st.max_message_width ids[i][j] e := by
  obtain ⟨ch, hch, h1, h2⟩ := lay_out_pair h αL βL hi hj
  obtain ⟨x, hx, ha⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨y, hy, hb⟩ := Option.bind_eq_some_iff.1 h2
  obtain rfl : x = y := Option.some.inj (hx.symm.trans hy)
  have hget : ch.getD i [] = x := by simp [List.getD_eq_getElem?_getD, hx]
  have ha' : x.getD (2 * j) 0 = αL + ((ids[i][j] : K) + 1) * βL ^ st.max_message_width := by
    simp [List.getD_eq_getElem?_getD, ha]
  have hb' : x.getD (2 * j + 1) 0 = βL := by simp [List.getD_eq_getElem?_getD, hb]
  refine ⟨ch, hch, ?_, ?_, fun e => ?_⟩ <;>
    simp only [columnAt, hl, hget, ha', hb', busDenom]

/-- **Several instances at one zeta.**

Each instance has its own trace coset, of its own size.

All share zeta and alpha, and read their lookup pairs from one challenge table.

Every check passes exactly when each instance's constraint polynomial meets its quotient at zeta. -/
theorem batch_checks_at_zeta (hV : GenValid G) (h2 : (2 : K) ≠ 0) (n : ℕ) (airs : ℕ → Air F)
    (hb : ∀ i < n, (airs i).public_boundary_io = []) (cs : ℕ → Coset G) (mains preps pers : ℕ → ℕ → K[X])
    (pvs : ℕ → List F) (hpv : ∀ i < n, (pvs i).length = (airs i).num_public_values)
    (Ps : ℕ → ℕ → K[X]) (ch : List (List K)) (all : List (List (Lookup F)))
    (hL : ∀ i < n, LaidOut (airs i) (ch.getD i []) (all.getD i [])) (Ts : ℕ → K) (α ζ : K) (qs : ℕ → K)
    (hζ : ∀ i < n, ¬ InCoset (cs i).shift (cs i).subgroup_generator (cs i).log_size ζ) :
    (∀ i < n,
      let σ := instAssign G (cs i) (mains i) (preps i) (pers i) (pvs i)
      let perm := permOpening (cs i).subgroup_generator ζ (Ps i) (all.getD i [])
      verify_constraints_with_lookups G (airs i) (openRow σ (.main 0) (airs i).width ζ)
        (openRow σ (.main 1) (airs i).width ζ) (openRow σ (.prep 0) (airs i).preprocessed_width ζ)
        (openRow σ (.prep 1) (airs i).preprocessed_width ζ) perm.current perm.next (ch.getD i [])
        (if all.getD i [] = [] then [] else [Ts i]) (openRow σ .periodic (airs i).num_periodic_columns ζ)
        (all.getD i []) (pvs i) (cs i) ζ α (qs i) = some (.ok ())) ↔
      ∀ i < n,
        (instancePoly G (airs i) (cs i) (mains i) (preps i) (pers i) (pvs i) (Ps i) (ch.getD i []) (Ts i)
          α (all.getD i [])).eval ζ *
          ((cs i).shift ^ 2 ^ (cs i).log_size /
            (vanishing (cs i).shift (cs i).subgroup_generator (cs i).log_size).eval ζ) = qs i := by
  refine forall₂_congr fun i hi => ?_
  dsimp only
  rw [verify_constraints_with_lookups_eq G hV h2 (hb i hi) (cs i) _ _ _ (hpv i hi) (Ps i) (hL i hi) (Ts i)
    α (qs i) (hζ i hi)]
  split_ifs with h <;> simpa using h

end Plonky3Lean.Proofs.BatchStark
