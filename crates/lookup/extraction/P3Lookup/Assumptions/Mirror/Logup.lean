/-
Transcriptions of the LogUp gadget.

They cover the tuple combiners, the rational folds, the constraints, the degree, and the terminal check.

These do not extract.
They are generic over the field traits and over the builder, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the p3-air builder transcriptions:

* a permutation builder is an extension builder with the extension ring and the base embedding
* it also holds the permutation window, challenges and values
* a strict zip on unequal lengths, an index out of range, and a failed assertion are a panic, which is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Lookup.Assumptions.Mirror.Types

@[expose] public section

namespace p3_lookup.mirror

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror

/-- The ring operations of an expression type. -/
structure RingOps (E : Type) where
  add : E → E → E
  sub : E → E → E
  mul : E → E → E
  zero : E
  one : E

/-- The permutation builder trait.

It extends an extension builder with:

- the extension ring
- the embedding of base expressions
- the permutation window, challenges and values. -/
structure PermBuilder (F E EE S : Type) extends ExtensionBuilder F E EE S where
  ext : RingOps EE
  ext_of : E → EE
  permutation : S → RowWindow EE
  permutation_randomness : S → List EE
  permutation_values : S → List EE

/-- The strict zip: the pairs, and a panic on unequal lengths. -/
def zip_eq {α β : Type _} (l : List α) (l' : List β) : Option (List (α × β)) :=
  if l.length = l'.length then some (l.zip l') else none

/-- Each tuple folded by Horner's rule, elt + acc * beta, then subtracted from alpha. -/
def combine_elements {E : Type} (R : RingOps E) (elements : List (List E)) (alpha beta : E) :
    List E :=
  elements.map fun elts =>
    R.sub alpha (elts.foldl (fun acc elt => R.add elt (R.mul acc beta)) R.zero)

/-- The numerator and denominator of sum_i m_i / t_i, through prefix and suffix products.

No tuple gives 0 / 1.

A multiplicity list shorter than the tuples panics. -/
def compute_combined_sum_terms {E : Type} (R : RingOps E) (elements : List (List E))
    (multiplicities : List E) (alpha beta : E) : Option (E × E) :=
  if elements.isEmpty then some (R.zero, R.one)
  else
    let n := elements.length
    let terms := combine_elements R elements alpha beta
    -- pref[i] = prod_(j < i) t_j
    let pref := terms.scanl (fun acc t => R.mul acc t) R.one
    -- suff[i] = prod_(j >= i) t_j
    let suff := terms.scanr (fun t acc => R.mul acc t) R.one
    let common_denominator := pref[n]?.getD R.zero
    let numerator := (List.range n).foldlM (fun acc i => do
      let m ← multiplicities[i]?
      let p ← pref[i]?
      let s ← suff[i + 1]?
      pure (R.add acc (R.mul (R.mul m p) s))) R.zero
    numerator.map (·, common_denominator)

/-- The numerator and denominator of an exclusive column:

- N = sum_k f_k m_k
- D = sum_k f_k t_k + 1 - sum_k f_k.

Unequal lengths panic. -/
def compute_exclusive_terms {E : Type} (R : RingOps E) (flags : List E) (elements : List (List E))
    (multiplicities : List E) (alpha beta : E) : Option (E × E) := do
  let terms := combine_elements R elements alpha beta
  let ftm ← zip_eq flags terms
  let ftm ← zip_eq ftm multiplicities
  let (numerator, denominator, flag_sum) := ftm.foldl (fun (st : E × E × E) x =>
    let ((flag, term), mult) := x
    (R.add st.1 (R.mul flag mult), R.add st.2.1 (R.mul flag term), R.add st.2.2 flag))
    (R.zero, R.zero, R.zero)
  pure (numerator, R.add denominator (R.sub R.one flag_sum))

variable {F : Type} [Field F] [DecidableEq F]

/-- Pin one lookup's fraction column on the current row: assert U f - V.

The lengths must agree, there must be two challenges per slot, and the column must exist. -/
def eval_fraction {E EE S : Type} (B : PermBuilder F E EE S) (s : S) (lookup : Lookup F) :
    Option S := do
  if lookup.elements.length ≠ lookup.multiplicities.length then none
  let elements ← lookup.elements.mapM fun exprs =>
    exprs.mapM fun e => (resolve B.toAirBuilder s e).map B.ext_of
  let multiplicities ← lookup.multiplicities.mapM fun e => (resolve B.toAirBuilder s e).map B.ext_of
  let permutation := B.permutation s
  let permutation_challenges := B.permutation_randomness s
  if permutation_challenges.length < 2 * (lookup.column + 1) then none
  let alpha ← permutation_challenges[2 * lookup.column]?
  let beta ← permutation_challenges[2 * lookup.column + 1]?
  let frac_local ← permutation.current[lookup.column + 1]?
  let flags ← (lookup.flags.getD []).mapM fun e => (resolve B.toAirBuilder s e).map B.ext_of
  let (numerator, common_denominator) ←
    if flags.isEmpty then compute_combined_sum_terms B.ext elements multiplicities alpha beta
    else compute_exclusive_terms B.ext flags elements multiplicities alpha beta
  pure (B.assert_zero_ext s (B.ext.sub (B.ext.mul common_denominator frac_local) numerator))

/-- The accumulator constraints on the current row:

- acc = 0 on the first row
- acc' = acc + row sum on transitions
- terminal = acc + row sum on the last row.

The permutation window must hold the accumulator and every fraction column. -/
def eval_accumulator {E EE S : Type} (B : PermBuilder F E EE S) (s : S) (lookups : List (Lookup F))
    (terminal : EE) : Option S := do
  let permutation := B.permutation s
  if ¬ permutation.current.length > lookups.length then none
  let acc_local ← permutation.current[0]?
  let acc_next ← permutation.next[0]?
  let row_sum ← lookups.foldlM (fun sum l => do
    let v ← permutation.current[l.column + 1]?
    pure (B.ext.add sum v)) B.ext.zero
  let s := (B.when (B.is_first_row s)).assert_zero_ext s acc_local
  let s := (B.when (B.is_transition s)).assert_zero_ext s
    (B.ext.sub (B.ext.sub acc_next acc_local) row_sum)
  pure ((B.when (B.is_last_row s)).assert_zero_ext s
    (B.ext.sub (B.ext.sub terminal acc_local) row_sum))

/-- Every lookup constraint of one AIR.

With no lookup, there must be no permutation value.

Otherwise there is one terminal, each fraction is pinned, then the accumulator is constrained. -/
def eval_all {E EE S : Type} (B : PermBuilder F E EE S) (s : S) (lookups : List (Lookup F)) :
    Option S := do
  if lookups.isEmpty then
    if (B.permutation_values s).length ≠ 0 then none
    pure s
  else
    if (B.permutation_values s).length ≠ 1 then none
    let terminal ← (B.permutation_values s)[0]?
    let s ← lookups.foldlM (fun s l => eval_fraction B s l) s
    eval_accumulator B s lookups terminal

/-- The cross-AIR check: the present terminals must sum to zero. -/
def verify_terminal_sum {EF : Type} [Field EF] [DecidableEq EF] (terminals : List (Option EF)) :
    Bool :=
  (terminals.filterMap id).sum = 0

/-- The degree of the fraction pin, with the transition selector at the given degree.

Additive: max(1 + sum_i deg_i, max_i (deg m_i + sum_(j != i) deg_j)).

Here deg_i is the largest degree in tuple i.

Exclusive: max(1 + max_k max(deg f_k + deg_k, deg f_k), max_k (deg f_k + deg m_k)).

Unequal lengths panic. -/
def constraint_degree_with_transition (lookup : Lookup F) (transition_degree : ℕ) : Option ℕ := do
  if lookup.multiplicities.length ≠ lookup.elements.length then none
  let degree := fun (e : SymbolicExpression F) => e.degree_multiple_with_transition transition_degree
  match lookup.flags with
  | some flags => do
    let fe ← zip_eq flags lookup.elements
    let deg_denom := ((fe.map fun (x : SymbolicExpression F × List (SymbolicExpression F)) =>
        degree x.1 + (x.2.map degree).foldr max 0) ++
      flags.map degree).foldr max 0
    let fm ← zip_eq flags lookup.multiplicities
    let deg_num := (fm.map fun x => degree x.1 + degree x.2).foldr max 0
    pure (max (1 + deg_denom) deg_num)
  | none =>
    let degs := lookup.elements.map fun elems => (elems.map degree).foldr max 0
    let deg_sum := degs.sum
    let deg_num :=
      ((lookup.multiplicities.zip degs).map fun x => degree x.1 + deg_sum - x.2).foldr max 0
    pure (max (1 + deg_sum) deg_num)

end p3_lookup.mirror
