module

public import P3Commit.Periodic
public import Plonky3Lean.Proofs.Commit.PeriodicBatch

@[expose] public section

/-!
# p3-commit: screening and tabulating periodic columns

The screen accepts exactly the columns whose length is a power of two dividing the height.

The compact table holds the longest period times the blowup rows.

Read modulo its height, it gives the periodic polynomial at every quotient-domain point.
-/

open Polynomial Finset
open p3_commit.periodic.mirror p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.Dft

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

/-! ## The screen -/

section screen

variable {K : Type _}

theorem isPowerOfTwo_iff (n : ℕ) : isPowerOfTwo n = true ↔ ∃ l, n = 2 ^ l := by
  constructor
  · intro h
    simp only [isPowerOfTwo, decide_eq_true_eq] at h
    exact ⟨_, h.2.symm⟩
  · rintro ⟨l, rfl⟩
    simp [isPowerOfTwo, Nat.log_pow (by norm_num : 1 < 2)]

/-- The column passes the screen: a power-of-two length dividing the height. -/
def ColumnOk (height : ℕ) (col : List K) : Prop :=
  isPowerOfTwo col.length = true ∧ height % col.length = 0

instance (height : ℕ) (col : List K) : Decidable (ColumnOk height col) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The error the screen reports for a failing column at an index. -/
def screenError (height : ℕ) (c : List K × ℕ) : PeriodicColumnShapeError :=
  if isPowerOfTwo c.1.length then .LengthNotDividingHeight c.2 c.1.length height
  else .LengthNotPowerOfTwo c.2 c.1.length

theorem screenStep_ok (height : ℕ) (c : List K × ℕ) :
    screenStep height (pure ()) c =
      if ColumnOk height c.1 then pure () else Except.error (screenError height c) := by
  unfold screenStep ColumnOk screenError
  by_cases h1 : isPowerOfTwo c.1.length <;> by_cases h2 : height % c.1.length = 0 <;>
    simp [h1, h2] <;> rfl

theorem foldl_screenStep_error (height : ℕ) (L : List (List K × ℕ)) (e : PeriodicColumnShapeError) :
    L.foldl (screenStep height) (Except.error e) = Except.error e := by
  induction L with
  | nil => rfl
  | cons c L ih => exact ih

/-- The screen returns the first failing column's error, and succeeds when none fails. -/
theorem foldl_screenStep (height : ℕ) (L : List (List K × ℕ)) :
    L.foldl (screenStep height) (pure ()) =
      match L.find? fun c => !decide (ColumnOk height c.1) with
      | none => pure ()
      | some c => Except.error (screenError height c) := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.foldl_cons, screenStep_ok, List.find?_cons]
    by_cases h : ColumnOk height c.1
    · simp only [h, ite_true, decide_true, Bool.not_true]
      exact ih
    · simp only [h, ite_false, decide_false, Bool.not_false]
      exact foldl_screenStep_error height L _

theorem new_eq (cols : List (List K)) (height : ℕ) :
    PeriodicColumns.new cols height =
      match cols.zipIdx.find? fun c => !decide (ColumnOk height c.1) with
      | none => .ok ⟨cols, height⟩
      | some c => .error (screenError height c) := by
  unfold PeriodicColumns.new
  rw [foldl_screenStep]
  cases (cols.zipIdx.find? fun c => !decide (ColumnOk height c.1)) <;> rfl

/-- The screen accepts exactly when every column's length is a power of two dividing the height. -/
theorem new_ok_iff (cols : List (List K)) (height : ℕ) :
    PeriodicColumns.new cols height = .ok ⟨cols, height⟩ ↔ ∀ col ∈ cols, ColumnOk height col := by
  rw [new_eq]
  split
  · rename_i hnone
    refine ⟨fun _ col hcol => ?_, fun _ => rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcol
    have := List.find?_eq_none.mp hnone (cols[i], i)
      (List.mem_zipIdx_iff_getElem?.mpr (by simp))
    simpa using this
  · rename_i c hc
    simp only [reduceCtorEq, false_iff, not_forall]
    have h1 := List.find?_some hc
    have h2 := List.mem_of_find?_eq_some hc
    have := (List.mem_zipIdx h2).2.2
    simp only [Nat.sub_zero] at this
    exact ⟨c.1, this ▸ List.getElem_mem _, by simpa using h1⟩

/-- A reported error names the first failing column. -/
theorem new_error (cols : List (List K)) (height : ℕ) (e : PeriodicColumnShapeError)
    (h : PeriodicColumns.new cols height = .error e) :
    ∃ i, ∃ hi : i < cols.length, ¬ ColumnOk height cols[i] ∧ e = screenError height (cols[i], i) ∧
      ∀ j (hj : j < i), ColumnOk height (cols[j]'(by omega)) := by
  rw [new_eq] at h
  split at h
  · simp at h
  · rename_i c hc
    simp only [Except.error.injEq] at h
    subst h
    obtain ⟨i, hi, hci, hbefore⟩ := List.find?_eq_some_iff_getElem.mp hc |>.2
    simp only [List.getElem_zipIdx, zero_add] at hci hbefore
    subst hci
    simp only [List.length_zipIdx] at hi
    have hbad := (List.find?_eq_some_iff_getElem.mp hc).1
    refine ⟨i, hi, by simpa using hbad, rfl, fun j hj => ?_⟩
    have := hbefore j hj
    simpa using this

end screen

/-! ## The compact table -/

section table

variable {K : Type _}

theorem trailingZeros_pow {a : ℕ} : trailingZeros (2 ^ a) = a := by
  simp [trailingZeros]

theorem gcd_two_pow (a w : ℕ) (hw : w ≠ 0) : Nat.gcd (2 ^ a) w = 2 ^ min a (padicValNat 2 w) := by
  obtain ⟨o, ho, hwo⟩ : ∃ o, ¬ 2 ∣ o ∧ w = 2 ^ padicValNat 2 w * o :=
    ⟨w / 2 ^ padicValNat 2 w, by
      intro h
      have := pow_succ_padicValNat_not_dvd (p := 2) hw
      obtain ⟨m, hm⟩ := h
      exact this ⟨m, by
        rw [pow_succ, mul_assoc, ← hm, Nat.mul_div_cancel' pow_padicValNat_dvd]⟩,
      (Nat.mul_div_cancel' pow_padicValNat_dvd).symm⟩
  have hco : Nat.Coprime (2 ^ a) o :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ho)
  conv_lhs => rw [hwo]
  rw [Nat.Coprime.gcd_mul_right_cancel_right _ hco.symm]
  rcases le_total a (padicValNat 2 w) with h | h
  · rw [min_eq_left h, Nat.gcd_eq_left (Nat.pow_dvd_pow 2 h)]
  · rw [min_eq_right h, Nat.gcd_eq_right (Nat.pow_dvd_pow 2 h)]

/-- On a power-of-two height, the packed group period is height / gcd(height, pack width). -/
theorem packed_group_period_eq (t : PeriodicLdeTable K) {a : ℕ} (ht : t.height = 2 ^ a) (ha : a < 64)
    {w : ℕ} (hw : w ≠ 0) (hw64 : w < 2 ^ 64) :
    t.packed_group_period w = some (t.height / Nat.gcd t.height w) := by
  have hv : padicValNat 2 w < 64 :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp
      ((Nat.le_of_dvd (Nat.pos_of_ne_zero hw) pow_padicValNat_dvd).trans_lt hw64)
  have htz : trailingZeros w = padicValNat 2 w := by simp [trailingZeros, hw]
  simp only [PeriodicLdeTable.packed_group_period, hw, ite_false, ht, trailingZeros_pow, htz,
    gcd_two_pow a w hw, show min a (padicValNat 2 w) < 64 by omega, ite_true]

/-- On a power-of-two height, a read takes row i mod height. -/
theorem get_eq (t : PeriodicLdeTable K) {a : ℕ} (ht : t.height = 2 ^ a) (i c : ℕ) :
    t.get i c = t.values[(i % 2 ^ a) * t.width + c]? := by
  simp [PeriodicLdeTable.get, ht, ← Nat.and_two_pow_sub_one_eq_mod]

/-- Group g of the packed reads sees the same values as group g mod the packed period. -/
theorem get_packed_period (t : PeriodicLdeTable K) {a : ℕ} (ht : t.height = 2 ^ a) (w g o c : ℕ) :
    t.get (g * w + o) c = t.get ((g % (t.height / Nat.gcd t.height w)) * w + o) c := by
  rw [get_eq t ht, get_eq t ht]
  congr 3
  set P := t.height / Nat.gcd t.height w
  obtain ⟨m, hm⟩ : 2 ^ a ∣ P * w := by
    have hg : 0 < Nat.gcd t.height w := Nat.gcd_pos_of_pos_left _ (by rw [ht]; positivity)
    obtain ⟨u, hu⟩ := Nat.gcd_dvd_left t.height w
    obtain ⟨v, hv⟩ := Nat.gcd_dvd_right t.height w
    have hP : P = u := Nat.div_eq_of_eq_mul_left hg (by rw [mul_comm]; exact hu)
    refine ⟨v, ?_⟩
    rw [hP, ← ht]
    generalize Nat.gcd t.height w = d at hu hv
    subst hv
    rw [hu]
    ring
  conv_lhs => rw [← Nat.mod_add_div g P]
  rw [add_mul, add_right_comm, mul_comm P, mul_assoc, hm,
    show g / P * (2 ^ a * m) = 2 ^ a * (g / P * m) by ring, Nat.add_mul_mod_self_left]

end table

/-! ## Tabulating on the quotient domain -/

section build

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

/-- The quotient points are x_0 omega^r, for r below the count. -/
theorem quotientPoints_eq (q : Coset G) (n : ℕ) (x0 : K) :
    quotientPoints G q n x0 = some ((List.range n).map fun r => x0 * q.subgroup_generator ^ r) := by
  induction n generalizing x0 with
  | zero => rfl
  | succ n ih =>
    simp only [quotientPoints, Coset.next_point, Option.bind_eq_bind, Option.bind_some, ih,
      Option.pure_def, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
      pow_zero, mul_one, pow_succ', mul_assoc]

/-- Padding a column to a multiple of its length keeps its periodic polynomial. -/
theorem periodicPoly_pad (s ω : K) (k : ℕ) (col : List K) (mp : ℕ) (hmp : 0 < mp)
    (hdvd : col.length ∣ mp) :
    periodicPoly s ω k ((List.range mp).map fun i => col.getD (i % col.length) 0) =
      periodicPoly s ω k col := by
  simp only [periodicPoly, List.length_map, List.length_range]
  congr 1
  funext i
  simp [List.getD_eq_getElem?_getD, Nat.mod_lt _ hmp, Nat.mod_mod_of_dvd _ hdvd]

/-- The periodic polynomial of a column of length 2^l repeats on a coset of order 2^(k + b).

Its period there is 2^(l + b). -/
theorem periodicPoly_periodic (hV : GenValid G) (hN : GenNested G) {s : K} (hs : s ≠ 0)
    {k l b : ℕ} (hkb : k + b ≤ G.adicity) (hl : l ≤ k) (col : List K) (hcol : col.length = 2 ^ l)
    (t : K) (i : ℕ) :
    (periodicPoly s (G.gen k) k col).eval (t * G.gen (k + b) ^ i) =
      (periodicPoly s (G.gen k) k col).eval (t * G.gen (k + b) ^ (i % 2 ^ (l + b))) := by
  have hk : k ≤ G.adicity := by omega
  rw [← comp_eq_periodicPoly G hV hN hs hk hl col hcol, eval_comp, eval_comp]
  simp only [eval_pow, eval_X, mul_pow, ← pow_mul]
  have hg : G.gen (k + b) ^ 2 ^ (k - l) = G.gen (l + b) := by
    rw [← gen_sub G hN hkb (show k - l ≤ k + b by omega)]; congr 1; omega
  have hm : G.gen (l + b) ^ (i % 2 ^ (l + b)) = G.gen (l + b) ^ i := by
    rw [(hV _ (by omega)).eq_orderOf, pow_mod_orderOf]
  rw [mul_comm i, mul_comm (i % _), pow_mul, pow_mul, hg, hm]

/-- Flattening rows of one width w: entry r w + c is entry c of row r. -/
theorem flatten_getElem? {α : Type _} (rows : List (List α)) (w : ℕ)
    (hw : ∀ row ∈ rows, row.length = w) (r c : ℕ) (hc : c < w) :
    rows.flatten[r * w + c]? = (rows[r]?).bind fun row => row[c]? := by
  induction rows generalizing r with
  | nil => simp
  | cons row rows ih =>
    have hrow := hw row List.mem_cons_self
    rcases r with _ | r
    · simp [List.getElem?_append_left (show c < row.length by omega)]
    · rw [List.flatten_cons, List.getElem?_append_right (by rw [hrow]; nlinarith),
        show (r + 1) * w + c - row.length = r * w + c by rw [hrow]; ring_nf; omega,
        ih (fun row' h => hw row' (List.mem_cons_of_mem _ h))]
      simp

/-- The table of a nonempty set of good columns.

Take a trace of order 2^k and a quotient of order 2^(k + b).

The table holds the longest period times 2^b rows.

A read at any index i is column c's periodic polynomial at quotient point i. -/
theorem build_periodic_lde_table_eq (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (trace quotient : Coset G) (cols : List (List K)) (hle : trace.log_size ≤ quotient.log_size)
    (hcols : ∀ col ∈ cols, ∃ l, col.length = 2 ^ l ∧ l ≤ trace.log_size) (hne : cols ≠ [])
    (hword : Coset.size G quotient * cols.length < 2 ^ 64) :
    ∃ t, build_periodic_lde_table G cols trace quotient = some t ∧ t.width = cols.length ∧
      (∃ mp ∈ cols.map List.length, t.height = mp * 2 ^ (quotient.log_size - trace.log_size)) ∧
      ∀ i c (hc : c < cols.length), t.get i c =
        some ((periodicPoly trace.shift trace.subgroup_generator trace.log_size cols[c]).eval
          (quotient.shift * quotient.subgroup_generator ^ i)) := by
  obtain ⟨b, hb⟩ : ∃ b, quotient.log_size = trace.log_size + b := ⟨_, (Nat.add_sub_cancel' hle).symm⟩
  set k := trace.log_size
  have hqs : Coset.size G quotient = 2 ^ (k + b) := by rw [size_eq, hb]
  have hts : Coset.size G trace = 2 ^ k := size_eq G trace
  have hnc : 0 < cols.length := List.length_pos_iff.mpr hne
  -- The screen passes.
  have hscreen : PeriodicColumns.new cols (2 ^ k) = .ok ⟨cols, 2 ^ k⟩ :=
    (new_ok_iff cols _).mpr fun col hcol => by
      obtain ⟨l, hl, hlk⟩ := hcols col hcol
      exact ⟨(isPowerOfTwo_iff _).mpr ⟨l, hl⟩, by
        rw [hl]; exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hlk)⟩
  -- The longest period.
  obtain ⟨mp, hmp⟩ : ∃ mp, (cols.map List.length).max? = some mp :=
    Option.isSome_iff_exists.mp (by
      rw [Option.isSome_iff_ne_none, ne_eq, List.max?_eq_none_iff]; simpa using hne)
  obtain ⟨hmem, hmax⟩ := List.max?_eq_some_iff.mp hmp
  obtain ⟨col0, hcol0, rfl⟩ := List.mem_map.mp hmem
  obtain ⟨L, hL, hLk⟩ := hcols col0 hcol0
  have hdvd : ∀ col ∈ cols, col.length ∣ col0.length := fun col hcol => by
    obtain ⟨l, hl, -⟩ := hcols col hcol
    have := hmax _ (List.mem_map_of_mem hcol)
    rw [hl, hL] at this ⊢
    exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp this)
  have hblow : 2 ^ (k + b) / 2 ^ k = 2 ^ b := by
    rw [Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  have hext : col0.length * 2 ^ b = 2 ^ (L + b) := by rw [hL, pow_add]
  have hextq : 2 ^ (L + b) ≤ 2 ^ (k + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hext64 : 2 ^ (L + b) * cols.length < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hextq) (hqs ▸ hword)
  simp only [build_periodic_lde_table, hts, hqs, hblow, hscreen, PeriodicColumns.max_period, hmp,
    hext]
  have c1 : ¬ 2 ^ (k + b) < 2 ^ k := not_lt.mpr (Nat.pow_le_pow_right (by norm_num) (by omega))
  have c2 : 2 ^ (k + b) % 2 ^ k = 0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
  have c3 : ¬ WORD ≤ 2 ^ (L + b) := not_le.mpr (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hnc) hext64)
  have c4 : ¬ 2 ^ (k + b) < 2 ^ (L + b) := not_lt.mpr hextq
  have c5 : ¬ WORD ≤ 2 ^ (L + b) * cols.length := not_le.mpr hext64
  -- The points and the rows.
  set x : ℕ → K := fun r => quotient.shift * quotient.subgroup_generator ^ r
  set P : List K → K[X] := fun col => periodicPoly trace.shift trace.subgroup_generator k col
  set R := (List.range (2 ^ (L + b))).map fun r => cols.map fun col => (P col).eval (x r)
  have hpad : ∀ col ∈ cols, ∀ pt, Coset.evaluate_periodic_column_at G trace
      ((List.range col0.length).map fun i => col.getD (i % col.length) 0) pt = some ((P col).eval pt) :=
    fun col hcol pt => by
      rw [evaluate_periodic_column_at_eq G hV hN h2 trace _ (by simp [hL]) hLk, periodicPoly_pad _ _ _ _ _
        (by rw [hL]; positivity) (hdvd col hcol)]
  have hrows : ((List.range (2 ^ (L + b))).map x).mapM (fun point =>
      (cols.map fun col => (List.range col0.length).map fun i => col.getD (i % col.length) 0).mapM
        fun padded => Coset.evaluate_periodic_column_at G trace padded point) = some R := by
    rw [mapM_some _ (fun point => cols.map fun col => (P col).eval point)]
    · simp [R]
    · intro point _
      rw [List.mapM_map]
      exact mapM_some _ _ _ fun col hcol => hpad col hcol point
  have hpts : quotientPoints G quotient (2 ^ (L + b)) (Coset.first_point G quotient) =
      some ((List.range (2 ^ (L + b))).map x) := by
    rw [quotientPoints_eq]; rfl
  have hlen : R.flatten.length = 2 ^ (L + b) * cols.length := by
    simp [R, List.length_flatten, Function.comp_def, List.sum_replicate]
  have hnew : PeriodicLdeTable.new R.flatten cols.length =
      some ⟨R.flatten, cols.length, 2 ^ (L + b)⟩ := by
    simp [PeriodicLdeTable.new, hnc.ne', hlen, Nat.mul_div_cancel _ hnc, isPowerOfTwo_iff]
  simp only [c1, c2, c3, c4, c5, ne_eq, not_true_eq_false, ite_false, hpts, Option.bind_eq_bind,
    Option.bind_some, List.take_of_length_le (by simp : ((List.range (2 ^ (L + b))).map x).length ≤ 2 ^ (L + b)),
    hrows, hnew]
  refine ⟨_, rfl, rfl, ⟨col0.length, hmem, by
    show 2 ^ (L + b) = _; rw [hb, hL, ← pow_add, Nat.add_sub_cancel_left]⟩,
    fun i c hc => ?_⟩
  rw [get_eq (a := L + b) _ rfl, flatten_getElem? R cols.length (by simp [R]) _ _ hc]
  obtain ⟨l, hl, hlk⟩ := hcols _ (List.getElem_mem hc)
  have hlL : l ≤ L := (Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num)).mp (by
    have := hmax _ (List.mem_map_of_mem (f := List.length) (List.getElem_mem hc))
    rwa [hl, hL] at this)
  have hkb : k + b ≤ G.adicity := hb ▸ quotient.log_size_le
  have hper := periodicPoly_periodic G hV hN trace.shift_ne_zero hkb hlk _ hl quotient.shift
  have hgq : quotient.subgroup_generator = G.gen (k + b) := by
    simp [TwoAdicMultiplicativeCoset.subgroup_generator, hb]
  simp only [R, x, P, List.getElem?_map, List.getElem?_range (Nat.mod_lt _ (by positivity : 0 < 2 ^ (L + b))),
    Option.map_some, Option.bind_some, List.getElem?_eq_getElem hc, hgq]
  simp only [TwoAdicMultiplicativeCoset.subgroup_generator] at hper ⊢
  rw [hper i, hper (i % _), Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : l + b ≤ L + b))]

/-- A declared column that fails the screen makes the table builder panic. -/
theorem build_periodic_lde_table_bad (trace quotient : Coset G) (cols : List (List K))
    (h : ∃ col ∈ cols, ¬ ColumnOk (Coset.size G trace) col) :
    build_periodic_lde_table G cols trace quotient = none := by
  have hne : ∀ p, PeriodicColumns.new cols (Coset.size G trace) ≠ .ok p := by
    intro p hp
    have hp' : PeriodicColumns.new cols (Coset.size G trace) = .ok ⟨cols, Coset.size G trace⟩ := by
      rw [hp]
      simp only [PeriodicColumns.new, bind, Except.bind] at hp ⊢
      split at hp
      · cases hp
      · cases hp; rfl
    obtain ⟨col, hcol, hbad⟩ := h
    exact hbad ((new_ok_iff _ _).mp hp' col hcol)
  unfold build_periodic_lde_table
  dsimp only
  split_ifs
  · rfl
  · rfl
  · split
    · rfl
    · rename_i p hp; exact absurd hp (hne p)

/-- No periodic columns give the empty table. -/
theorem build_periodic_lde_table_nil (trace quotient : Coset G)
    (hle : trace.log_size ≤ quotient.log_size) :
    build_periodic_lde_table G [] trace quotient = some PeriodicLdeTable.empty := by
  have c1 : ¬ Coset.size G quotient < Coset.size G trace := by
    rw [size_eq, size_eq]; exact not_lt.mpr (Nat.pow_le_pow_right (by norm_num) hle)
  have c2 : Coset.size G quotient % Coset.size G trace = 0 := by
    rw [size_eq, size_eq]; exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hle)
  simp [build_periodic_lde_table, c1, c2, PeriodicColumns.new, PeriodicColumns.max_period]
  rfl

end build

end Plonky3Lean.Proofs.Commit
