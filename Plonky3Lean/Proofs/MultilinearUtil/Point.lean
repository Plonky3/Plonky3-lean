module

public import Plonky3Lean.Proofs.MultilinearUtil.Model
public import Plonky3Lean.Proofs.MultilinearUtil.Unique
public import P3MultilinearUtil.Point

@[expose] public section

/-!
# Points: the equality tables and the closed forms

The doubling builds the table of the coordinates entered so far, the latest one on the top bit.

So the most-significant-bit order yields the table of the point, and the other order the table of its reverse.

Every thread split yields the same table, because the table of r ++ s is the outer product of the two tables.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.point.mirror

variable {F : Type _} [Field F]

/-! ## The doubling -/

theorem split_by_coordinate_eq (W : ℕ) (low : List F) (c : F) :
    split_by_coordinate W low c = (low.map fun l => l - l * c, low.map (· * c)) := by
  simp only [split_by_coordinate, List.map_map]
  congr 1
  · exact map_pack_slice_with_suffix W (fun l => l - l * c) (by simp) low
  · exact map_pack_slice_with_suffix W (· * c) (by simp) low

/-- The point a bit order reads: the point itself, or its reverse. -/
def ordered (p : List F) : BitOrder → List F
  | .Msb => p
  | .Lsb => p.reverse

/-- The coordinates entered after k steps, the latest first. -/
def entered (p : List F) (k : ℕ) : BitOrder → List F
  | .Msb => p.drop (p.length - k)
  | .Lsb => (p.take k).reverse

omit [Field F] in
theorem length_entered (p : List F) {k : ℕ} (hk : k ≤ p.length) (o : BitOrder) :
    (entered p k o).length = k := by
  cases o <;> simp [entered] <;> omega

theorem entered_succ (p : List F) {k : ℕ} (hk : k < p.length) (o : BitOrder) :
    entered p (k + 1) o = entering p o k :: entered p k o := by
  cases o
  · simp only [entered, entering, List.getD_eq_getElem?_getD]
    rw [show p.length - (k + 1) = p.length - 1 - k by omega,
      List.drop_eq_getElem_cons (by omega), List.getElem?_eq_getElem (by omega)]
    simp [show p.length - 1 - k + 1 = p.length - k by omega]
  · simp only [entered, entering, List.take_add_one, List.getElem?_eq_getElem hk,
      List.reverse_append, Option.toList_some, List.getD_eq_getElem?_getD, Option.getD_some]
    rfl

omit [Field F] in
theorem entered_full (p : List F) (o : BitOrder) : entered p p.length o = ordered p o := by
  cases o <;> simp [entered, ordered]

/-- The table of r, scaled by s. -/
abbrev sTable (s : F) (r : List F) : List F := (eqTable r).map (s * ·)

theorem sTable_cons (s c : F) (r : List F) :
    sTable s (c :: r) = (sTable s r).map (fun l => l - l * c) ++ (sTable s r).map (· * c) := by
  simp only [sTable, eqTable_cons, List.map_append, List.map_map]
  congr 1 <;> exact List.map_congr_left fun _ _ => by simp only [Function.comp]; ring

/-- One step of the doubling enters a coordinate on the top bit. -/
theorem doubling_step {W : ℕ} (s c : F) (r rest : List F) :
    (match split_by_coordinate W ((sTable s r ++ rest).take (2 ^ r.length)) c with
      | (low, high) => low ++ high ++ (sTable s r ++ rest).drop (2 ^ (r.length + 1))) =
      sTable s (c :: r) ++ rest.drop (2 ^ r.length) := by
  have hl : (sTable s r).length = 2 ^ r.length := by simp
  simp only [split_by_coordinate_eq, List.take_left' hl, sTable_cons, pow_succ, mul_two,
    List.drop_append, hl, Nat.add_sub_cancel_left]
  rw [List.drop_eq_nil_of_le (by omega), List.nil_append]

theorem fill_serial_loop (W : ℕ) (p : List F) (o : BitOrder) (s : F) (rest : List F)
    {k : ℕ} (hk : k ≤ p.length) :
    (List.range k).foldl (fun out k =>
      let (low, high) := split_by_coordinate W (out.take (2 ^ k)) (entering p o k)
      low ++ high ++ out.drop (2 ^ (k + 1))) (s :: rest) =
      sTable s (entered p k o) ++ rest.drop (2 ^ k - 1) := by
  induction k with
  | zero => cases o <;> simp [entered, sTable]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
    have hlen := length_entered p (show k ≤ p.length by omega) o
    have h := doubling_step (W := W) s (entering p o k) (entered p k o) (rest.drop (2 ^ k - 1))
    rw [hlen] at h
    rw [h, entered_succ p (by omega), List.drop_drop]
    congr 2
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]; omega

/-- The serial fill is the scaled table of the point the bit order reads. -/
theorem fill_equality_table_serial_eq (W : ℕ) (p out : List F) (o : BitOrder) (s : F)
    (h : out.length = 2 ^ p.length) :
    Point.fill_equality_table_serial W p out o s = some (sTable s (ordered p o)) := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, out = a :: rest :=
    List.exists_cons_of_ne_nil (by
      intro h'; have := Nat.one_le_two_pow (n := p.length); simp [h'] at h; omega)
  simp only [Point.fill_equality_table_serial, h, ne_eq, not_true_eq_false, ite_false,
    List.set_cons_zero]
  simp only [List.length_cons] at h
  rw [fill_serial_loop W p o s rest le_rfl, entered_full,
    List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem sTable_append (s : F) (r t : List F) :
    sTable s (r ++ t) = (sTable s r).flatMap fun a => sTable a t := by
  simp only [sTable, eqTable_append, List.map_flatMap, List.flatMap_map, List.map_map]
  exact List.flatMap_congr fun _ _ => List.map_congr_left fun _ _ => by
    simp only [Function.comp]; ring

/-- Every split of the variables into seeds and chunks yields the scaled table. -/
theorem fill_equality_table_in_chunks_eq (W : ℕ) (p out : List F) (o : BitOrder) (s : F)
    {lv : ℕ} (hlv : lv ≤ p.length) (h : out.length = 2 ^ p.length) :
    Point.fill_equality_table_in_chunks W p out o s lv = some (sTable s (ordered p o)) := by
  simp only [Point.fill_equality_table_in_chunks, show ¬ p.length < lv by omega, ite_false]
  split
  · exact fill_equality_table_serial_eq W p out o s h
  · rename_i hh
    set hv := p.length - lv
    obtain ⟨high, low, hsplit, hlh, hll⟩ : ∃ high low : List F,
        high_low p o lv = (high, low) ∧ high.length = hv ∧ low.length = lv ∧
        ordered high o ++ ordered low o = ordered p o := by
      cases o
      · exact ⟨_, _, rfl, by simp [hv], by simp; omega, by simp [ordered]⟩
      · exact ⟨_, _, rfl, by simp [hv], by simp; omega, by
          simp [ordered, ← List.reverse_append]⟩
    obtain ⟨hll, hord⟩ := hll
    rw [hsplit]
    simp only
    have hn : 2 ^ p.length = 2 ^ hv * 2 ^ lv := by rw [← pow_add]; congr 1; omega
    rw [fill_equality_table_serial_eq W high _ o s (by simp [hlh])]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [mapM_some _ _ (fun cs : List F × F => sTable cs.2 (ordered low o)) fun cs hcs => by
      rw [fill_equality_table_serial_eq W low _ o _ (by
        rw [hll]; exact length_of_mem_chunks (by positivity) (h.trans hn) (List.of_mem_zip hcs).1)]]
    have hlen : (sTable s (ordered high o)).length = 2 ^ hv := by
      cases o <;> simp [ordered, hlh]
    have hz : ((chunks (2 ^ lv) out).zip (sTable s (ordered high o))).map
        (fun cs : List F × F => sTable cs.2 (ordered low o)) =
        (sTable s (ordered high o)).map fun a => sTable a (ordered low o) := by
      conv_rhs => rw [← List.map_snd_zip (l₁ := chunks (2 ^ lv) out)
        (l₂ := sTable s (ordered high o)) (by rw [length_chunks (by positivity) (h.trans hn), hlen])]
      rw [List.map_map]; rfl
    rw [hz, hlen, ← hn, ← h, List.drop_length]
    simp only [Option.bind_some, List.append_nil]
    rw [← List.flatMap_def, ← sTable_append, hord]
    rfl

theorem sTable_one (r : List F) : sTable 1 r = eqTable r := by simp [sTable]

/-- The equality table under a bit order, for every packing width and every task length. -/
theorem equality_table_eq (W task_len : ℕ) (p : List F) (o : BitOrder) (h : p.length < 64) :
    Point.equality_table W task_len p o = some (eqTable (ordered p o)) := by
  simp only [Point.equality_table, h, ↓reduceIte]
  rw [Point.fill_equality_table,
    fill_equality_table_in_chunks_eq _ _ _ _ _ (min_le_right _ _) (by simp), sTable_one]

theorem equality_table_panics (W task_len : ℕ) (p : List F) (o : BitOrder) (h : 64 ≤ p.length) :
    Point.equality_table W task_len p o = none := by
  simp [Point.equality_table, show ¬ p.length < 64 by omega]

end Plonky3Lean.Proofs.MultilinearUtil
