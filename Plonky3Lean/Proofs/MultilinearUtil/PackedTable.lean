module

public import Plonky3Lean.Proofs.MultilinearUtil.Eval

@[expose] public section

/-!
# The packed equality table

The last log_2 W variables fill the lanes: lane l of packed entry j is scale eq(j W + l, point).

So unpacking the table gives the scalar table, in index order.

Every entry of the buffers is written before it is read, so the uninitialised memory is never observed.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.poly.mirror
open Finset

variable {K A : Type _} [Field K] [CommRing A] [Algebra K A]

/-- The table of r scaled by s, in an algebra. -/
def aTable (s : A) (r : List K) : List A := (eqTable r).map fun t => s * algebraMap K A t

@[simp] theorem length_aTable (s : A) (r : List K) : (aTable s r).length = 2 ^ r.length := by
  simp [aTable]

theorem aTable_cons (s : A) (c : K) (r : List K) :
    aTable s (c :: r) = (aTable s r).map (fun x => x - x * algebraMap K A c) ++
      (aTable s r).map (· * algebraMap K A c) := by
  simp only [aTable, eqTable_cons, List.map_append, List.map_map]
  congr 1 <;> refine List.map_congr_left fun _ _ => ?_ <;> simp only [Function.comp, map_mul,
    map_sub, map_one] <;> ring

theorem zip_step (lo hi : List A) (c : A) (h : lo.length ≤ hi.length) :
    (lo.zip hi).map (fun p => p.1 * c) = lo.map (· * c) := by
  rw [show (fun p : A × A => p.1 * c) = (· * c) ∘ Prod.fst from rfl, ← List.map_map,
    List.map_fst_zip h]

theorem zip_map_self (lo : List A) (g : A → A) :
    (lo.zip (lo.map g)).map (fun q => q.1 - q.2) = lo.map (fun x => x - g x) := by
  induction lo with
  | nil => simp
  | cons a lo ih => simp [ih]

theorem eq_serial_loop (s : A) : ∀ (L S : List K) (junk : List A),
    2 ^ (S.length + L.length) ≤ 2 ^ S.length + junk.length →
    (L.zipIdx S.length).foldl (fun out vi =>
      let lo := out.take (2 ^ vi.2)
      let hi := out.drop (2 ^ vi.2)
      let hi' := (lo.zip hi).map fun p => p.1 * algebraMap K A vi.1
      let lo' := (lo.zip hi').map fun q => q.1 - q.2
      lo' ++ (hi' ++ hi.drop (2 ^ vi.2))) (aTable s S ++ junk) =
      aTable s (L.reverse ++ S) ++ junk.drop (2 ^ (S.length + L.length) - 2 ^ S.length)
  | [], S, junk, _ => by simp
  | c :: L, S, junk, hj => by
    have hmono : 2 ^ (S.length + 1) ≤ 2 ^ (S.length + (L.length + 1)) :=
      Nat.pow_le_pow_right two_pos (by omega)
    have hp : 2 ^ (S.length + 1) = 2 ^ S.length + 2 ^ S.length := by rw [pow_succ]; omega
    simp only [List.length_cons] at hj
    have hl : (aTable s S).length = 2 ^ S.length := by simp
    rw [List.zipIdx_cons, List.foldl_cons]
    simp only [List.take_left' hl, List.drop_left' hl]
    rw [zip_step (aTable s S) junk (algebraMap K A c) (by rw [hl]; omega), zip_map_self]
    have := eq_serial_loop s L (c :: S) (junk.drop (2 ^ S.length))
      (by simp only [List.length_cons, List.length_drop]
          rw [show S.length + 1 + L.length = S.length + (L.length + 1) by omega]; omega)
    simp only [List.length_cons] at this
    rw [← List.append_assoc, ← aTable_cons, this, List.drop_drop, List.reverse_cons,
      List.append_assoc, List.singleton_append,
      show S.length + 1 + L.length = S.length + (L.length + 1) by omega]
    congr 2
    generalize 2 ^ (S.length + (L.length + 1)) = X at hmono ⊢
    generalize 2 ^ (S.length + 1) = Y at hmono hp ⊢
    omega

/-- eq_serial: the scaled table, for every initial content of the buffer. -/
theorem eq_serial_eq (out : List A) (p : List K) (s : A) (h : out.length = 2 ^ p.length) :
    eq_serial out p s = some (aTable s p) := by
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, out = a :: rest :=
    List.exists_cons_of_ne_nil (by intro h'; have := Nat.one_le_two_pow (n := p.length); simp [h'] at h; omega)
  have hl := eq_serial_loop s p.reverse [] rest (by simp at h ⊢; omega)
  simp only [List.length_nil, List.length_reverse, Nat.zero_add, List.reverse_reverse,
    List.append_nil, pow_zero] at hl
  have h0 : aTable s ([] : List K) = [s] := by simp [aTable]
  rw [h0, List.singleton_append] at hl
  have hr : rest.length = 2 ^ p.length - 1 := by simp at h; omega
  simp only [eq_serial, h, ne_eq, not_true_eq_false, ↓reduceIte, List.set_cons_zero, hl,
    Option.some.injEq]
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem eq_serial_panics (out : List A) (p : List K) (s : A) (h : out.length ≠ 2 ^ p.length) :
    eq_serial out p s = none := by simp [eq_serial, h]

theorem aTable_append (s : A) (r t : List K) :
    aTable s (r ++ t) = (aTable s r).flatMap fun a => aTable a t := by
  simp only [aTable, eqTable_append, List.map_flatMap, List.flatMap_map, List.map_map]
  exact List.flatMap_congr fun _ _ => List.map_congr_left fun _ _ => by
    simp only [Function.comp, map_mul]; ring

section NewPacked

variable {EF : Type _} [Field EF] [DecidableEq EF]

/-- The seed: lane l is scale eq(l, last log_2 W coordinates). -/
def packedSeed (w : ℕ) (point : List EF) (s : EF) : Fin (2 ^ w) → EF :=
  fun l => (aTable s (point.drop (point.length - w))).getD l 0

theorem new_packed_from_point_eq_aTable (w T : ℕ) (point : List EF) (s : EF) (hs : s ≠ 0)
    (hw : w ≤ point.length) :
    Poly.new_packed_from_point w T point s =
      some (aTable (packedSeed w point s) (point.take (point.length - w))) := by
  have hinit := eq_serial_eq (List.replicate (2 ^ w) 0) (point.drop (point.length - w)) s
    (by simp; omega)
  simp only [Poly.new_packed_from_point, hs, ↓reduceIte, show ¬ point.length < w by omega,
    hinit, Option.bind_eq_bind, Option.bind_some, from_ext_slice, length_aTable,
    List.length_drop, show point.length - (point.length - w) = w by omega]
  split
  · rw [eq_serial_eq _ _ _ (by simp)]; rfl
  · rename_i hbig
    set rest := point.take (point.length - w) with hrest
    set lc := Nat.clog 2 T
    have hlc : (rest.take lc).length = lc := by simp; omega
    rw [eq_serial_eq _ _ _ (by simp [hlc]), Option.bind_some]
    have hsplit : rest = rest.take lc ++ rest.drop lc := (List.take_append_drop _ _).symm
    have hn : (rest.take lc).length + (rest.drop lc).length = rest.length := by simp; omega
    have hlen : (List.replicate (2 ^ rest.length) (0 : Fin (2 ^ w) → EF)).length =
        2 ^ (rest.take lc).length * 2 ^ (rest.drop lc).length := by
      rw [List.length_replicate, ← pow_add, hn]
    rw [show rest.length - lc = (rest.drop lc).length by simp,
      chunks_eq (by positivity) (show _ = 2 ^ (rest.take lc).length * 2 ^ (rest.drop lc).length
      from hlen)]
    rw [mapM_some _ _ (fun cs => aTable cs.2 (rest.drop lc)) fun cs hcs => by
      obtain ⟨t, ht, ht'⟩ := List.mem_map.mp (List.of_mem_zip hcs).1
      simp only [List.mem_range] at ht
      rw [eq_serial_eq _ _ _ (by rw [← ht', length_chunkAt hlen ht])]]
    simp only [Option.pure_def, Option.bind_some, Option.some.injEq]
    rw [show (fun cs : List (Fin (2 ^ w) → EF) × (Fin (2 ^ w) → EF) => aTable cs.2 (rest.drop lc)) =
      (fun a => aTable a (rest.drop lc)) ∘ Prod.snd from rfl, ← List.map_map,
      List.map_snd_zip (by simp [hlc])]
    conv_rhs => rw [hsplit, aTable_append]
    rw [List.flatMap_def]
    rfl

omit [DecidableEq EF] in
theorem getD_map_ringHom_mul {B : Type _} [CommRing B] (φ : EF →+* B) (c : B) (l : List EF) {j : ℕ}
    (hj : j < l.length) : (l.map fun t => c * φ t).getD j 0 = c * φ (l.getD j 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

omit [Field EF] [DecidableEq EF] in
theorem length_to_ext_iter {W : ℕ} (v : List (Fin W → EF)) : (to_ext_iter v).length = v.length * W := by
  induction v with
  | nil => simp [to_ext_iter]
  | cons a v ih => rw [to_ext_iter_cons, List.length_append, ih, List.length_ofFn]; simp; ring

omit [DecidableEq EF] in
theorem getD_eqTable_append' (r t : List EF) {w a b : ℕ} (ht : t.length = w)
    (ha : a < 2 ^ r.length) (hb : b < 2 ^ w) :
    (eqTable (r ++ t)).getD (a * 2 ^ w + b) 0 = (eqTable r).getD a 0 * (eqTable t).getD b 0 := by
  subst ht; exact getD_eqTable_append r t ha hb

omit [DecidableEq EF] in
theorem getD_to_ext_iter {W : ℕ} (v : List (Fin W → EF)) {j l : ℕ} (hj : j < v.length) (hl : l < W) :
    (to_ext_iter v).getD (j * W + l) 0 = v.getD j 0 ⟨l, hl⟩ := by
  rw [to_ext_iter, getD_flatMap_const _ _ (fun _ _ => List.length_ofFn) _ hj hl]
  simp [List.getD_eq_getElem?_getD, hl, List.getElem?_eq_getElem hj]

omit [DecidableEq EF] in
/-- Unpacking the packed table gives the scalar table: the lanes are the last log_2 W variables. -/
theorem unpack_new_packed (w : ℕ) (point : List EF) (s : EF) (hw : w ≤ point.length) :
    to_ext_iter (aTable (packedSeed w point s) (point.take (point.length - w))) = sTable s point := by
  have hlen : (aTable (packedSeed w point s) (point.take (point.length - w))).length =
      2 ^ (point.length - w) := by simp
  have htot : (to_ext_iter (aTable (packedSeed w point s) (point.take (point.length - w)))).length =
      2 ^ point.length := by
    rw [length_to_ext_iter, hlen, ← pow_add]; congr 1; omega
  refine ext_getD 0 (by rw [htot]; simp) fun x hx => ?_
  rw [htot] at hx
  have hW : 0 < 2 ^ w := by positivity
  have hj : x / 2 ^ w < 2 ^ (point.length - w) := by
    rw [Nat.div_lt_iff_lt_mul hW, ← pow_add, show point.length - w + w = point.length by omega]
    exact hx
  rw [← Nat.div_add_mod x (2 ^ w), Nat.mul_comm, getD_to_ext_iter _ (by rw [hlen]; exact hj)
    (Nat.mod_lt _ hW)]
  conv_rhs => rw [← List.take_append_drop (point.length - w) point]
  simp only [sTable]
  rw [getD_map_mul, getD_eqTable_append' _ _ (by simp; omega) (by simpa using hj)
    (Nat.mod_lt x hW)]
  rw [aTable, getD_map_ringHom_mul _ _ _ (by simpa using hj)]
  simp only [Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    packedSeed, aTable]
  rw [getD_map_mul]
  ring

end NewPacked

end Plonky3Lean.Proofs.MultilinearUtil
