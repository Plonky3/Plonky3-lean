module

public import P3Sha256
public import Plonky3Lean.Proofs.Hash.Sha256.Compress

@[expose] public section

/-!
# p3-sha256: the 2-to-1 compression function

The two 32-byte halves are copied into one block, compressed from the initial hash value, and the
hash value is written out big-endian.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Sha256 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Sha256

theorem index_usize_eq' {α : Type} [Inhabited α] {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize)
    (h : i.val < v.val.length) : Std.Array.index_usize v i = .ok (v.val[i.val]!) := by
  rw [index_usize_eq _ _ h]
  exact congrArg _ (getElem!_pos v.val i.val h).symm

theorem update_eq' {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize) (x : α)
    (h : i.val < v.val.length) :
    Std.Array.update v i x = .ok (Std.Array.from (v.val.set i.val x) (by simp)) :=
  update_eq v i x h

/-! ## Copying the halves into a block -/

/-- The block after the first `k` rounds of the copy. -/
def blk (in₀ in₁ : List Std.U8) (k : ℕ) : Std.Array Std.U8 64#usize :=
  Std.Array.make 64#usize ((List.range 64).map fun j =>
    if j < 32 then (if j < k then in₀.getD j 0#u8 else 0#u8)
    else (if j - 32 < k then in₁.getD (j - 32) 0#u8 else 0#u8))
    (by simp only [List.length_map, List.length_range]; rfl)

theorem blk_val (in₀ in₁ : List Std.U8) (k : ℕ) : (blk in₀ in₁ k).val = (List.range 64).map
    fun j => if j < 32 then (if j < k then in₀.getD j 0#u8 else 0#u8)
      else (if j - 32 < k then in₁.getD (j - 32) 0#u8 else 0#u8) := by
  simp [blk]

theorem copy_body (input : Std.Array (Std.Array Std.U8 32#usize) 2#usize) (k : ℕ) (hk : k < 32) :
    p3_sha256.hax_reshaped.compress_loop0.body input { start := usz k, «end» := 32#usize }
      (blk (input.val[0]!).val (input.val[1]!).val k) =
      .ok (.cont ({ start := usz (k + 1), «end» := 32#usize },
        blk (input.val[0]!).val (input.val[1]!).val (k + 1))) := by
  obtain ⟨i', e, hi'⟩ := range_next_some (usz k) 32#usize
    (by rw [usz_val (by omega)]; exact hk)
  rw [show i' = usz (k + 1) from eq_usz (by omega) (by rw [hi', usz_val (by omega)])] at e
  unfold p3_sha256.hax_reshaped.compress_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, e, bind_ok,
    Aeneas.Std.uncurry_apply_pair]
  have l0 : (0#usize : Std.Usize) = usz 0 := ofNatCore_eq_usz _ _ (by norm_num)
  have l1 : (1#usize : Std.Usize) = usz 1 := ofNatCore_eq_usz _ _ (by norm_num)
  have hadd : (32#usize + usz k : RustM Std.Usize) = .ok (usz (32 + k)) := by
    rw [show (32#usize : Std.Usize) = usz 32 from ofNatCore_eq_usz _ _ (by norm_num)]
    exact usz_add (by omega)
  have hlen : ∀ a : Std.Array Std.U8 32#usize, a.val.length = 32 := fun a => by simp
  rw [l0, l1]
  rw [index_usize_eq' input (usz 0) (by rw [usz_val (by norm_num)]; simp), bind_ok,
    usz_val (by norm_num : 0 < 2 ^ 32),
    index_usize_eq' _ (usz k) (by rw [usz_val (by omega), hlen]; omega), bind_ok,
    update_eq' _ (usz k) _ (by rw [usz_val (by omega), blk_val]; simp; omega), bind_ok,
    index_usize_eq' input (usz 1) (by rw [usz_val (by norm_num)]; simp), bind_ok,
    usz_val (by norm_num : 1 < 2 ^ 32),
    index_usize_eq' _ (usz k) (by rw [usz_val (by omega), hlen]; omega), bind_ok,
    hadd, bind_ok,
    update_eq' _ (usz (32 + k)) _ (by rw [usz_val (by omega)]; simp; omega)]
  rw [bind_ok]
  apply congrArg RustM.ok
  apply congrArg ControlFlow.cont
  congr 1
  apply Std.Array.ext
  simp only [Std.Array.from_val, blk_val, usz_val (show k < 2 ^ 32 by omega),
    usz_val (show 32 + k < 2 ^ 32 by omega)]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have hj : j < 64 := by simpa using h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  have g : ∀ (a : Std.Array Std.U8 32#usize) (i : ℕ), i < 32 → a.val.getD i 0#u8 = a.val[i]! :=
    fun a i hi => by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi), getElem!_pos _ _ (by rw [hlen]; exact hi)]
  split_ifs <;> first | omega | rfl | (subst_vars; rw [g _ _ (by omega)])
  all_goals rw [show 32 + k - 32 = k by omega]

theorem copy_done (input : Std.Array (Std.Array Std.U8 32#usize) 2#usize) (b : Std.Array Std.U8 64#usize) :
    p3_sha256.hax_reshaped.compress_loop0.body input { start := usz 32, «end» := 32#usize } b =
      .ok (.done b) := by
  unfold p3_sha256.hax_reshaped.compress_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_next_none (usz 32) 32#usize (by rw [usz_val (by norm_num)]; exact le_rfl), bind_ok,
    Aeneas.Std.uncurry_apply_pair]

/-- The copy leaves the first half in bytes `0..32` and the second in `32..64`. -/
theorem copy_eq (input : Std.Array (Std.Array Std.U8 32#usize) 2#usize) :
    p3_sha256.hax_reshaped.compress_loop0 { start := 0#usize, «end» := 32#usize } input
      (blk (input.val[0]!).val (input.val[1]!).val 0) =
      .ok (blk (input.val[0]!).val (input.val[1]!).val 32) := by
  unfold p3_sha256.hax_reshaped.compress_loop0
  rw [show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by norm_num)]
  refine loop_of_steps (fun x => match x with
      | (iter1, block1) => p3_sha256.hax_reshaped.compress_loop0.body input iter1 block1)
    (fun k => (({ start := usz k, «end» := 32#usize } :
      CoreModels.core.ops.range.Range Std.Usize), blk (input.val[0]!).val (input.val[1]!).val k)) 32 _
    (fun k hk => copy_body input k hk) (copy_done input _)

/-! ## Writing the hash value out -/

/-- The output after its first `n` bytes are written from `B`. -/
def outArr (B : List Std.U8) (n : ℕ) : Std.Array Std.U8 32#usize :=
  Std.Array.make 32#usize ((List.range 32).map fun j => if j < n then B.getD j 0#u8 else 0#u8)
    (by simp only [List.length_map, List.length_range]; rfl)

theorem outArr_val (B : List Std.U8) (n : ℕ) :
    (outArr B n).val = (List.range 32).map fun j => if j < n then B.getD j 0#u8 else 0#u8 := by
  simp [outArr]

theorem write_body (B : List Std.U8) (i : ℕ) (hi : i < 8) (bytes : Std.Array Std.U8 4#usize)
    (hb : ∀ j < 4, bytes.val[j]! = B.getD (4 * i + j) 0#u8) (j : ℕ) (hj : j < 4) :
    p3_sha256.hax_reshaped.compress_loop1_loop0.body (usz i) bytes { start := usz j, «end» := usz 4 }
      (outArr B (4 * i + j)) =
      .ok (.cont ({ start := usz (j + 1), «end» := usz 4 }, outArr B (4 * i + (j + 1)))) := by
  obtain ⟨i', e, hi'⟩ := range_next_some (usz j) (usz 4)
    (by rw [usz_val (by omega), usz_val (by omega)]; omega)
  rw [show i' = usz (j + 1) from eq_usz (by omega) (by rw [hi', usz_val (by omega)])] at e
  unfold p3_sha256.hax_reshaped.compress_loop1_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, e, bind_ok,
    Aeneas.Std.uncurry_apply_pair]
  have hmul : (4#usize * usz i : RustM Std.Usize) = .ok (usz (4 * i)) := by
    rw [show (4#usize : Std.Usize) = usz 4 from ofNatCore_eq_usz _ _ (by norm_num)]
    exact usz_mul (by omega) (by omega) (by omega)
  rw [index_usize_eq' _ (usz j) (by rw [usz_val (by omega)]; simp; omega), bind_ok, hmul, bind_ok,
    usz_add (by omega), bind_ok,
    update_eq' _ (usz (4 * i + j)) _ (by rw [usz_val (by omega), outArr_val]; simp; omega),
    bind_ok, usz_val (show j < 2 ^ 32 by omega), hb j hj]
  apply congrArg RustM.ok
  apply congrArg ControlFlow.cont
  congr 1
  apply Std.Array.ext
  simp only [Std.Array.from_val, outArr_val, usz_val (show 4 * i + j < 2 ^ 32 by omega)]
  apply List.ext_getElem (by simp)
  intro m h1 h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  split_ifs <;> first | omega | rfl | (subst_vars; rfl)

theorem write_done (i : Std.Usize) (bytes : Std.Array Std.U8 4#usize) (o : Std.Array Std.U8 32#usize) :
    p3_sha256.hax_reshaped.compress_loop1_loop0.body i bytes { start := usz 4, «end» := usz 4 } o =
      .ok (.done o) := by
  unfold p3_sha256.hax_reshaped.compress_loop1_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_next_none (usz 4) (usz 4) le_rfl, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem write_word (B : List Std.U8) (i : ℕ) (hi : i < 8) (bytes : Std.Array Std.U8 4#usize)
    (hb : ∀ j < 4, bytes.val[j]! = B.getD (4 * i + j) 0#u8) :
    p3_sha256.hax_reshaped.compress_loop1_loop0 { start := 0#usize, «end» := 4#usize }
      (outArr B (4 * i)) (usz i) bytes = .ok (outArr B (4 * (i + 1))) := by
  unfold p3_sha256.hax_reshaped.compress_loop1_loop0
  rw [show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by norm_num),
    show (4#usize : Std.Usize) = usz 4 from ofNatCore_eq_usz _ _ (by norm_num)]
  refine loop_of_steps _ (fun j => (({ start := usz j, «end» := usz 4 } :
      CoreModels.core.ops.range.Range Std.Usize), outArr B (4 * i + j))) 4 _
    (fun j hj => write_body B i hi bytes hb j hj) (write_done (usz i) bytes _)

/-- The big-endian bytes of a list of words, as Rust bytes. -/
def outBytes (W : List Word) : List Std.U8 := (bytesOfWords W).map fun b => ⟨b⟩

theorem outBytes_getD (W : List Word) (hW : W.length = 8) (i j : ℕ) (hi : i < 8) (hj : j < 4) :
    (outBytes W).getD (4 * i + j) 0#u8 = ⟨(bytesOfWord (W.getD i 0)).getD j 0⟩ := by
  match W, hW with
  | [w₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇], _ =>
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem out_body (W : List Word) (hW : W.length = 8) (k : ℕ) (hk : k < 8) :
    p3_sha256.hax_reshaped.compress_loop1.body (toArray8 W) { start := usz k, «end» := 8#usize }
      (outArr (outBytes W) (4 * k)) =
      .ok (.cont ({ start := usz (k + 1), «end» := 8#usize }, outArr (outBytes W) (4 * (k + 1)))) := by
  obtain ⟨i', e, hi'⟩ := range_next_some (usz k) 8#usize (by rw [usz_val (by omega)]; exact hk)
  rw [show i' = usz (k + 1) from eq_usz (by omega) (by rw [hi', usz_val (by omega)])] at e
  unfold p3_sha256.hax_reshaped.compress_loop1.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, e, bind_ok,
    Aeneas.Std.uncurry_apply_pair]
  rw [index_usize_eq' _ (usz k) (by rw [usz_val (by omega)]; simp [toArray8]; omega), bind_ok,
    CoreModels.core.num.U32.to_be_bytes, CoreModels.rust_primitives.arithmetic.to_be_bytes_u32,
    bind_ok, write_word _ k hk _ ?_, bind_ok]
  intro j hj
  rw [outBytes_getD W hW k j hk hj]
  have hx : (toArray8 W).val[(usz k).val]! = ⟨W.getD k 0⟩ := by
    rw [usz_val (by omega)]
    simp only [toArray8, Std.Array.make_val, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    rw [List.getElem_map, List.getElem_take, List.getElem_append_left (by omega)]
  simp only [hx, Aeneas.Std.core.num.U32.to_be_bytes, Std.Array.from_val, u32_bv_mk, toBEBytes_word,
    bytesOfWord]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem out_done (st : Std.Array Std.U32 8#usize) (o : Std.Array Std.U8 32#usize) :
    p3_sha256.hax_reshaped.compress_loop1.body st { start := usz 8, «end» := 8#usize } o =
      .ok (.done o) := by
  unfold p3_sha256.hax_reshaped.compress_loop1.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_next_none (usz 8) 8#usize (by rw [usz_val (by norm_num)]; exact le_rfl), bind_ok,
    Aeneas.Std.uncurry_apply_pair]

theorem out_eq (W : List Word) (hW : W.length = 8) :
    p3_sha256.hax_reshaped.compress_loop1 { start := 0#usize, «end» := 8#usize } (toArray8 W)
      (outArr (outBytes W) 0) = .ok (outArr (outBytes W) 32) := by
  unfold p3_sha256.hax_reshaped.compress_loop1
  rw [show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by norm_num)]
  refine loop_of_steps (fun x => match x with
      | (iter1, output1) => p3_sha256.hax_reshaped.compress_loop1.body (toArray8 W) iter1 output1)
    (fun k => (({ start := usz k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize),
      outArr (outBytes W) (4 * k))) 8 _ (fun k hk => out_body W hW k hk) (out_done _ _)

/-- p3-sha256's initial hash value is FIPS 180-4's. -/
theorem H256_256_eq : p3_sha256.H256_256 = toArray8 H0 := by
  unfold p3_sha256.H256_256
  apply Std.Array.ext
  decide +kernel

/-- The reshaped compression: FIPS 180-4's compression of the two halves from `H^(0)`, written
out big-endian. -/
theorem reshaped_compress_eq (input : Std.Array (Std.Array Std.U8 32#usize) 2#usize) :
    p3_sha256.hax_reshaped.compress input = .ok (outArr (outBytes (compress H0
      (wordsOfBytes ((blk (input.val[0]!).val (input.val[1]!).val 32).val.map UScalar.bv)))) 32) := by
  unfold p3_sha256.hax_reshaped.compress
  have hz64 : CoreModels.core.array.repeat 64#usize CoreModels.core.U8.Insts.CoreCloneClone 0#u8 =
      .ok (blk (input.val[0]!).val (input.val[1]!).val 0) := by
    rw [repeat_eq _ _ _ (fun _ => rfl) (by decide)]
    congr 1
  have hz32 : CoreModels.core.array.repeat 32#usize CoreModels.core.U8.Insts.CoreCloneClone 0#u8 =
      .ok (outArr (outBytes (compressBlocks H0
        [blk (input.val[0]!).val (input.val[1]!).val 32])) 0) := by
    rw [repeat_eq _ _ _ (fun _ => rfl) (by decide)]
    congr 1
  rw [hz64, bind_ok, copy_eq, bind_ok]
  simp only [CoreModels.core.array.Array.as_slice, CoreModels.rust_primitives.slice.array_as_slice,
    bind_ok, H256_256_eq]
  rw [compress256_eq _ (by rfl), bind_ok, hz32, bind_ok]
  exact out_eq _ (length_compressBlocks _ (by rfl) _)

theorem blk_full (in₀ in₁ : Std.Array Std.U8 32#usize) :
    (blk in₀.val in₁.val 32).val = in₀.val ++ in₁.val := by
  rw [blk_val]
  have h0 : in₀.val.length = 32 := by simp
  have h1 : in₁.val.length = 32 := by simp
  apply List.ext_getElem (by simp [h0, h1])
  intro j hj1 hj2
  simp only [List.getElem_map, List.getElem_range]
  split_ifs with h
  · rw [List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
  · rw [List.getElem_append_right (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp only [h0]
  · simp at hj1; omega

theorem outArr_full (B : List Std.U8) (hB : B.length = 32) : (outArr B 32).val = B := by
  rw [outArr_val]
  apply List.ext_getElem (by simp [hB])
  intro j hj1 hj2
  simp only [List.getElem_map, List.getElem_range]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by simpa using hj1)), List.getD_eq_getElem _ _ hj2]

/-- `Sha256Compress::compress`: FIPS 180-4's compression of the two halves, in order, from the
initial hash value, written out big-endian. -/
theorem compress_spec (self : p3_sha256.Sha256Compress)
    (input : Std.Array (Std.Array Std.U8 32#usize) 2#usize) :
    p3_sha256.Sha256Compress.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayU8322.compress
      self input ⦃ out => out.val.map UScalar.bv = bytesOfWords (compress H0
        (wordsOfBytes (((input.val[0]!).val ++ (input.val[1]!).val).map UScalar.bv))) ⦄ := by
  unfold p3_sha256.Sha256Compress.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayU8322.compress
  rw [reshaped_compress_eq, WP.spec_ok, outArr_full _ (by
    simp [outBytes, bytesOfWords, bytesOfWord, length_compress _ _ (show H0.length = 8 from rfl)]),
    blk_full]
  simp [outBytes]

end Plonky3Lean.Proofs.Sha256
