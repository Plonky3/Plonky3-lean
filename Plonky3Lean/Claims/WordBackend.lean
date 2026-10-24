module

public import Plonky3Lean.Proofs.WordBackend.Accept
public import Plonky3Lean.Proofs.WordBackend.Transpose
public import Plonky3Lean.Proofs.WordBackend.Code

@[expose] public section

/-!
# p3-word-backend: claims

What this repository asserts about the word proving backend, at the Plonky3 commit pinned in `plonky3/`.

The model is the set of transcriptions in `crates/word-backend/stub`.

The crate itself does not extract: its dependencies do not compile in the variant charon reads.

The scalar relations are those of p3-word, proven on its extraction.

The backend checks three things on bit columns:

- A zero relation vanishes on every bit.
- An AND relation multiplies two input bits into the output bit.
- A product relation compares two exponent lifts and the low bits.

The shift reduction reads committed words through the transpose of each shift.

The proofs rest on two facts:

- Every shift kind commutes with XOR.
- A challenge field passing the field check has a generator of order $2^n - 1$, with $n \ge 2w$.

A panic is a failed computation.
-/

open Finset Aeneas Aeneas.Std CoreModels p3_word Plonky3Lean.Proofs.Word Plonky3Lean.Proofs.WordBackend
open p3_word_backend.columns.mirror p3_word_backend.integer_mul.mirror
open p3_word_backend.shift.wiring.mirror p3_word_backend.keys.code.mirror

namespace Plonky3Lean.Claims.P3WordBackend

/-! ## The relation columns and the relation checks -/

/-- One operand read into a column is its scalar value.

It panics exactly when a term lies outside its segment. -/
theorem evaluate.eq {W : Type} [DecidableEq W] {inst : word.Word W} (M : Model inst)
    (pub wit : Slice W) (op : constraint.Operand W) (hv : OpValid M op) :
    evaluate inst M.xorf pub.val wit.val RustM.ok op =
      match opVal M pub wit op with
      | some v => RustM.ok v
      | none => RustM.fail .panic :=
  evaluate_eq M pub wit op hv

/-- The columns of a flat system are its scalar operand values.

- Every address lies in range.
- Both segments have their declared lengths.

Then the columns are built without panicking, and each entry is the scalar value of its operand. -/
theorem OperationColumns.new.flat {W : Type} [DecidableEq W] {inst : word.Word W} (M : Model inst)
    (sys : system.ConstraintSystem W) (pub wit : Slice W) (hv : SysValid M sys)
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len) (hin : validateSpec sys = .Ok ()) :
    OperationColumns.new inst M.xorf (.Flat sys) pub.val wit.val =
      RustM.ok (.ok (colsOf M sys pub wit)) :=
  columns_flat M sys pub wit hv hp hw hin

/-- On those columns, the word-level row checks accept exactly when the scalar verifier does. -/
theorem accepts.iff {W : Type} [DecidableEq W] {inst : word.Word W} (M : Model inst)
    (sys : system.ConstraintSystem W) (pub wit : Slice W)
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len) (hin : validateSpec sys = .Ok ()) :
    Accepts (· = M.zero) (fun l r o => M.andf l r = o) (fun a b lo hi => M.mulf a b = (lo, hi))
        (colsOf M sys pub wit) ↔
      verifySpec M sys pub wit = .Ok () :=
  accepts_iff M sys pub wit hp hw hin

/-- At 32 bits, the backend's bit-level checks accept exactly the statements the scalar verifier accepts.

- The columns are built without panicking.
- A zero relation is checked bit by bit.
- An AND relation is checked as a product of bits.
- A product relation is checked by the two lifts and the low bits.

The challenge field has $2^n$ elements, passes the field check, and its generator has order $2^n - 1$. -/
theorem backend.word32 {F : Type _} [Field F] {n : ℕ} (sys : system.ConstraintSystem word.Word32)
    (pub wit : Slice word.Word32) (hv : SysValid M32 sys)
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len) (hin : validateSpec sys = .Ok ())
    (g : F) (hg : orderOf g = 2 ^ n - 1) (hcheck : check_field (2 ^ n) 32 = .ok ()) :
    ∃ cols, OperationColumns.new I32w packedAdd32 (.Flat sys) pub.val wit.val = .ok (.ok cols) ∧
      (Accepts (fun v => ∀ i < 32, v.bv.getLsbD i = false)
          (fun l r o => ∀ i < 32, (l.bv.getLsbD i && r.bv.getLsbD i) = o.bv.getLsbD i)
          (fun a b lo hi => LiftOK g 32 a.val b.val lo.val hi.val) cols ↔
        verifySpec M32 sys pub wit = .Ok ()) :=
  backend32 sys pub wit hv hp hw hin g hg hcheck

/-- At 64 bits, the backend's bit-level checks accept exactly the statements the scalar verifier accepts.

The hypotheses are those of the 32-bit claim. -/
theorem backend.word64 {F : Type _} [Field F] {n : ℕ} (sys : system.ConstraintSystem word.Word64)
    (pub wit : Slice word.Word64) (hv : SysValid M64 sys)
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len) (hin : validateSpec sys = .Ok ())
    (g : F) (hg : orderOf g = 2 ^ n - 1) (hcheck : check_field (2 ^ n) 64 = .ok ()) :
    ∃ cols, OperationColumns.new I64w packedAdd64 (.Flat sys) pub.val wit.val = .ok (.ok cols) ∧
      (Accepts (fun v => ∀ i < 64, v.bv.getLsbD i = false)
          (fun l r o => ∀ i < 64, (l.bv.getLsbD i && r.bv.getLsbD i) = o.bv.getLsbD i)
          (fun a b lo hi => LiftOK g 64 a.val b.val lo.val hi.val) cols ↔
        verifySpec M64 sys pub wit = .Ok ()) :=
  backend64 sys pub wit hv hp hw hin g hg hcheck

/-! ## The exponent lift of a product -/

/-- One row of factor leaves multiplies to $g^{a b}$. -/
theorem factor_leaves.prod {F : Type _} [Field F] (g : F) {w a b : ℕ} (ha : a < 2 ^ w)
    (hb : b < 2 ^ w) :
    (factor_leaves [a] [b] w (generator_squarings g (2 * w))).prod = g ^ (a * b) := by
  rw [factor_row_prod g hb, Nat.mod_eq_of_lt ha, mul_comm]

/-- One row of result leaves multiplies to $g^{lo + 2^w hi}$. -/
theorem result_leaves.prod {F : Type _} [Field F] (g : F) {w lo hi : ℕ} (hl : lo < 2 ^ w)
    (hh : hi < 2 ^ w) :
    (result_leaves [lo] [hi] w (generator_squarings g (2 * w))).prod = g ^ (lo + 2 ^ w * hi) :=
  result_row_prod g hl hh

/-- The field check accepts a field of $2^n$ elements exactly when $n \ge 2w$. -/
theorem check_field.two_pow (n w : ℕ) : check_field (2 ^ n) w = .ok () ↔ 2 * w ≤ n :=
  check_field_two_pow n w

/-- One row of the product check accepts exactly the true full-width products.

The rows of leaves multiply to the same value and the low bits agree exactly when $a b = lo + 2^w hi$. -/
theorem row.sound {F : Type _} [Field F] {n w a b lo hi : ℕ} (g : F) (hg : orderOf g = 2 ^ n - 1)
    (hcheck : check_field (2 ^ n) w = .ok ()) (hw : 1 ≤ w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hl : lo < 2 ^ w) (hh : hi < 2 ^ w) :
    ((factor_leaves [a] [b] w (generator_squarings g (2 * w))).prod =
        (result_leaves [lo] [hi] w (generator_squarings g (2 * w))).prod ∧
      a % 2 * (b % 2) = lo % 2) ↔ a * b = lo + 2 ^ w * hi :=
  row_sound g hg hcheck hw ha hb hl hh

/-- Without the low bits, the two rows agree on a false product in exactly one case.

- The field has exactly $2^{2w}$ elements.
- The product is zero.
- Both limbs are all ones. -/
theorem row.collision {F : Type _} [Field F] {n w a b lo hi : ℕ} (g : F)
    (hg : orderOf g = 2 ^ n - 1) (hcheck : check_field (2 ^ n) w = .ok ()) (hw : 1 ≤ w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hl : lo < 2 ^ w) (hh : hi < 2 ^ w) :
    ((factor_leaves [a] [b] w (generator_squarings g (2 * w))).prod =
        (result_leaves [lo] [hi] w (generator_squarings g (2 * w))).prod ∧
      a * b ≠ lo + 2 ^ w * hi) ↔
      n = 2 * w ∧ a * b = 0 ∧ lo = 2 ^ w - 1 ∧ hi = 2 ^ w - 1 :=
  row_collision g hg hcheck hw ha hb hl hh

/-- The reduction exists exactly when the statement declares a product. -/
theorem IntegerMulReduction.new.none (r k : ℕ) : IntegerMulReduction.new r k = none ↔ r = 0 :=
  reduction_new_none r k

/-! ## The shift transpose -/

/-- Every 32-bit shift commutes with XOR. -/
theorem sem32.xor (k : shift.ShiftKind) (a : ℕ) (x y : BitVec 32) :
    sem32 k a (x ^^^ y) = sem32 k a x ^^^ sem32 k a y :=
  sem32_xor k a x y

/-- Every 64-bit shift, lane shifts included, commutes with XOR. -/
theorem sem64.xor (k : shift.ShiftKind) (a : ℕ) (x y : BitVec 64) :
    sem64 k a (x ^^^ y) = sem64 k a x ^^^ sem64 k a y :=
  sem64_xor k a x y

/-- For a 32-bit shift that does not panic, the transpose reads the shifted word.

Pairing the bits of a word with the transposed table gives the shifted word read at the point. -/
theorem shift_transpose.word32 {R : Type _} [CommRing R] [CharP R 2] (s : shift.Shift word.Word32)
    (hs : ¬ panics32 s.kind s.amount.val) (out : List R) (hout : out.length = 32) :
    ∃ T, shift_transpose I32w s out = RustM.ok T ∧
      ∀ x < 2 ^ 32, ev 32 x (wt T) = ev 32 (S32 s x) (wt out) :=
  ⟨_, shift_transpose32 s hs out hout, fun _ hx =>
    pair_transpose 32 (S32 s) (S32_xor s) (wt out) hx⟩

/-- For a 64-bit shift that does not panic, the transpose reads the shifted word. -/
theorem shift_transpose.word64 {R : Type _} [CommRing R] [CharP R 2] (s : shift.Shift word.Word64)
    (hs : ¬ panics64 s.kind s.amount.val) (out : List R) (hout : out.length = 64) :
    ∃ T, shift_transpose I64w s out = RustM.ok T ∧
      ∀ x < 2 ^ 64, ev 64 x (wt T) = ev 64 (S64 s x) (wt out) :=
  ⟨_, shift_transpose64 s hs out hout, fun _ hx =>
    pair_transpose 64 (S64 s) (S64_xor s) (wt out) hx⟩

/-- The two-slot transpose at 32 bits reads the word shifted by the inner slot, then the outer one. -/
theorem shift_weights.word32 {R : Type _} [CommRing R] [CharP R 2]
    (shifts : Array (shift.Shift word.Word32) 2#usize) {inner outer : shift.Shift word.Word32}
    (h : shifts.val = [inner, outer]) (hi : ¬ panics32 inner.kind inner.amount.val)
    (ho : ¬ panics32 outer.kind outer.amount.val) (out : List R) (hout : out.length = 32) :
    ∃ T, shift_weights I32w shifts out = RustM.ok T ∧
      ∀ x < 2 ^ 32, ev 32 x (wt T) = ev 32 (S32 outer (S32 inner x)) (wt out) :=
  ⟨_, shift_weights32 shifts h hi ho out hout, fun x hx =>
    pair_transpose 32 (S32 outer ∘ S32 inner)
      (fun x y => by simp [S32_xor]) (wt out) hx⟩

/-- The two-slot transpose at 64 bits reads the word shifted by the inner slot, then the outer one. -/
theorem shift_weights.word64 {R : Type _} [CommRing R] [CharP R 2]
    (shifts : Array (shift.Shift word.Word64) 2#usize) {inner outer : shift.Shift word.Word64}
    (h : shifts.val = [inner, outer]) (hi : ¬ panics64 inner.kind inner.amount.val)
    (ho : ¬ panics64 outer.kind outer.amount.val) (out : List R) (hout : out.length = 64) :
    ∃ T, shift_weights I64w shifts out = RustM.ok T ∧
      ∀ x < 2 ^ 64, ev 64 x (wt T) = ev 64 (S64 outer (S64 inner x)) (wt out) :=
  ⟨_, shift_weights64 shifts h hi ho out hout, fun x hx =>
    pair_transpose 64 (S64 outer ∘ S64 inner)
      (fun x y => by simp [S64_xor]) (wt out) hx⟩

/-! ## The key codes -/

/-- Every shift the 32-bit constructor builds is rebuilt from its own kind and amount. -/
theorem Shift.new.fixed32 {k : shift.ShiftKind} {amt : Std.Usize} {s : shift.Shift word.Word32}
    (h : shift.Shift.new I32w k amt = .ok (.Ok s)) : Fixed I32w s :=
  Plonky3Lean.Proofs.WordBackend.fixed32 h

/-- Every shift the 64-bit constructor builds is rebuilt from its own kind and amount. -/
theorem Shift.new.fixed64 {k : shift.ShiftKind} {amt : Std.Usize} {s : shift.Shift word.Word64}
    (h : shift.Shift.new I64w k amt = .ok (.Ok s)) : Fixed I64w s :=
  Plonky3Lean.Proofs.WordBackend.fixed64 h

/-- A key code decodes, without panicking, to its family and its two shifts. -/
theorem KeyCode.round_trip {W : Type} (inst : word.Word W) (op : system.ConstraintKind)
    (shifts : Array (shift.Shift W) 2#usize) {inner outer : shift.Shift W}
    (h : shifts.val = [inner, outer]) (hi : Fixed inst inner) (ho : Fixed inst outer) :
    ∃ c, KeyCode.new op shifts = .ok c ∧ KeyCode.operation c = .ok op ∧
      ShiftSequenceCode.shifts inst (KeyCode.sequence c) = .ok shifts :=
  key_code_round inst op shifts h hi ho

/-- Two keys with the same code have the same family and the same shifts. -/
theorem KeyCode.injective {W : Type} (inst : word.Word W) {op₁ op₂ : system.ConstraintKind}
    {s₁ s₂ : Array (shift.Shift W) 2#usize} {i₁ o₁ i₂ o₂ : shift.Shift W}
    (h₁ : s₁.val = [i₁, o₁]) (h₂ : s₂.val = [i₂, o₂])
    (hi₁ : Fixed inst i₁) (ho₁ : Fixed inst o₁) (hi₂ : Fixed inst i₂) (ho₂ : Fixed inst o₂)
    {c : ℕ} (e₁ : KeyCode.new op₁ s₁ = .ok c) (e₂ : KeyCode.new op₂ s₂ = .ok c) :
    op₁ = op₂ ∧ s₁ = s₂ := by
  obtain ⟨c₁, f₁, op1, sh1⟩ := key_code_round inst op₁ s₁ h₁ hi₁ ho₁
  obtain ⟨c₂, f₂, op2, sh2⟩ := key_code_round inst op₂ s₂ h₂ hi₂ ho₂
  have hc₁ : c₁ = c := by simpa [RustM.ok.injEq] using f₁.symm.trans e₁
  have hc₂ : c₂ = c := by simpa [RustM.ok.injEq] using f₂.symm.trans e₂
  subst hc₁ hc₂
  exact ⟨by simpa [RustM.ok.injEq] using op1.symm.trans op2,
    by simpa [RustM.ok.injEq] using sh1.symm.trans sh2⟩

end Plonky3Lean.Claims.P3WordBackend
