/-
Transcriptions of statement.rs and columns.rs: the two statement forms and the relation columns.

A packed word holds the bits of its word in the same order, so a column holds words.

Adding two packed words XORs their bits, lane by lane.

A failed expectation panics.
-/
module

public import P3Word

@[expose] public section

namespace p3_word_backend.columns.mirror

open Aeneas Aeneas.Std p3_word

variable {W : Type}

/-- The items of a vector, as a list. -/
abbrev vlist {T : Type} (v : CoreModels.alloc.vec.Vec T) : List T := Slice.val v

/-- A usize built from a natural number, keeping its low bits. -/
def usz (x : ℕ) : Std.Usize := ⟨BitVec.ofNat _ x⟩

/-- The relations a key proves: one flat system, or a composition of gadgets. -/
inductive Statement (W : Type) where
  | Flat (system : system.ConstraintSystem W)
  | Composed (composition : component.Composition W)

/-- The number of verifier-known words. -/
def Statement.public_len : Statement W → ℕ
  | .Flat s => s.public_len.val
  | .Composed c => c.public_len.val

/-- The number of committed words. -/
def Statement.witness_len : Statement W → ℕ
  | .Flat s => s.witness_len.val
  | .Composed c => c.witness_len.val

/-- The shape check: the public segment first, then the committed one.

An error names the segment, the expected length and the actual length. -/
def check_shape (st : Statement W) (public_len witness_len : ℕ) :
    Except (index.Segment × ℕ × ℕ) Unit :=
  if public_len ≠ st.public_len then .error (.Public, st.public_len, public_len)
  else if witness_len ≠ st.witness_len then .error (.Witness, st.witness_len, witness_len)
  else .ok ()

/-- Adding two packed 32-bit words, read back as a word. -/
def packedAdd32 (a b : word.Word32) : word.Word32 := ⟨a.bv ^^^ b.bv⟩

/-- Adding two packed 64-bit words, read back as a word. -/
def packedAdd64 (a b : word.Word64) : word.Word64 := ⟨a.bv ^^^ b.bv⟩

/-- The relation columns, in the Rust arrays' index order. -/
structure OperationColumns (W : Type) where
  zero : List W
  and_left : List W
  and_right : List W
  and_output : List W
  mul_left : List W
  mul_right : List W
  mul_low : List W
  mul_high : List W

/-- The columns before any relation is read. -/
def OperationColumns.empty : OperationColumns W := ⟨[], [], [], [], [], [], [], []⟩

/-- The word at a checked index, if its position lies inside its segment. -/
def get (pub wit : List W) (i : index.ValueIndex) : Option W :=
  match i.segment with
  | .Public => pub[i.position.val]?
  | .Witness => wit[i.position.val]?

/-- One term of an operand: readdress it, read its word, shift it and add it in. -/
def readTerm (inst : word.Word W) (add : W → W → W) (pub wit : List W)
    (remap : index.ValueIndex → RustM index.ValueIndex) (acc : W) (t : shift.ShiftedValue W) :
    RustM W := do
  let i ← remap t.index
  let w ← match get pub wit i with
    | some w => .ok w
    | none => .fail .panic
  let u ← shift.ShiftedValue.apply inst t w
  .ok (add acc u)

/-- One operand, read through a readdressing map, term by term from the zero word. -/
def evaluate (inst : word.Word W) (add : W → W → W) (pub wit : List W)
    (remap : index.ValueIndex → RustM index.ValueIndex) (op : constraint.Operand W) : RustM W := do
  let z ← inst.ZERO
  (vlist op.terms).foldlM (readTerm inst add pub wit remap) z

/-- Appends one block of relations: the zero family, then AND, then products, constraint by constraint. -/
def OperationColumns.extend (inst : word.Word W) (add : W → W → W) (pub wit : List W)
    (cols : OperationColumns W) (sys : system.ConstraintSystem W)
    (remap : index.ValueIndex → RustM index.ValueIndex) : RustM (OperationColumns W) := do
  let ev := evaluate inst add pub wit remap
  let zs ← (vlist sys.zero_constraints).mapM fun (c : constraint.ZeroConstraint W) => ev c.value
  let ands ← (vlist sys.and_constraints).mapM fun (c : constraint.AndConstraint W) => do
    let l ← ev c.left
    let r ← ev c.right
    let o ← ev c.output
    .ok (l, r, o)
  let muls ← (vlist sys.integer_mul_constraints).mapM fun (c : constraint.IntegerMulConstraint W) => do
    let a ← ev c.left
    let b ← ev c.right
    let lo ← ev c.low
    let hi ← ev c.high
    .ok (a, b, lo, hi)
  .ok { zero := cols.zero ++ zs
        and_left := cols.and_left ++ ands.map (·.1)
        and_right := cols.and_right ++ ands.map (·.2.1)
        and_output := cols.and_output ++ ands.map (·.2.2)
        mul_left := cols.mul_left ++ muls.map (·.1)
        mul_right := cols.mul_right ++ muls.map (·.2.1)
        mul_low := cols.mul_low ++ muls.map (·.2.2.1)
        mul_high := cols.mul_high ++ muls.map (·.2.2.2) }

/-- The readdressing of one instance of one call, expected to succeed. -/
def resolveOrPanic (inst : word.Word W) (comp : component.Composition W) (call inst' : ℕ)
    (slot : index.ValueIndex) : RustM index.ValueIndex := do
  let r ← component.Composition.resolve inst comp (usz call) (usz inst') slot
  match r with
  | .Ok r => .ok r
  | .Err _ => .fail .panic

/-- The columns of a statement.

The shape is checked first.

A flat statement reads its words directly.

A composed one walks each gadget once per instance, readdressing every term. -/
def OperationColumns.new (inst : word.Word W) (add : W → W → W) (st : Statement W)
    (pub wit : List W) : RustM (Except (index.Segment × ℕ × ℕ) (OperationColumns W)) :=
  match check_shape st pub.length wit.length with
  | .error e => .ok (.error e)
  | .ok () =>
    match st with
    | .Flat sys => do
      let cols ← OperationColumns.extend inst add pub wit .empty sys .ok
      .ok (.ok cols)
    | .Composed comp => do
      let cols ← ((vlist comp.calls).zipIdx).foldlM (fun cols (call, index) =>
        (List.range call.instances.val).foldlM (fun cols inst' =>
          OperationColumns.extend inst add pub wit cols call.component.body
            (resolveOrPanic inst comp index inst')) cols) .empty
      .ok (.ok cols)

end p3_word_backend.columns.mirror
