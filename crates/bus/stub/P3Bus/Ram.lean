/-
Transcriptions of the mutable read-write memory: its statement, its column layout, and its constraints.

These do not extract: the constraints are generic over the builder.

Code over `ExtensionField` also does not extract (docs/extractor-issues.md 180).

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the declaring builder:

- a machine word is a natural number
- an addition that overflows 64 bits is the error Rust returns
- a slice of a row is its sublist, and a range past the row's end panics
- a debug assertion panics, as in a debug build
- a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Bus.Builder

@[expose] public section

namespace p3_bus.ram.mirror

open p3_air.builder.mirror p3_bus.mirror

/-! ## The statement -/

/-- The largest cell number or clock width decomposed into digits. -/
def MAX_RAM_BIT_WIDTH : ℕ := 64

/-- The fewest accesses a statement may cover. -/
def MIN_RAM_ACCESS_COUNT : ℕ := 2

/-- How one proof's memory relates to the executions on either side of it. -/
inductive RamBoundary where
  | SingleProof
  | Segment (incoming outgoing : String)
  deriving DecidableEq

def RamBoundary.is_segment : RamBoundary → Bool
  | .SingleProof => false
  | .Segment .. => true

def RamBoundary.image_buses : RamBoundary → Option (String × String)
  | .SingleProof => none
  | .Segment incoming outgoing => some (incoming, outgoing)

/-- The public shape of one memory. -/
structure RamStatement where
  access_bus : String
  access_count : ℕ
  address_bits : ℕ
  timestamp_bits : ℕ
  value_width : ℕ
  boundary : RamBoundary

/-- The errors a statement or layout can raise. -/
inductive RamError where
  | TooFewAccesses (access_count minimum : ℕ)
  | NonPowerOfTwoAccessCount (access_count : ℕ)
  | AddressBits (address_bits maximum : ℕ)
  | TimestampBits (timestamp_bits maximum : ℕ)
  | EmptyValue
  | DuplicateBus (nm : String)
  | BusName (nm : String) (error : BusNameError)
  | LayoutOverflow
  deriving DecidableEq

/-- Operation, cell digits, clock digits, then value. -/
def RamStatement.access_payload_width (st : RamStatement) : ℕ :=
  1 + st.address_bits + st.timestamp_bits + st.value_width

/-- Cell digits, then value. -/
def RamStatement.image_payload_width (st : RamStatement) : ℕ := st.address_bits + st.value_width

/-- Validate a statement: the dimensions in order, then each channel name and its uniqueness. -/
def RamStatement.validate (st : RamStatement) : Except RamError Unit := do
  if st.access_count < MIN_RAM_ACCESS_COUNT then
    throw (.TooFewAccesses st.access_count MIN_RAM_ACCESS_COUNT)
  if ¬ (st.access_count ≠ 0 ∧ st.access_count &&& (st.access_count - 1) = 0) then
    throw (.NonPowerOfTwoAccessCount st.access_count)
  if st.address_bits = 0 ∨ st.address_bits > MAX_RAM_BIT_WIDTH then
    throw (.AddressBits st.address_bits MAX_RAM_BIT_WIDTH)
  if st.timestamp_bits = 0 ∨ st.timestamp_bits > MAX_RAM_BIT_WIDTH then
    throw (.TimestampBits st.timestamp_bits MAX_RAM_BIT_WIDTH)
  if st.value_width = 0 then throw .EmptyValue
  let names := st.access_bus :: (match st.boundary.image_buses with
    | some (incoming, outgoing) => [incoming, outgoing]
    | none => [])
  (List.range names.length).forM fun position => do
    let nm := names.getD position ""
    match BusName.try_new nm with
    | .error error => throw (.BusName nm error)
    | .ok _ => pure ()
    if (names.take position).contains nm then throw (.DuplicateBus nm)

/-- Leaves added on the push and pull sides.

There is one pull per access.

A continuing proof adds an image entry each way per row. -/
def RamStatement.leaf_contribution (st : RamStatement) : ℕ × ℕ :=
  let images := if st.boundary.is_segment then st.access_count else 0
  (images, st.access_count + images)

/-! ## The layout -/

/-- The column offsets of the sorted trace. -/
structure RamLayout where
  address_bits : ℕ
  timestamp_bits : ℕ
  value_width : ℕ
  compare_bits : ℕ
  operation : ℕ
  address : ℕ
  timestamp : ℕ
  value : ℕ
  same_address : ℕ
  compare_delta : ℕ
  compare_carry : ℕ
  compare_nonzero : ℕ
  group_end : ℕ
  width : ℕ
  deriving DecidableEq

/-- Addition of machine words, none at 2^64 or more. -/
def checked_add (a b : ℕ) : Option ℕ := if a + b < 2 ^ 64 then some (a + b) else none

/-- One step of the offset allocator: the current offset, and the next one. -/
def take (next count : ℕ) : Except RamError (ℕ × ℕ) :=
  match checked_add next count with
  | some n => .ok (next, n)
  | none => .error .LayoutOverflow

/-- The layout: validate, then allocate the columns in order. -/
def RamLayout.new (st : RamStatement) : Except RamError RamLayout := do
  st.validate
  let compare_bits := max st.address_bits st.timestamp_bits
  let (operation, n) ← take 0 1
  let (address, n) ← take n st.address_bits
  let (timestamp, n) ← take n st.timestamp_bits
  let (value, n) ← take n st.value_width
  let (same_address, n) ← take n 1
  let (compare_delta, n) ← take n compare_bits
  let (compare_carry, n) ← take n (compare_bits + 1)
  let (compare_nonzero, n) ← take n compare_bits
  let (group_end, n) ← take n (if st.boundary.is_segment then 1 else 0)
  pure { address_bits := st.address_bits, timestamp_bits := st.timestamp_bits,
         value_width := st.value_width, compare_bits, operation, address, timestamp, value,
         same_address, compare_delta, compare_carry, compare_nonzero, group_end, width := n }

/-- The columns of one access: operation, cell digits, clock digits, then value. -/
def RamLayout.access_columns (L : RamLayout) : List ℕ :=
  [L.operation] ++ (List.range L.address_bits).map (L.address + ·) ++
    (List.range L.timestamp_bits).map (L.timestamp + ·) ++ (List.range L.value_width).map (L.value + ·)

/-- The columns of one image entry: the cell digits, then the value. -/
def RamLayout.image_columns (L : RamLayout) : List ℕ :=
  (List.range L.address_bits).map (L.address + ·) ++ (List.range L.value_width).map (L.value + ·)

/-! ## The constraints -/

/-- The memory AIR: the statement and its layout. -/
structure RamAir where
  statement : RamStatement
  layout : RamLayout

/-- Build the AIR from its layout, which validates. -/
def RamAir.new (st : RamStatement) : Except RamError RamAir := do
  pure ⟨st, ← RamLayout.new st⟩

/-- The n entries of a row from position a, which panics past the row's end. -/
def slice {E : Type _} (row : List E) (a n : ℕ) : Option (List E) :=
  if a + n ≤ row.length then some ((row.drop a).take n) else none

variable {F E S : Type _} [Zero F] [One F] [OfNat F 2]

/-- Exclusive or of two bit-valued expressions: l + r - 2 l r. -/
def xor (B : ExprOps F E) (l r : E) : E := B.sub (B.add l r) (B.mul (B.mul (B.const 2) l) r)

/-- Exclusive or of three bit-valued expressions. -/
def xor3 (B : ExprOps F E) (a b c : E) : E := xor B (xor B a b) c

/-- Majority of three bit-valued expressions: ab + ac + bc - 2abc. -/
def majority (B : ExprOps F E) (a b c : E) : E :=
  B.sub (B.add (B.add (B.mul a b) (B.mul a c)) (B.mul b c))
    (B.mul (B.mul (B.mul (B.const 2) a) b) c)

/-- Inclusive or of two bit-valued expressions: l + r - l r. -/
def or (B : ExprOps F E) (l r : E) : E := B.sub (B.add l r) (B.mul l r)

/-- The later key is the earlier one plus a nonzero gap.

A ripple adder checks the sum, and refuses a final carry. -/
def assert_strict_increase (B : AirBuilder F E S) (s : S) (enabled : E)
    (left right delta carry nonzero : List E) : Option S := do
  let bits := left.length
  if ¬ (right.length = bits ∧ bits ≤ delta.length ∧ bits < carry.length ∧ bits ≤ nonzero.length)
  then none
  let s := B.assert_zero s (B.mul enabled (← carry[0]?))
  let s ← (List.range bits).foldlM (fun s bit => do
    let addend ← left[bit]?
    let difference ← delta[bit]?
    let carry_in ← carry[bit]?
    let sum := xor3 B.toExprOps addend difference carry_in
    let s := B.assert_zero s (B.mul enabled (B.sub (← right[bit]?) sum))
    let s := B.assert_zero s (B.mul enabled
      (B.sub (← carry[bit + 1]?) (majority B.toExprOps addend difference carry_in)))
    let running ← if bit = 0 then pure difference
      else do pure (or B.toExprOps (← nonzero[bit - 1]?) difference)
    pure (B.assert_zero s (B.mul enabled (B.sub (← nonzero[bit]?) running)))) s
  let s := B.assert_zero s (B.mul enabled (← carry[bits]?))
  if bits = 0 then none
  pure (B.assert_zero s (B.mul enabled (B.sub (B.const 1) (← nonzero[bits - 1]?))))

/-- Every cell digit, clock digit and gap digit is a bit. -/
def RamAir.eval_booleanity (air : RamAir) (B : AirBuilder F E S) (s : S) : Option S := do
  let row := (B.main s).current
  let L := air.layout
  let s ← (List.range L.address_bits).foldlM
    (fun s bit => do pure (B.assert_bool s (← row[L.address + bit]?))) s
  let s ← (List.range L.timestamp_bits).foldlM
    (fun s bit => do pure (B.assert_bool s (← row[L.timestamp + bit]?))) s
  (List.range L.compare_bits).foldlM
    (fun s bit => do pure (B.assert_bool s (← row[L.compare_delta + bit]?))) s

/-- An opening read returns zero, or a continuing proof's opening access is a read. -/
def RamAir.eval_run_start (air : RamAir) (B : AirBuilder F E S) (s : S) (row : List E) :
    Option S := do
  let L := air.layout
  match air.statement.boundary with
  | .SingleProof =>
    let read := B.sub (B.const 1) (← row[L.operation]?)
    (List.range L.value_width).foldlM
      (fun s component => do pure (B.assert_zero s (B.mul read (← row[L.value + component]?)))) s
  | .Segment .. => pure (B.assert_zero s (← row[L.operation]?))

/-- The order constraints.

Row zero gets the opening rule.

Each transition gets:

- the cell equality
- the two strict comparisons
- read continuity
- a continuing proof's opening rule. -/
def RamAir.eval_order (air : RamAir) (B : AirBuilder F E S) (s : S) : Option S := do
  let row := (B.main s).current
  let next_row := (B.main s).next
  let L := air.layout
  let first := B.when_first_row s
  let s := first.assert_zero s (← row[L.same_address]?)
  let s ← air.eval_run_start first s row
  let transition := B.when_transition s
  let same ← next_row[L.same_address]?
  let s ← (List.range L.address_bits).foldlM (fun s bit => do
    let previous ← row[L.address + bit]?
    let current ← next_row[L.address + bit]?
    pure (transition.assert_zero s (B.mul same (B.sub current previous)))) s
  let delta ← slice next_row L.compare_delta L.compare_bits
  let carry ← slice next_row L.compare_carry (L.compare_bits + 1)
  let nonzero ← slice next_row L.compare_nonzero L.compare_bits
  let s ← assert_strict_increase transition s (B.sub (B.const 1) same)
    (← slice row L.address L.address_bits) (← slice next_row L.address L.address_bits)
    delta carry nonzero
  let s ← assert_strict_increase transition s same
    (← slice row L.timestamp L.timestamp_bits) (← slice next_row L.timestamp L.timestamp_bits)
    delta carry nonzero
  let read := B.sub (B.const 1) (← next_row[L.operation]?)
  let s ← (List.range L.value_width).foldlM (fun s component => do
    let previous ← row[L.value + component]?
    let current ← next_row[L.value + component]?
    match air.statement.boundary with
    | .SingleProof =>
      pure (transition.assert_zero s (B.mul read (B.sub current (B.mul same previous))))
    | .Segment .. =>
      pure (transition.assert_zero s (B.mul (B.mul read same) (B.sub current previous)))) s
  if air.statement.boundary.is_segment then
    air.eval_run_start (transition.when_ne same (B.const 1)) s next_row
  else pure s

/-- The run marker of a continuing proof.

A row closes its run exactly when the next row opens one, and the last row closes. -/
def RamAir.eval_run_marker (air : RamAir) (B : AirBuilder F E S) (s : S) : Option S := do
  if !air.statement.boundary.is_segment then return s
  let row := (B.main s).current
  let next_row := (B.main s).next
  let L := air.layout
  let s := (B.when_transition s).assert_eq s (← row[L.group_end]?)
    (B.sub (B.const 1) (← next_row[L.same_address]?))
  pure ((B.when_last_row s).assert_one s (← row[L.group_end]?))

/-- A validated channel name, read back. -/
def channel (nm : String) : Option String :=
  match BusName.try_new nm with
  | .ok nm => some nm
  | .error _ => none

/-- Declare the bus interactions: pull each access.

A continuing proof also pulls each opening value from the inherited image.

It pushes each closing value to the handed-on image. -/
def RamAir.declare (air : RamAir) (B : BusBuilder F E S) (s : S) : Option S := do
  let row := (B.main s).current
  let L := air.layout
  let access ← L.access_columns.mapM (row[·]?)
  let s := B.push_bus_interaction s (← channel air.statement.access_bus) .Pull access .Always
  match air.statement.boundary with
  | .SingleProof => pure s
  | .Segment incoming outgoing =>
    let image ← L.image_columns.mapM (row[·]?)
    let opening := B.sub (B.const 1) (← row[L.same_address]?)
    let s := B.push_bus_interaction s (← channel incoming) .Pull image (.Boolean opening)
    let closing ← row[L.group_end]?
    pure (B.push_bus_interaction s (← channel outgoing) .Push image (.Boolean closing))

/-- The AIR's evaluation: the bits, the order, the run marker, then the declarations. -/
def RamAir.eval (air : RamAir) (B : BusBuilder F E S) (s : S) : Option S := do
  let s ← air.eval_booleanity B.toAirBuilder s
  let s ← air.eval_order B.toAirBuilder s
  let s ← air.eval_run_marker B.toAirBuilder s
  air.declare B s

end p3_bus.ram.mirror
