/-
Transcriptions of the batched equality tables of p3-multilinear-util.

A dense matrix view is the list of its rows; column i of the points matrix is point i.

The input field IF is the field of the coordinates, and EF the field of the weights and of the output.

A product of a value by a coordinate maps the coordinate into the value's algebra first.

Every index the loops read or write is in range at every call site, so out-of-range accesses are not modelled.

The flag INITIALIZED adds to the output when true and overwrites it when false.

The workspaces are modelled by their lengths: a split past the end panics, and the values left in them are never read.
-/
module

public import P3MultilinearUtil.Model
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace p3_multilinear_util.eq_batch.mirror

open p3_multilinear_util.mirror

variable {IF EF : Type _} [Field IF] [Field EF] [Algebra IF EF]

/-- One doubling of the buffer for every point: row idx keeps v - v z, row idx + stride gets v z. -/
def fillStep {A : Type _} [CommRing A] [Algebra IF A] (m : ℕ) (row : List IF) (stride : ℕ)
    (buf : List (List A)) (idx : ℕ) : List (List A) :=
  let vals := (buf.getD idx []).zip (row.take m)
  let scaled := vals.map fun vz => vz.1 * algebraMap IF A vz.2
  let kept := (vals.zip scaled).map fun vs => vs.1.1 - vs.2
  (buf.set idx kept).set (idx + stride) scaled

/-- fill_buffer_batch: the variables from the last, the k-th from the end with stride 2^k.

It debug-asserts that the two matrices have the same width. -/
def fill_buffer_batch {A : Type _} [CommRing A] [Algebra IF A] (m_evals m : ℕ)
    (evals : List (List IF)) (buffer : List (List A)) : Option (List (List A)) :=
  if m_evals ≠ m then none
  else some (evals.reverse.zipIdx.foldl (fun buf ri =>
    (List.range (2 ^ ri.2)).foldl (fillStep m ri.1 (2 ^ ri.2)) buf) buffer)

/-- eval_eq_1_batch: the two weighted sums over one variable, eq(1, z) = z and eq(0, z) = 1 - z. -/
def eval_eq_1_batch (row : List IF) (scalars : List EF) : EF × EF :=
  let sum := scalars.sum
  let eq_1_sum := (List.zipWith (fun s z => s * algebraMap IF EF z) scalars row).sum
  (sum - eq_1_sum, eq_1_sum)

/-- One split of the weights: s z for the bit-1 branch and s - s z for the bit-0 branch. -/
def splitScalars (row : List IF) (scalars : List EF) : List EF × List EF :=
  let s1 := List.zipWith (fun s z => s * algebraMap IF EF z) scalars row
  (List.zipWith (· - ·) scalars s1, s1)

/-- eval_eq_2_batch: the four sums over two variables, in big-endian order; the workspace holds 2 m. -/
def eval_eq_2_batch (rows : List (List IF)) (scalars : List EF) (m ws : ℕ) : Option (List EF) :=
  if ws < 2 * m then none
  else
    let (eq_0s, eq_1s) := splitScalars (rows.getD 0 []) scalars
    let (e00, e01) := eval_eq_1_batch (rows.getD 1 []) eq_0s
    let (e10, e11) := eval_eq_1_batch (rows.getD 1 []) eq_1s
    some [e00, e01, e10, e11]

/-- eval_eq_3_batch: the eight sums over three variables; the workspace holds 6 m. -/
def eval_eq_3_batch (rows : List (List IF)) (scalars : List EF) (m ws : ℕ) : Option (List EF) := do
  if ws < 2 * m then none
  let next := ws - 2 * m
  if next < 2 * m then none
  if next - 2 * m < 2 * m then none
  let (eq_0s, eq_1s) := splitScalars (rows.getD 0 []) scalars
  let lo ← eval_eq_2_batch rows.tail eq_0s m (2 * m)
  let hi ← eval_eq_2_batch rows.tail eq_1s m (2 * m)
  pure (lo ++ hi)

/-- add_or_set: add the evaluations to the output, or overwrite it. -/
def add_or_set (initialized : Bool) (out evaluations : List EF) : Option (List EF) :=
  if out.length ≠ evaluations.length then none
  else if initialized then some (List.zipWith (· + ·) out evaluations)
  else some evaluations

/-- eval_eq_batch_basic: unrolled up to three variables, then a split on the first variable. -/
def eval_eq_batch_basic (initialized : Bool) (m : ℕ) :
    List (List IF) → List EF → List EF → ℕ → Option (List EF)
  | rows, scalars, out, ws =>
    if out.length ≠ 2 ^ rows.length then none
    else match rows with
      | [] =>
        let sum := scalars.sum
        some (out.set 0 (if initialized then out.getD 0 0 + sum else sum))
      | [r0] =>
        let (e0, e1) := eval_eq_1_batch r0 scalars
        add_or_set initialized out [e0, e1]
      | [r0, r1] => do add_or_set initialized out (← eval_eq_2_batch [r0, r1] scalars m ws)
      | [r0, r1, r2] => do add_or_set initialized out (← eval_eq_3_batch [r0, r1, r2] scalars m ws)
      | r0 :: r1 :: r2 :: r3 :: rest => do
        if ws < 2 * m then none
        let (s0, s1) := splitScalars r0 scalars
        let half := out.length / 2
        let low ← eval_eq_batch_basic initialized m (r1 :: r2 :: r3 :: rest) s0 (out.take half)
          (ws - 2 * m)
        let high ← eval_eq_batch_basic initialized m (r1 :: r2 :: r3 :: rest) s1 (out.drop half)
          (ws - 2 * m)
        pure (low ++ high)

/-- packed_eq_poly_batch: the tables of the last log_2 W variables, one packed value per point.

The buffer starts with the weights in row 0; column i is then packed, and from_ext_slice asserts it has W entries. -/
def packed_eq_poly_batch {K : Type _} [Field K] (W m : ℕ) (rows : List (List K))
    (scalars : List K) : Option (List (Fin W → K)) := do
  if W ≠ 2 ^ rows.length then none
  let buffer : List (List K) :=
    scalars :: List.replicate (2 ^ rows.length - 1) (List.replicate m 0)
  let buffer ← fill_buffer_batch m m rows buffer
  (List.range m).mapM fun col =>
    from_ext_slice W ((List.range (2 ^ rows.length)).map fun r => (buffer.getD r []).getD col 0)

/-- An evaluation strategy: the packed type, the seed tables and the final accumulation. -/
structure Evaluator (IF EF P : Type _) where
  /-- The packed seed of each point over the last log_2 W variables. -/
  init_packed_batch : List (List IF) → List EF → Option (List P)
  /-- Write or add the weighted lanes of the packed tables into an output of W entries. -/
  accumulate_packed_batch : Bool → List EF → List P → List EF → Option (List EF)

/-- The extension evaluator: the seeds carry the weights, and the accumulation sums the packed tables. -/
def extEvaluator (W m : ℕ) : Evaluator EF EF (Fin W → EF) where
  init_packed_batch rows scalars := packed_eq_poly_batch W m rows scalars
  accumulate_packed_batch initialized out final _ :=
    if final.isEmpty then some (if initialized then out else out.map fun _ => 0)
    else
      let unpacked := List.ofFn final.sum
      some (if initialized then List.zipWith (· + ·) out unpacked ++ out.drop unpacked.length
        else unpacked.take out.length ++ out.drop unpacked.length)

/-- The base evaluator: the seeds have unit weights, and lane k accumulates sum_i scalars_i table_i[k]. -/
def baseEvaluator {F : Type _} [Field F] [Algebra F EF] (W m : ℕ) : Evaluator F EF (Fin W → F) where
  init_packed_batch rows _ := packed_eq_poly_batch W m rows (List.replicate m 1)
  accumulate_packed_batch initialized out final scalars :=
    if out.length ≠ W ∨ final.length ≠ scalars.length then none
    else if scalars.isEmpty then some (if initialized then out else out.map fun _ => 0)
    else some ((List.range out.length).map fun k =>
      let dot := (List.zipWith (fun s (v : Fin W → F) =>
        s * algebraMap F EF (if h : k < W then v ⟨k, h⟩ else 0)) scalars final).sum
      if initialized then out.getD k 0 + dot else dot)

/-- One split of the packed tables: t z for the bit-1 branch and t - t z for the bit-0 branch. -/
def splitPacked {P : Type _} [CommRing P] [Algebra IF P] (row : List IF) (eq_evals : List P) :
    List P × List P :=
  let s1 := List.zipWith (fun t z => t * algebraMap IF P z) eq_evals row
  (List.zipWith (· - ·) eq_evals s1, s1)

/-- eval_eq_packed_batch: unrolled up to three variables, then a split on the first variable.

The output has W 2^n entries, and the workspace holds 2 m, 4 m or 8 m at the unrolled sizes. -/
def eval_eq_packed_batch {P : Type _} [CommRing P] [Algebra IF P] (E : Evaluator IF EF P)
    (W : ℕ) (initialized : Bool) (m : ℕ) :
    List (List IF) → List EF → List P → List EF → ℕ → Option (List EF)
  | rows, out, eq_evals, scalars, ws =>
    if out.length ≠ W * 2 ^ rows.length then none
    else match rows with
      | [] => E.accumulate_packed_batch initialized out eq_evals scalars
      | [r0] => do
        if ws < 2 * m then none
        let (s0, s1) := splitPacked r0 eq_evals
        let half := out.length / 2
        let low ← E.accumulate_packed_batch initialized (out.take half) s0 scalars
        let high ← E.accumulate_packed_batch initialized (out.drop half) s1 scalars
        pure (low ++ high)
      | [r0, r1] => do
        if ws < 4 * m then none
        let (s0, s1) := splitPacked r0 eq_evals
        let (s00, s01) := splitPacked r1 s0
        let (s10, s11) := splitPacked r1 s1
        let q := out.length / 4
        let o00 ← E.accumulate_packed_batch initialized (out.take q) s00 scalars
        let o01 ← E.accumulate_packed_batch initialized ((out.drop q).take q) s01 scalars
        let o10 ← E.accumulate_packed_batch initialized ((out.drop (2 * q)).take q) s10 scalars
        let o11 ← E.accumulate_packed_batch initialized (out.drop (3 * q)) s11 scalars
        pure (o00 ++ o01 ++ o10 ++ o11)
      | [r0, r1, r2] => do
        if ws < 8 * m then none
        let (s0, s1) := splitPacked r0 eq_evals
        let (s00, s01) := splitPacked r1 s0
        let (s10, s11) := splitPacked r1 s1
        let leaves := [splitPacked r2 s00, splitPacked r2 s01, splitPacked r2 s10,
          splitPacked r2 s11].flatMap fun pr => [pr.1, pr.2]
        let e := out.length / 8
        let parts ← (List.range 8).mapM fun j =>
          E.accumulate_packed_batch initialized
            (if j = 7 then out.drop (7 * e) else (out.drop (j * e)).take e)
            (leaves.getD j []) scalars
        pure parts.flatten
      | r0 :: r1 :: r2 :: r3 :: rest => do
        if ws < 2 * m then none
        let (s0, s1) := splitPacked r0 eq_evals
        let half := out.length / 2
        let low ← eval_eq_packed_batch E W initialized m (r1 :: r2 :: r3 :: rest) (out.take half) s0
          scalars (ws - 2 * m)
        let high ← eval_eq_packed_batch E W initialized m (r1 :: r2 :: r3 :: rest) (out.drop half)
          s1 scalars (ws - 2 * m)
        pure (low ++ high)

/-- eval_eq_batch_common, for W = 2^w lanes and T threads.

Small tables take the recursive path; large ones split the variables into thread, middle and lane variables. -/
def eval_eq_batch_common {P : Type _} [CommRing P] [Algebra IF P] (E : Evaluator IF EF P)
    (w T : ℕ) (initialized : Bool) (m : ℕ) (rows : List (List IF)) (out scalars : List EF) :
    Option (List EF) := do
  if m = 0 then
    if scalars.isEmpty then return out else none
  let n := rows.length
  if m ≠ scalars.length then none
  if out.length ≠ 2 ^ n then none
  let log_num_threads := Nat.clog 2 T
  if n ≤ w + 1 + log_num_threads then
    eval_eq_batch_basic initialized m rows scalars out (max (2 * m * n) 1)
  else
    let front_rows := rows.take (n - w)
    let packed_rows := rows.drop (n - w)
    let init_packings ← E.init_packed_batch packed_rows scalars
    if init_packings.length ≠ m then none
    let parallel_buffer : List (List P) :=
      init_packings :: List.replicate (2 ^ log_num_threads - 1) (List.replicate m 0)
    let buffer_rows := front_rows.take log_num_threads
    let middle_rows := front_rows.drop log_num_threads
    let parallel_buffer ← fill_buffer_batch m m buffer_rows parallel_buffer
    let out_chunk_size := out.length / 2 ^ log_num_threads
    let parts ← ((chunks out_chunk_size out).zip parallel_buffer).mapM fun cb =>
      eval_eq_packed_batch E (2 ^ w) initialized m middle_rows cb.1 cb.2 scalars
        (max (2 * (middle_rows.length + 1) * m) (8 * m))
    pure parts.flatten

/-- eval_eq_batch: the points and the weights in EF. -/
def eval_eq_batch (w T : ℕ) (initialized : Bool) (m : ℕ) (rows : List (List EF))
    (out scalars : List EF) : Option (List EF) :=
  eval_eq_batch_common (extEvaluator (2 ^ w) m) w T initialized m rows out scalars

/-- eval_eq_base_batch: the points in the base field F and the weights in EF. -/
def eval_eq_base_batch {F : Type _} [Field F] [Algebra F EF] (w T : ℕ) (initialized : Bool)
    (m : ℕ) (rows : List (List F)) (out scalars : List EF) : Option (List EF) :=
  eval_eq_batch_common (baseEvaluator (EF := EF) (2 ^ w) m) w T initialized m rows out scalars

end p3_multilinear_util.eq_batch.mirror
