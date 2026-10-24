module

public import P3Bus
public import Plonky3Lean.Lib.UsizeAdd

@[expose] public section

/-!
# The extracted integer helpers

hax extracts a direction's position, the boundary rows and the RAM payload widths.

Each returns what its transcription computes, while the result fits a usize.

Past that the shipped code panics, where the transcription, over the naturals, does not.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Bus.Extracted

/-- The direction of the transcriptions. -/
def dirMirror : p3_bus.direction.BusDirection → p3_bus.mirror.BusDirection
  | .Push => .Push
  | .Pull => .Pull

/-- The boundary of the transcriptions. -/
def boundaryMirror : p3_bus.builder.BusBoundary → p3_bus.mirror.BusBoundary
  | .First => .First
  | .Last => .Last

theorem index_eq (d : p3_bus.direction.BusDirection) :
    ∃ n : Std.Usize, p3_bus.direction.BusDirection.index d = .ok n ∧ n.val = (dirMirror d).index := by
  cases d <;> exact ⟨_, rfl, rfl⟩

theorem contains_row_eq (b : p3_bus.builder.BusBoundary) (row height : Std.Usize)
    (hrow : row.val < Usize.max) :
    p3_bus.builder.BusBoundary.contains_row b row height =
      .ok ((boundaryMirror b).contains_row row.val height.val) := by
  cases b
  · simp [p3_bus.builder.BusBoundary.contains_row, boundaryMirror, p3_bus.mirror.BusBoundary.contains_row,
      UScalar.eq_equiv, beq_eq_decide]
  · obtain ⟨i, hi, hiv⟩ := usize_add_ok row 1#usize (by simp; omega)
    simp [p3_bus.builder.BusBoundary.contains_row, boundaryMirror, p3_bus.mirror.BusBoundary.contains_row,
      hi, UScalar.eq_equiv, hiv, beq_eq_decide]

theorem contains_row_max (row height : Std.Usize) (hrow : row.val = Usize.max) :
    p3_bus.builder.BusBoundary.contains_row .Last row height = .fail .panic := by
  simp [p3_bus.builder.BusBoundary.contains_row, usize_add_fail row 1#usize (by simp; omega)]

theorem access_payload_width_eq (st : p3_bus.ram.statement.RamStatement)
    (h : 1 + st.address_bits.val + st.timestamp_bits.val + st.value_width.val ≤ Usize.max) :
    ∃ n : Std.Usize, p3_bus.ram.statement.RamStatement.access_payload_width st = .ok n ∧
      n.val = 1 + st.address_bits.val + st.timestamp_bits.val + st.value_width.val := by
  obtain ⟨a, ha, hav⟩ := usize_add_ok 1#usize st.address_bits (by simp; omega)
  obtain ⟨b, hb, hbv⟩ := usize_add_ok a st.timestamp_bits (by simp at hav; omega)
  obtain ⟨c, hc, hcv⟩ := usize_add_ok b st.value_width (by simp at hav; omega)
  refine ⟨c, ?_, by simp at hav; omega⟩
  simp [p3_bus.ram.statement.RamStatement.access_payload_width, ha, hb, hc]

theorem access_payload_width_fail (st : p3_bus.ram.statement.RamStatement)
    (h : Usize.max < 1 + st.address_bits.val + st.timestamp_bits.val + st.value_width.val) :
    p3_bus.ram.statement.RamStatement.access_payload_width st = .fail .panic := by
  unfold p3_bus.ram.statement.RamStatement.access_payload_width
  by_cases h1 : (1#usize).val + st.address_bits.val ≤ Usize.max
  · obtain ⟨a, ha, hav⟩ := usize_add_ok _ _ h1
    by_cases h2 : a.val + st.timestamp_bits.val ≤ Usize.max
    · obtain ⟨b, hb, hbv⟩ := usize_add_ok _ _ h2
      simp only [ha, hb, Std.bind_ok]
      exact usize_add_fail b st.value_width (by simp at hav; omega)
    · simp only [ha, Std.bind_ok, usize_add_fail a st.timestamp_bits (not_le.mp h2), Std.bind_fail]
  · simp only [usize_add_fail _ _ (not_le.mp h1), Std.bind_fail]

theorem image_payload_width_eq (st : p3_bus.ram.statement.RamStatement)
    (h : st.address_bits.val + st.value_width.val ≤ Usize.max) :
    ∃ n : Std.Usize, p3_bus.ram.statement.RamStatement.image_payload_width st = .ok n ∧
      n.val = st.address_bits.val + st.value_width.val :=
  usize_add_ok _ _ h

theorem image_payload_width_fail (st : p3_bus.ram.statement.RamStatement)
    (h : Usize.max < st.address_bits.val + st.value_width.val) :
    p3_bus.ram.statement.RamStatement.image_payload_width st = .fail .panic :=
  usize_add_fail _ _ h

end Plonky3Lean.Proofs.Bus.Extracted
