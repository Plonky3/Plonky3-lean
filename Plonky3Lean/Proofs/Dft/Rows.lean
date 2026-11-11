module

public import P3Dft

@[expose] public section

/-!
# The butterflies on rows

Each unrolled loop computes the butterfly entry by entry, for rows of equal length.
-/

namespace Plonky3Lean.Proofs.Dft

open p3_dft.butterflies.mirror

variable {F : Type _} [Field F]

variable (t s : F)

theorem dit_apply_to_rows :
    ∀ r1 r2 : List F, r1.length = r2.length →
      DitButterfly.apply_to_rows t r1 r2 =
        (List.zipWith (fun a b => a + b * t) r1 r2, List.zipWith (fun a b => a - b * t) r1 r2)
  | a1 :: b1 :: c1 :: d1 :: r1, a2 :: b2 :: c2 :: d2 :: r2, h => by
    rw [DitButterfly.apply_to_rows, dit_apply_to_rows r1 r2 (by simpa using h)]
    simp
  | [], [], _ => by simp [DitButterfly.apply_to_rows]
  | [_], [_], _ => by simp [DitButterfly.apply_to_rows]
  | [_, _], [_, _], _ => by simp [DitButterfly.apply_to_rows]
  | [_, _, _], [_, _, _], _ => by simp [DitButterfly.apply_to_rows]
  | [], _ :: _, h | [_], [], h | [_], _ :: _ :: _, h | [_, _], [], h | [_, _], [_], h
  | [_, _], _ :: _ :: _ :: _, h | [_, _, _], [], h | [_, _, _], [_], h | [_, _, _], [_, _], h
  | [_, _, _], _ :: _ :: _ :: _ :: _, h => by simp at h
  | _ :: _ :: _ :: _ :: _, [], h | _ :: _ :: _ :: _ :: _, [_], h
  | _ :: _ :: _ :: _ :: _, [_, _], h | _ :: _ :: _ :: _ :: _, [_, _, _], h => by simp at h

theorem dif_apply_to_rows :
    ∀ r1 r2 : List F, r1.length = r2.length →
      DifButterfly.apply_to_rows t r1 r2 =
        (List.zipWith (fun a b => a + b) r1 r2, List.zipWith (fun a b => (a - b) * t) r1 r2)
  | a1 :: b1 :: c1 :: d1 :: r1, a2 :: b2 :: c2 :: d2 :: r2, h => by
    rw [DifButterfly.apply_to_rows, dif_apply_to_rows r1 r2 (by simpa using h)]
    simp
  | [], [], _ => by simp [DifButterfly.apply_to_rows]
  | [_], [_], _ => by simp [DifButterfly.apply_to_rows]
  | [_, _], [_, _], _ => by simp [DifButterfly.apply_to_rows]
  | [_, _, _], [_, _, _], _ => by simp [DifButterfly.apply_to_rows]
  | [], _ :: _, h | [_], [], h | [_], _ :: _ :: _, h | [_, _], [], h | [_, _], [_], h
  | [_, _], _ :: _ :: _ :: _, h | [_, _, _], [], h | [_, _, _], [_], h | [_, _, _], [_, _], h
  | [_, _, _], _ :: _ :: _ :: _ :: _, h => by simp at h
  | _ :: _ :: _ :: _ :: _, [], h | _ :: _ :: _ :: _ :: _, [_], h
  | _ :: _ :: _ :: _ :: _, [_, _], h | _ :: _ :: _ :: _ :: _, [_, _, _], h => by simp at h

/-- The scaled butterfly on rows is the plain butterfly scaled by s, entry by entry. -/
theorem scaled_apply_to_rows :
    ∀ r1 r2 : List F, r1.length = r2.length →
      ScaledDitButterfly.apply_to_rows (ScaledDitButterfly.new t s) r1 r2 =
        (List.zipWith (fun a b => (a + b * t) * s) r1 r2, List.zipWith (fun a b => (a - b * t) * s) r1 r2)
  | a1 :: b1 :: c1 :: d1 :: r1, a2 :: b2 :: c2 :: d2 :: r2, h => by
    rw [ScaledDitButterfly.apply_to_rows, scaled_apply_to_rows r1 r2 (by simpa using h)]
    simp only [ScaledDitButterfly.new, List.zipWith_cons_cons]
    ring_nf
  | [], [], _ => by simp [ScaledDitButterfly.apply_to_rows, ScaledDitButterfly.new]
  | [_], [_], _ => by simp [ScaledDitButterfly.apply_to_rows, ScaledDitButterfly.new]; ring_nf; simp
  | [_, _], [_, _], _ => by simp [ScaledDitButterfly.apply_to_rows, ScaledDitButterfly.new]; ring_nf; simp
  | [_, _, _], [_, _, _], _ => by simp [ScaledDitButterfly.apply_to_rows, ScaledDitButterfly.new]; ring_nf; simp
  | [], _ :: _, h | [_], [], h | [_], _ :: _ :: _, h | [_, _], [], h | [_, _], [_], h
  | [_, _], _ :: _ :: _ :: _, h | [_, _, _], [], h | [_, _, _], [_], h | [_, _, _], [_, _], h
  | [_, _, _], _ :: _ :: _ :: _ :: _, h => by simp at h
  | _ :: _ :: _ :: _ :: _, [], h | _ :: _ :: _ :: _ :: _, [_], h
  | _ :: _ :: _ :: _ :: _, [_, _], h | _ :: _ :: _ :: _ :: _, [_, _, _], h => by simp at h

end Plonky3Lean.Proofs.Dft
