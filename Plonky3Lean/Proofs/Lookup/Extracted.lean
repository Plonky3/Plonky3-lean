module

public import P3Lookup
public import Plonky3Lean.Lib

@[expose] public section

/-!
# The extracted helpers

The extracted count record and the gadget's constructor never panic and return what their names say.
-/

namespace Plonky3Lean.Proofs.Lookup.Extracted

open Aeneas Aeneas.Std CoreModels
open p3_lookup

variable {E : Type}

/-- A bounded count keeps its expression and its weight. -/
theorem bounded_spec (e : E) (w : Std.U32) :
    count.Count.bounded e w = .ok { expr := e, weight := w } := rfl

/-- A provided count has weight 0. -/
theorem provided_spec (e : E) : count.Count.provided e = .ok { expr := e, weight := 0#u32 } := rfl

/-- The weight accessor returns the weight. -/
theorem weight_spec (c : count.Count E) : count.Count.impl.weight c = .ok c.weight := rfl

/-- Splitting a count returns its expression and its weight. -/
theorem into_parts_spec (c : count.Count E) : count.Count.into_parts c = .ok (c.expr, c.weight) :=
  rfl

/-- The gadget's constructor never panics. -/
theorem new_spec : logup.LogUpGadget.new = .ok () := rfl

end Plonky3Lean.Proofs.Lookup.Extracted
