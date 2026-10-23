module

public import Plonky3Lean.Proofs.Bus.Gkr

@[expose] public section

/-!
# The bus's security terms

The bus charges four error events, each a numerator over the challenge-field order:

```text
    fingerprint   max(1, s) N        tuple collisions and the offset
    sumcheck      5 R                degree-five rounds
    batching      L (T - 1)          one challenge per layer over T trees
    collapse      h                  one coordinate per contracted level
```

The fingerprint numerator is the coefficient of the proven soundness count.

The other three follow the schedule: for a height h = 2k, R = k(k - 1) and L = k; for h = 2k + 1, R = k^2 and L = k + 1.
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.security.mirror p3_bus.plan.mirror p3_bus.product.mirror

/-- **The charged numerators.** With two trees, the bus charges max(1, s) N for the fingerprint, then 5 R, L and h, each omitted when zero. -/
theorem components_eq (plan : BusPlan) (h2 : plan.product_shape.num_trees = 2) :
    components (p3_bus.security.mirror.BusPlan.security_dims plan) =
      [max 1 plan.geometry.tuple_variables * max plan.geometry.non_padding_leaf_counts.1
        plan.geometry.non_padding_leaf_counts.2] ++
      ([5 * (if plan.product_shape.log_height % 2 = 0 then
          (plan.product_shape.log_height / 2) * (plan.product_shape.log_height / 2 - 1)
        else (plan.product_shape.log_height / 2) ^ 2),
        (plan.product_shape.log_height + 1) / 2, plan.product_shape.log_height].filter (· ≠ 0)) := by
  simp only [components, p3_bus.security.mirror.BusPlan.security_dims, layers_rounds,
    layers_length, layers_branches, h2,
    Nat.add_one_sub_one, mul_one, max_comm 1]

end Plonky3Lean.Proofs.Bus
