import HolomorphicAnosov.Topology.TorusCoordinateCover

namespace HolomorphicAnosov

open _root_.HolomorphicAnosov.Topology

noncomputable section
open Filter Function
open scoped _root_.Topology

/-- Integral vectors, as actual points of the projection kernel. -/
def integerKernelMap (n : ℕ) : (Fin n → ℤ) →+ (coordinateProjection n).ker where
  toFun z := ⟨fun i ↦ (z i : ℝ), by
    change coordinateProjection n _ = 0
    ext i
    exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨z i, by simp⟩⟩
  map_zero' := by ext; simp
  map_add' z w := by ext; simp

end
end HolomorphicAnosov
