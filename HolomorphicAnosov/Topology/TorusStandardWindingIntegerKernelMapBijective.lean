import HolomorphicAnosov.Topology.TorusStandardWindingBase

namespace HolomorphicAnosov

open _root_.HolomorphicAnosov.Topology

noncomputable section
open Filter Function
open scoped _root_.Topology

/-- Coordinatewise integer-cast injectivity and `AddCircle.coe_eq_zero_iff` give the exact deck coordinates. -/
theorem integerKernelMap_bijective (n : ℕ) : Bijective (integerKernelMap n) := by
  constructor
  · intro z w h
    funext i
    exact Int.cast_injective (congrArg (fun g : (coordinateProjection n).ker ↦ g.val i) h)
  · intro v
    have hv (i : Fin n) : ∃ z : ℤ, (z : ℝ) = v.val i := by
      have hi := congrFun v.property i
      obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hi
      exact ⟨z, by simpa using hz⟩
    choose z hz using hv
    exact ⟨z, Subtype.ext (funext hz)⟩

end
end HolomorphicAnosov
