import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Homeomorph.Lemmas

namespace HolomorphicAnosov

/-- A homeomorphic front disjoint from a center has a continuous positive inverse-direction radius.

This is the center-avoidance component of Cairns's radial-front construction.  It is
independent of the angular parametrization and is reusable whenever a compact front is
parametrized by a topological space of directions. -/
theorem continuous_positive_inverse_direction_radius
    {E : Type*} [NormedAddCommGroup E]
    {D : Type*} [TopologicalSpace D]
    (N : E) (L : Set E) (hN : ∀ Q ∈ L, Q ≠ N) (d : L ≃ₜ D) :
    Continuous (fun v ↦ ‖(d.symm v : E) - N‖) ∧
      (∀ v, 0 < ‖(d.symm v : E) - N‖) := by
  constructor
  · exact continuous_norm.comp
      ((continuous_subtype_val.comp d.symm.continuous).sub continuous_const)
  · intro v
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (hN (d.symm v) (d.symm v).property))

end HolomorphicAnosov
