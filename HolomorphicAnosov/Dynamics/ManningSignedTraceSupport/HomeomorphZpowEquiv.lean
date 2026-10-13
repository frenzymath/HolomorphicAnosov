import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Algebra.Group.End

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter

/-- Forgetting topology preserves integer powers: the forgetful map is a group
homomorphism, so the general homomorphism power law applies. -/
theorem homeomorph_zpow_equiv {X : Type*} [TopologicalSpace X]
    (F : X ≃ₜ X) (j : ℤ) : (F ^ j).toEquiv = F.toEquiv ^ j := by
  let φ : (X ≃ₜ X) →* (X ≃ X) :=
    { toFun := Homeomorph.toEquiv
      map_one' := rfl
      map_mul' := by intro a b; rfl }
  exact map_zpow φ F j


end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter
