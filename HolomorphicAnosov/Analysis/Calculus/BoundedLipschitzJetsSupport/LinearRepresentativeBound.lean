import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.DifferentiableRepresentativeStructure

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Bounded linear maps are bounded representatives, HPS (3.3), p. 29.
Linearity gives L(0)=0 and `ContinuousLinearMap.le_opNorm` gives the global
bound ‖Lx‖ ≤ ‖L‖‖x‖, with nonnegative bound ‖L‖. Thus the same bound is
eventual on the punctured neighborhood filter, including the zero domain. -/
theorem linearMap_isBoundedRepresentative (L : X →L[ℝ] Y) :
    IsBoundedRepresentative X Y (L : X → Y) := by
  exact ⟨L.map_zero, ‖L‖, norm_nonneg _,
    Filter.Eventually.of_forall fun x ↦ L.le_opNorm x⟩

/-- The actual function underlying a bounded linear representative, HPS p. 29. -/
def linearRepresentative (L : X →L[ℝ] Y) : BoundedRepresentative X Y :=
  ⟨(L : X → Y), linearMap_isBoundedRepresentative X Y L⟩

/-- The canonical bounded-linear-map-to-jet linear map, HPS (3.3), p. 29. -/
def linearJet : (X →L[ℝ] Y) →ₗ[ℝ] BoundedJet X Y where
  toFun := fun L => jetClass X Y (linearRepresentative X Y L)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl


end HolomorphicAnosov.BoundedLipschitzJets

