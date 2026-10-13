import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LinearJetNorm

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable [CompleteSpace X] [CompleteSpace Y]

omit [CompleteSpace X] in
/-- HPS Theorem (3.3), p.29: differentiable jets are closed. The operator-to-jet linear map is isometric by the norm equality. Bounded linear maps into complete Y form a complete space, so the isometry has closed range; that range is precisely the differentiable jets. -/
theorem differentiableJets_isClosed :
    @IsClosed (BoundedJet X Y)
      (inferInstance : NormedAddCommGroup (BoundedJet X Y)).toMetricSpace.toUniformSpace.toTopologicalSpace
      (differentiableJets X Y : Set (BoundedJet X Y)) := by
  let : TopologicalSpace (BoundedJet X Y) :=
    (inferInstance : NormedAddCommGroup (BoundedJet X Y)).toMetricSpace.toUniformSpace.toTopologicalSpace
  let iso : (X →L[ℝ] Y) →ₗᵢ[ℝ] BoundedJet X Y :=
    LinearIsometry.mk (linearJet X Y) (linearJet_norm_eq_opNorm X Y)
  rw [differentiableJets_eq_linearJet_range X Y]
  exact iso.isometry.isClosedEmbedding.isClosed_range


end HolomorphicAnosov.BoundedLipschitzJets

