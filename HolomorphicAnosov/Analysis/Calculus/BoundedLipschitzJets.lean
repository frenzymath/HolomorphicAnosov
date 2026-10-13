import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LittleORepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.ContinuousRepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.DifferentiableRepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LinearRepresentativeBound
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.DifferentiableContinuous
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.DifferentiableRange
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LinearJetNorm
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LinearJetSubtypeSurjective
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.BoundedJetsCompleteAnnular
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.ContinuousJetsClosedAnnular
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.DifferentiableClosed

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace X] [CompleteSpace Y]

omit [CompleteSpace X] in
/-- HPS Theorem (3.3), printed pp.27–29. The first conclusion is proved by
annular selection; continuous jets use adjacent radial interpolation and closed-annulus
pasting away from zero, then a slope bound gives continuity at zero. The radii are
chosen inside the open continuity neighborhoods of the adjacent representatives,
as in the printed local-domain construction. Finite-radius errors are 2^(-n) instead of 1/n; both
tend to zero. The final conclusions are the imported HPS derivative and operator-norm
identification. Zero domain and codomain are included without dividing by ‖x‖. -/
theorem bounded_lipschitz_jets :
    CompleteSpace (BoundedJet X Y) ∧
    @IsClosed (BoundedJet X Y)
      (inferInstance : NormedAddCommGroup (BoundedJet X Y)).toMetricSpace.toUniformSpace.toTopologicalSpace
      (continuousJets X Y : Set (BoundedJet X Y)) ∧
    @IsClosed (BoundedJet X Y)
      (inferInstance : NormedAddCommGroup (BoundedJet X Y)).toMetricSpace.toUniformSpace.toTopologicalSpace
      (differentiableJets X Y : Set (BoundedJet X Y)) ∧
    differentiableJets X Y ≤ continuousJets X Y ∧
    differentiableJets X Y = LinearMap.range (linearJet X Y) ∧
    ∃ e : (X →L[ℝ] Y) ≃ₗᵢ[ℝ] ↥(differentiableJets X Y),
      ∀ L : X →L[ℝ] Y, (e L : BoundedJet X Y) = linearJet X Y L := by
  refine ⟨boundedJets_complete_annular X Y, continuousJets_closed_annular X Y, differentiableJets_isClosed X Y,
    differentiableJets_le_continuousJets X Y,
    differentiableJets_eq_linearJet_range X Y, ?_⟩
  let iso : (X →L[ℝ] Y) →ₗᵢ[ℝ] ↥(differentiableJets X Y) :=
    LinearIsometry.mk (linearJetSubtype X Y) (by
      intro L
      change ‖linearJet X Y L‖ = ‖L‖
      exact linearJet_norm_eq_opNorm X Y L)
  refine ⟨LinearIsometryEquiv.ofSurjective iso (linearJetSubtype_surjective X Y), ?_⟩
  intro L
  rfl

end HolomorphicAnosov.BoundedLipschitzJets

