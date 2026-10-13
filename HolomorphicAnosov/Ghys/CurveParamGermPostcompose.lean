import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import HolomorphicAnosov.Ghys.CurvePostcomposeAdmissible

/-! Biholomorphic postcomposition of admissible curve germs. (Ghys, Lemma 3.2, p.591) -/

open scoped Topology _root_.Topology Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov.Ghys
universe u v
variable {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
variable {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]
variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L']

/-- The admissible curve germ obtained by postcomposition with a biholomorphism. (Ghys, p.591) -/
def curveParamGermPostcompose
    (T : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) L L' ∞)
    (γ : CurveParamGerm L) : CurveParamGerm L' :=
  ⟨γ.1.map (T : L → L'), curve_postcompose_admissible T γ⟩


end HolomorphicAnosov.Ghys
