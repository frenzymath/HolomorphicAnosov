import HolomorphicAnosov.Ghys.CurveParamGermPostcompose
import HolomorphicAnosov.Ghys.CurveJetReparametrization

/-! Biholomorphic target postcomposition commutes with rational source reparametrization of
admissible curve germs. (Ghys, Lemma 3.2, p.591) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff

noncomputable section

namespace HolomorphicAnosov.Ghys

universe u v

/-- Target postcomposition commutes with source reparametrization on admissible curve germs. (Ghys,
Lemma 3.2, p.591) -/
theorem curveParamGermPostcompose_reparametrize
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
    {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L']
    (T : Diffeomorph (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) L L' ∞)
    (p : CurveJetReparametrization) (γ : CurveParamGerm L) :
    curveParamGermPostcompose T (curveParamGermReparametrize L p γ) =
      curveParamGermReparametrize L' p (curveParamGermPostcompose T γ) := by
  apply Subtype.ext
  change (γ.1.compTendsto p.apply p.tendsto_zero).map (T : L → L') =
    (γ.1.map (T : L → L')).compTendsto p.apply p.tendsto_zero
  induction γ.1 using Filter.Germ.inductionOn with
  | h f => rfl


end HolomorphicAnosov.Ghys
