import HolomorphicAnosov.Ghys.CurvePostcomposeJetEquivalences
import HolomorphicAnosov.Ghys.JetDynamicsLeafwiseDiffeomorphSmoothnessCore
import HolomorphicAnosov.Ghys.CurveJetAffineData
import Mathlib.Geometry.Manifold.Diffeomorph

namespace HolomorphicAnosov.Ghys

open Set _root_.HolomorphicAnosov.Topology _root_.Topology
open scoped Topology _root_.Topology Manifold ContDiff

universe u v

/-! This file proves smoothness of the fixed-leaf jet postcomposition equivalence in the coefficient atlases. (Ghys, §3) -/
theorem curve_postcompose_jet_diffeomorph_smooth
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
    {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
    [IsManifold 𝓘(ℂ) ∞ L] [IsManifold 𝓘(ℂ) ∞ L']
    [T2Space L] [T2Space L'] [SecondCountableTopology L]
    [SecondCountableTopology L']
    [ChartedSpace (ℂ × ℂ) (CurveJet1 L)]
    [ChartedSpace (ℂ × ℂ) (CurveJet1 L')]
    [ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)]
    [ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L')]
    [IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 L)]
    [IsManifold 𝓘(ℂ, ℂ × ℂ) ∞ (CurveJet1 L')]
    [IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 L)]
    [IsManifold 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ (CurveJet2 L')]
    (hAtlases :
      CurveJetCoefficientAtlases L (inferInstance : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
        (inferInstance : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)) ∧
      CurveJetCoefficientAtlases L' (inferInstance : ChartedSpace (ℂ × ℂ) (CurveJet1 L'))
        (inferInstance : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L')))
    (T : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) L L' ∞) :
    ∃ (E1 : Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
        (CurveJet1 L) (CurveJet1 L') ∞)
      (E2 : Diffeomorph 𝓘(ℂ, (ℂ × ℂ) × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ)
        (CurveJet2 L) (CurveJet2 L') ∞),
      (∀ γ : CurveParamGerm L,
        E1 (curveJet1Class L γ) =
          curveJet1Class L' (curveParamGermPostcompose T γ)) ∧
      (∀ γ : CurveParamGerm L,
        E2 (curveJet2Class L γ) =
          curveJet2Class L' (curveParamGermPostcompose T γ)) := by
  obtain ⟨E1, E2, hE1, hE2⟩ := curve_postcompose_jet_equivalences T
  obtain ⟨h1, h1i, h2, h2i⟩ := curve_postcompose_jet_equiv_contMDiff hAtlases T E1 E2 hE1 hE2
  refine ⟨{ toEquiv := E1, contMDiff_toFun := h1, contMDiff_invFun := h1i },
    { toEquiv := E2, contMDiff_toFun := h2, contMDiff_invFun := h2i }, ?_⟩
  exact ⟨hE1, hE2⟩


end HolomorphicAnosov.Ghys
