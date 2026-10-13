import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
namespace HolomorphicAnosov

/-- The rational first-jet graph actions are continuous in fixed local bundle charts (HPS, pp.55–58, 62). -/
theorem parameter_graph_slope_continuity
    {Z X Y U V : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Z → X →L[ℝ] U) (B : Z → Y →L[ℝ] U)
    (C : Z → X →L[ℝ] V) (D : Z → Y →L[ℝ] V)
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hD : Continuous D) :
    (∀ P : Z → X →L[ℝ] Y, Continuous P →
      (∀ z, (A z + (B z).comp (P z)).IsInvertible) →
      Continuous (fun z ↦ (C z + (D z).comp (P z)).comp
        (ContinuousLinearMap.inverse (A z + (B z).comp (P z))))) ∧
    (∀ P : Z → V →L[ℝ] U, Continuous P →
      (∀ z, (A z - (P z).comp (C z)).IsInvertible) →
      Continuous (fun z ↦ (ContinuousLinearMap.inverse (A z - (P z).comp (C z))).comp
        ((P z).comp (D z) - B z))) := by
  constructor
  · intro P hP hinv
    have hH : Continuous (fun z ↦ A z + (B z).comp (P z)) := hA.add (hB.clm_comp hP)
    have hI : Continuous (fun z ↦ ContinuousLinearMap.inverse (A z + (B z).comp (P z))) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact ((hinv z).contDiffAt_map_inverse (n := 1)).continuousAt.comp
        (f := fun z ↦ A z + (B z).comp (P z)) hH.continuousAt
    exact (hC.add (hD.clm_comp hP)).clm_comp hI
  · intro P hP hinv
    have hH : Continuous (fun z ↦ A z - (P z).comp (C z)) := hA.sub (hP.clm_comp hC)
    have hI : Continuous (fun z ↦ ContinuousLinearMap.inverse (A z - (P z).comp (C z))) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact ((hinv z).contDiffAt_map_inverse (n := 1)).continuousAt.comp
        (f := fun z ↦ A z - (P z).comp (C z)) hH.continuousAt
    exact hI.clm_comp ((hP.clm_comp hD).sub hB)

end HolomorphicAnosov
