import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeContinuity

noncomputable section
open scoped ContDiff
namespace HolomorphicAnosov

/-- All spatial derivatives of the two rational slope actions exist wherever the horizontal block is invertible (HPS pp.33–35 and 55–58). -/
theorem parameter_graph_slope_contDiffAt
    {Z X Y U V : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ∞ω) (z : Z)
    (A : Z → X →L[ℝ] U) (B : Z → Y →L[ℝ] U)
    (C : Z → X →L[ℝ] V) (D : Z → Y →L[ℝ] V)
    (hA : ContDiffAt ℝ n A z) (hB : ContDiffAt ℝ n B z)
    (hC : ContDiffAt ℝ n C z) (hD : ContDiffAt ℝ n D z) :
    (∀ P : Z → X →L[ℝ] Y, ContDiffAt ℝ n P z →
      (A z + (B z).comp (P z)).IsInvertible →
      ContDiffAt ℝ n (fun z ↦ (C z + (D z).comp (P z)).comp
        (ContinuousLinearMap.inverse (A z + (B z).comp (P z)))) z) ∧
    (∀ P : Z → V →L[ℝ] U, ContDiffAt ℝ n P z →
      (A z - (P z).comp (C z)).IsInvertible →
      ContDiffAt ℝ n (fun z ↦ (ContinuousLinearMap.inverse (A z - (P z).comp (C z))).comp
        ((P z).comp (D z) - B z)) z) := by
  constructor
  · intro P hP hinv
    have hi0 : ContDiffAt ℝ n (ContinuousLinearMap.inverse : (X →L[ℝ] U) → (U →L[ℝ] X))
        _ := hinv.contDiffAt_map_inverse
    have hI : ContDiffAt ℝ n (fun z ↦ ContinuousLinearMap.inverse (A z + (B z).comp (P z))) z :=
      ContDiffAt.fun_comp z hi0 (hA.add (hB.clm_comp hP))
    exact (hC.add (hD.clm_comp hP)).clm_comp hI
  · intro P hP hinv
    have hi0 : ContDiffAt ℝ n (ContinuousLinearMap.inverse : (X →L[ℝ] U) → (U →L[ℝ] X))
        _ := hinv.contDiffAt_map_inverse
    have hI : ContDiffAt ℝ n (fun z ↦ ContinuousLinearMap.inverse (A z - (P z).comp (C z))) z :=
      ContDiffAt.fun_comp z hi0 (hA.sub (hP.clm_comp hC))
    exact hI.clm_comp ((hP.clm_comp hD).sub hB)

end HolomorphicAnosov
