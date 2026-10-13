import HolomorphicAnosov.Geometry.HermitianCoreGramDeterminantChange
import HolomorphicAnosov.Geometry.HermitianVolumePositiveOfChartIdentity
import HolomorphicAnosov.Geometry.HermitianJacobianPairedImage
import HolomorphicAnosov.Geometry.HermitianChartDeterminantReal
import HolomorphicAnosov.Geometry.PositiveRealTangentTopFormScaleInjective
import HolomorphicAnosov.Geometry.HermitianPairedChartFrame
import HolomorphicAnosov.Geometry.HermitianPreferredPairedEvaluation
import HolomorphicAnosov.Geometry.PositiveTopFormScalarSmooth
import HolomorphicAnosov.Geometry.PositiveTopFormBiholomorphPullback

/-! This file constructs the Hermitian metric volume form and its Jacobian under biholomorphisms. (Demailly, VI §4.) -/



open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- The Hermitian metric has its smooth positive real volume for the complex orientation; its coefficient is the real positive complex determinant, its value on every paired unitary frame is one, and every biholomorphism has the unique positive smooth pullback Jacobian with the squared-complex-determinant rule in every pair of unitary frames. (Demailly, VI §4; Zhang, Lemma 4.3.) -/
theorem hermitian_metric_volume_jacobian [IsManifold (complexModel d) ∞ X]
    (h : HermitianTangentMetricCore d X) (hh : IsSmoothHermitianTangentMetric h) :
    IsSmoothPositiveRealTangentTopForm (hermitianMetricPreferredTopForm h) ∧
    (∀ (e : OpenPartialHomeomorph X (ComplexModel d)),
      e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ∀ z ∈ e.target,
        (Matrix.det fun i j => hermitianTangentChartCoefficient h e i j z).im = 0 ∧
        0 < hermitianMetricChartVolumeDensity h e z ∧
        realTangentTopFormChartCoefficient (hermitianMetricPreferredTopForm h) e z =
          hermitianMetricChartVolumeDensity h e z) ∧
    (∀ (x : X) (b : Module.Basis (Fin d) ℂ (TangentSpace (complexModel d) x)),
      (∀ i j, hermitianTangentPairing h x (b i) (b j) = if i = j then 1 else 0) →
      hermitianMetricPreferredTopForm h x (fun i => complexTangentToReal d x
        (if i.2 = 0 then b i.1 else Complex.I • b i.1)) = 1) ∧
    ∀ F : Biholomorph d d X X, ∃ J : X → ℝ,
      ContMDiff (realModel d) (modelWithCornersSelf ℝ ℝ) ∞ J ∧
      (∀ x, 0 < J x) ∧
      realTangentTopFormPullback F (hermitianMetricPreferredTopForm h) =
        realTangentTopFormScale J (hermitianMetricPreferredTopForm h) ∧
      (∀ J' : X → ℝ,
        realTangentTopFormPullback F (hermitianMetricPreferredTopForm h) =
          realTangentTopFormScale J' (hermitianMetricPreferredTopForm h) → J' = J) ∧
      ∀ (x : X)
        (b : Module.Basis (Fin d) ℂ (TangentSpace (complexModel d) x))
        (c : Module.Basis (Fin d) ℂ (TangentSpace (complexModel d) (F x))),
        (∀ i j, hermitianTangentPairing h x (b i) (b j) = if i = j then 1 else 0) →
        (∀ i j, hermitianTangentPairing h (F x) (c i) (c j) = if i = j then 1 else 0) →
        J x = ‖Matrix.det (LinearMap.toMatrix b c
          (mfderiv (complexModel d) (complexModel d) F x).toLinearMap)‖ ^ 2 := by
  have hchart : ∀ (e : OpenPartialHomeomorph X (ComplexModel d)),
      e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      Set.EqOn (realTangentTopFormChartCoefficient (hermitianMetricPreferredTopForm h) e)
        (hermitianMetricChartVolumeDensity h e) e.target := by
    intro e he z hz
    unfold realTangentTopFormChartCoefficient
    rw [show realTangentPairedChartFrame e z =
      (fun i ↦ complexTangentToReal d (e.symm z)
        (if i.2 = 0 then hermitianTangentChartFrame e z i.1
         else Complex.I • hermitianTangentChartFrame e z i.1)) from
      funext (hermitian_paired_chart_frame e he z hz)]
    rw [hermitian_preferred_paired_evaluation]
    rfl
  have hunit : ∀ (x : X) (b : Module.Basis (Fin d) ℂ (TangentSpace (complexModel d) x)),
      (∀ i j, hermitianTangentPairing h x (b i) (b j) = if i = j then 1 else 0) →
      hermitianMetricPreferredTopForm h x (fun i ↦ complexTangentToReal d x
        (if i.2 = 0 then b i.1 else Complex.I • b i.1)) = 1 := by
    intro x b hb
    rw [hermitian_preferred_paired_evaluation]
    have hm : (fun i j ↦ (h x).inner (b j) (b i)) =
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
      ext i j
      exact hb i j
    rw [hm, Matrix.det_one, Complex.one_re]
  have hpositive := hermitian_volume_positive_of_chart_identity h hh hchart
  refine ⟨hpositive, ?_, hunit, ?_⟩
  · intro e he z hz
    exact ⟨hermitian_chart_det_real h e z,
      hermitian_chart_density_pos h e he z hz, hchart e he hz⟩
  · intro F
    suffices hpullpositive : IsSmoothPositiveRealTangentTopForm
        (realTangentTopFormPullback F (hermitianMetricPreferredTopForm h)) by
      obtain ⟨J, hsmooth, hpos, hpull⟩ := positive_topForms_exists_smooth_scalar
        (realTangentTopFormPullback F (hermitianMetricPreferredTopForm h))
        (hermitianMetricPreferredTopForm h) hpullpositive hpositive
      refine ⟨J, hsmooth, hpos, hpull, ?_, ?_⟩
      · intro J' hJ'
        exact positive_topForm_scale_injective _ hpositive (hJ'.symm.trans hpull)
      · intro x b c hb hc
        rw [hermitian_jacobian_eq_native_paired_image h F J hpull x b (hunit x b hb)]
        let D := mfderiv (complexModel d) (complexModel d) F x
        have hpair : (fun i : ComplexPairedIndex d ↦ complexTangentToReal d (F x)
            (D (if i.2 = 0 then b i.1 else Complex.I • b i.1))) =
            (fun i ↦ complexTangentToReal d (F x)
              (if i.2 = 0 then D (b i.1) else Complex.I • D (b i.1))) := by
          funext i
          split_ifs <;> simp only [map_smul]
        change hermitianMetricPreferredTopForm h (F x)
          (fun i ↦ complexTangentToReal d (F x)
            (D (if i.2 = 0 then b i.1 else Complex.I • b i.1))) = _
        rw [hpair, hermitian_preferred_paired_evaluation h (F x) (fun i ↦ D (b i))]
        have hg := hermitian_core_gram_det_change (h (F x)) c (fun i ↦ D (b i))
        have hm : (fun i j ↦ (h (F x)).inner (c j) (c i)) =
            (1 : Matrix (Fin d) (Fin d) ℂ) := by
          ext i j
          exact hc i j
        rw [hm, Matrix.det_one, one_mul] at hg
        have hr := congrArg Complex.re hg
        have hmatrix : (Matrix.of fun i j ↦ c.repr (D (b j)) i) =
            LinearMap.toMatrix b c D.toLinearMap := by
          ext i j
          simp only [Matrix.of_apply, LinearMap.toMatrix_apply]
          rfl
        rw [hmatrix] at hr
        exact hr
    exact positive_topForm_biholomorph_pullback F _ hpositive




end HolomorphicAnosov
