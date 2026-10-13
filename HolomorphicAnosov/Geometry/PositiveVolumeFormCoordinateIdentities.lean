import HolomorphicAnosov.Geometry.Manifold.OrientedRealTopForm
import HolomorphicAnosov.Geometry.Manifold.SmoothPositiveRealVolumeForm
import HolomorphicAnosov.Geometry.Manifold.VolumeCoordinateConditions
import HolomorphicAnosov.Geometry.Manifold.RealVolumeJacobian
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Coordinate coefficients of top forms obey determinant transition and pullback formulas. Positive
volume forms have unique smooth positive pullback Jacobians under orientation-preserving
diffeomorphisms. (Demailly, I (1.13), (1.16)–(1.17), pp. 10–11; Zhang, Lemma 4.3, eq. (31), p.
16) -/

open Set _root_.Topology
open scoped Manifold ContDiff

namespace HolomorphicAnosov.VolumePrototype

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (CoordinateSpace n) M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- The selected positive chart has strictly positive density at the selected point. (Demailly, I
§1.C, p. 11) -/
theorem chosenChart_density_pos
    {o : OrientedAtlas (n := n) (M := M)} (ν : PositiveVolumeForm o) (x : M) :
    0 < chartDensity ν.form (chosenChart o x) (chosenChart o x x) := by
  obtain ⟨hchart, hx⟩ := Classical.choose_spec (o.covers x)
  exact ν.positive _ hchart _ ((chosenChart o x).map_source hx)

/-- The scalar function expressing the pullback of a positive volume form as a multiple of itself
equals its Jacobian. (Demailly, I (1.13), p. 10) -/
theorem jacobian_unique_of_pullback
    {o : OrientedAtlas (n := n) (M := M)} (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (j : M → ℝ) (hj : ∀ x, pullback ν.form F x = j x • ν.form x) :
    j = jacobian ν F := by
  funext x
  let φ := chosenChart o x
  have hx : x ∈ φ.source := (Classical.choose_spec (o.covers x)).2
  have hd : chartDensity (pullback ν.form F) φ (φ x) =
      j x * chartDensity ν.form φ (φ x) := by
    unfold chartDensity
    rw [φ.left_inv hx, hj]
    rfl
  change j x = chartDensity (pullback ν.form F) φ (φ x) /
    chartDensity ν.form φ (φ x)
  rw [hd, mul_div_cancel_right₀ _ (ne_of_gt (chosenChart_density_pos ν x))]


/-- Top-degree alternating forms are proportional, with scalar given by evaluation on any tuple
where the denominator is nonzero. (Demailly, I (1.13), p. 10) -/
private theorem top_alternating_eq_ratio_smul
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (b : Module.Basis (Fin n) ℝ E)
    (η ν : ContinuousAlternatingMap ℝ E ℝ (Fin n))
    (v : Fin n → E) (hv : ν v ≠ 0) :
    η = (η v / ν v) • ν := by
  have heval (β : ContinuousAlternatingMap ℝ E ℝ (Fin n)) (w : Fin n → E) :
      β w = β b * b.det w := by
    have h := congrArg (fun f : AlternatingMap ℝ E ℝ (Fin n) ↦ f w)
      (β.toAlternatingMap.eq_smul_basis_det b)
    exact h
  apply ContinuousAlternatingMap.ext
  intro w
  change η w = (η v / ν v) * ν w
  apply (mul_right_cancel₀ hv)
  calc
    η w * ν v = η v * ν w := by
      rw [heval η w, heval ν v, heval η v, heval ν w]
      ring
    _ = ((η v / ν v) * ν w) * ν v := by
      rw [mul_right_comm, div_mul_cancel₀ _ hv]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a positive volume form equals its Jacobian times the original form on each
tangent fibre. (Demailly, I (1.13), p. 10) -/
theorem pullback_eq_jacobian_smul
    {o : OrientedAtlas (n := n) (M := M)} (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (x : M) : pullback ν.form F x = jacobian ν F x • ν.form x := by
  let φ := chosenChart o x
  have hx : x ∈ φ.source := (Classical.choose_spec (o.covers x)).2
  have hφ : φ.symm (φ x) = x := φ.left_inv hx
  
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
    (tangentSpaceCastModel 𝓘(ℝ, CoordinateSpace n) (φ.symm (φ x))).symm.toLinearEquiv
  have h := top_alternating_eq_ratio_smul b
    (pullback ν.form F (φ.symm (φ x))) (ν.form (φ.symm (φ x)))
    (fun i ↦ mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) φ.symm (φ x)
      ((NormedSpace.fromTangentSpace (φ x)).symm (EuclideanSpace.basisFun (Fin n) ℝ i)))
    (ne_of_gt (chosenChart_density_pos ν x))
  change pullback ν.form F (φ.symm (φ x)) = jacobian ν F x • ν.form (φ.symm (φ x)) at h
  rw [hφ] at h
  exact h

/-- The pullback density in any chart equals the Jacobian times the original density. (Demailly, I
(1.13), p. 10) -/
theorem chartDensity_pullback_eq_jacobian_mul
    {o : OrientedAtlas (n := n) (M := M)} (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (φ : OpenPartialHomeomorph M (CoordinateSpace n)) (z : CoordinateSpace n) :
    chartDensity (pullback ν.form F) φ z =
      jacobian ν F (φ.symm z) * chartDensity ν.form φ z := by
  unfold chartDensity
  rw [pullback_eq_jacobian_smul]
  rfl

/-- The Jacobian equals the pullback-to-original density ratio in every positive source chart
containing the point. (Demailly, I (1.13), §1.C, pp. 10–11) -/
theorem jacobian_eq_chartDensity_ratio
    {o : OrientedAtlas (n := n) (M := M)} (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (φ : OpenPartialHomeomorph M (CoordinateSpace n)) (hφ : φ ∈ o.charts)
    (x : M) (hx : x ∈ φ.source) :
    jacobian ν F x = chartDensity (pullback ν.form F) φ (φ x) /
      chartDensity ν.form φ (φ x) := by
  rw [chartDensity_pullback_eq_jacobian_mul, φ.left_inv hx]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (ν.positive φ hφ (φ x) (φ.map_source hx)))).symm


set_option backward.isDefEq.respectTransparency false in
/-- Precomposing a top alternating form with a linear endomorphism multiplies its basis coefficient
by the signed determinant. (Demailly, I (1.13), p. 10) -/
private theorem coordinate_top_form_comp_det
    (η : ContinuousAlternatingMap ℝ (CoordinateSpace n) ℝ (Fin n))
    (T : CoordinateSpace n →L[ℝ] CoordinateSpace n) :
    η (fun i ↦ T (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      η (EuclideanSpace.basisFun (Fin n) ℝ) * LinearMap.det T.toLinearMap := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have h := congrArg (fun f : AlternatingMap ℝ (CoordinateSpace n) ℝ (Fin n) ↦
    f (T.toLinearMap ∘ b)) (η.toAlternatingMap.eq_smul_basis_det b)
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Module.Basis.det_comp,
    Module.Basis.det_self, mul_one] at h
  simpa [b, Function.comp_def] using h

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a top form after a smooth map from the coordinate model equals its target-chart
density times the signed determinant of the coordinate derivative. (Demailly, I (1.13), p. 10) -/
private theorem chartDensity_of_coordinate_map
    (η : TopForm n M) (H : CoordinateSpace n → M)
    (ψ : OpenPartialHomeomorph M (CoordinateSpace n))
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (z : CoordinateSpace n)
    (hH : ContMDiffAt 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) ∞ H z)
    (hz : H z ∈ ψ.source) :
    η (H z) (fun i ↦ mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) H z
      ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i))) =
      chartDensity η ψ (ψ (H z)) *
        LinearMap.det (fderiv ℝ (fun w ↦ ψ (H w)) z).toLinearMap := by
  have hψat := contMDiffAt_of_mem_maximalAtlas hψ hz
  have hψinv := contMDiffAt_symm_of_mem_maximalAtlas hψ (ψ.map_source hz)
  have hcoord := hψat.comp z hH
  have hevent : (ψ.symm ∘ (ψ ∘ H)) =ᶠ[nhds z] H := by
    filter_upwards [hH.continuousAt.eventually (ψ.open_source.mem_nhds hz)] with w hw
    exact ψ.left_inv hw
  have hderiv := hevent.mfderiv_eq (I := 𝓘(ℝ, CoordinateSpace n))
    (I' := 𝓘(ℝ, CoordinateSpace n))
  rw [mfderiv_comp z (hψinv.mdifferentiableAt (by simp))
    (hcoord.mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at hderiv
  let β : ContinuousAlternatingMap ℝ (CoordinateSpace n) ℝ (Fin n) :=
    (η (ψ.symm (ψ (H z)))).compContinuousLinearMap
      ((mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) ψ.symm (ψ (H z))).comp
        (NormedSpace.fromTangentSpace (ψ (H z))).symm.toContinuousLinearMap)
  have h := coordinate_top_form_comp_det β (fderiv ℝ (fun w ↦ ψ (H w)) z)
  change η (ψ.symm (ψ (H z)))
      (fun i ↦ mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) ψ.symm (ψ (H z))
        ((fderiv ℝ (fun w ↦ ψ (H w)) z) (EuclideanSpace.basisFun (Fin n) ℝ i))) =
      chartDensity η ψ (ψ (H z)) *
        LinearMap.det (fderiv ℝ (fun w ↦ ψ (H w)) z).toLinearMap at h
  rw [ψ.left_inv hz] at h
  convert h using 1
  apply congrArg (η (H z))
  funext i
  exact (congrArg (fun L ↦ L (EuclideanSpace.basisFun (Fin n) ℝ i)) hderiv).symm


omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- Inverse-chart coefficients transform by the signed determinant of the coordinate transition.
(Demailly, I (1.13), p. 10) -/
theorem chartDensity_transition
    (η : TopForm n M) (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n))
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (z : CoordinateSpace n) (hz : z ∈ φ.target) (hψz : φ.symm z ∈ ψ.source) :
    chartDensity η φ z = chartDensity η ψ (ψ (φ.symm z)) * transitionDet φ ψ z := by
  exact chartDensity_of_coordinate_map η φ.symm ψ hψ z
    (contMDiffAt_symm_of_mem_maximalAtlas hφ hz) hψz

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
/-- The pullback coefficient equals the target coefficient times the signed determinant of the
coordinate derivative. (Demailly, I (1.13), p. 10) -/
theorem chartDensity_pullback_coordinate
    (η : TopForm n M)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n))
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (z : CoordinateSpace n) (hz : z ∈ φ.target) (hψz : F (φ.symm z) ∈ ψ.source) :
    chartDensity (pullback η F) φ z =
      chartDensity η ψ (ψ (F (φ.symm z))) *
        LinearMap.det (fderiv ℝ (fun w ↦ ψ (F (φ.symm w))) z).toLinearMap := by
  have hφinv := contMDiffAt_symm_of_mem_maximalAtlas hφ hz
  have hF : ContMDiffAt 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) ∞ F
      (φ.symm z) := F.contMDiff_toFun (φ.symm z)
  have h := chartDensity_of_coordinate_map η (F ∘ φ.symm) ψ hψ z
    (hF.comp z hφinv) hψz
  rw [mfderiv_comp z (hF.mdifferentiableAt (by simp))
    (hφinv.mdifferentiableAt (by simp))] at h
  exact h

/-- Positive volume forms satisfy the density overlap law. (Demailly, I (1.13), §1.C, pp. 10–11) -/
theorem positiveVolumeForm_densityOverlapLaw
    (o : OrientedAtlas (n := n) (M := M)) (ν : PositiveVolumeForm o) :
    DensityOverlapLaw o ν := by
  intro φ hφ ψ hψ z hz hψz
  exact chartDensity_transition ν.form φ ψ (o.compatible φ hφ) (o.compatible ψ hψ)
    z hz hψz

/-- The Jacobian is the target density times the coordinate derivative determinant divided by the
source density in every positive chart pair. (Demailly, I (1.13), pp. 10–11) -/
theorem jacobian_eq_positive_chart_pair
    {o : OrientedAtlas (n := n) (M := M)} (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n))
    (hφ : φ ∈ o.charts) (hψ : ψ ∈ o.charts)
    (x : M) (hx : x ∈ φ.source) (hFx : F x ∈ ψ.source) :
    jacobian ν F x = chartDensity ν.form ψ (ψ (F x)) *
      LinearMap.det (fderiv ℝ (fun w ↦ ψ (F (φ.symm w))) (φ x)).toLinearMap /
        chartDensity ν.form φ (φ x) := by
  rw [jacobian_eq_chartDensity_ratio ν F φ hφ x hx,
    chartDensity_pullback_coordinate ν.form F φ ψ (o.compatible φ hφ)
      (o.compatible ψ hψ) (φ x) (φ.map_source hx) (by simpa only [φ.left_inv hx] using hFx),
    φ.left_inv hx]

/-- Orientation-preserving diffeomorphisms have strictly positive Jacobians with respect to a
positive volume form. (Demailly, I §1.C, p. 11) -/
theorem jacobian_pos_of_preservesOrientation
    {o : OrientedAtlas (n := n) (M := M)} (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (hF : PreservesOrientation o F) (x : M) : 0 < jacobian ν F x := by
  obtain ⟨φ, hφ, hx⟩ := o.covers x
  obtain ⟨ψ, hψ, hFx⟩ := o.covers (F x)
  rw [jacobian_eq_positive_chart_pair ν F φ ψ hφ hψ x hx hFx]
  exact div_pos (mul_pos (ν.positive ψ hψ _ (ψ.map_source hFx))
    (hF φ hφ ψ hψ (φ x) (φ.map_source hx) (by simpa only [φ.left_inv hx] using hFx)))
    (ν.positive φ hφ _ (φ.map_source hx))


/-- The determinant is a smooth function of coordinate endomorphisms. (Demailly, I §1.C, p. 11) -/
private theorem coordinate_det_contDiff :
    ContDiff ℝ ∞ (fun T : CoordinateSpace n →L[ℝ] CoordinateSpace n ↦
      LinearMap.det T.toLinearMap) := by
  classical
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  simp_rw [← LinearMap.det_toMatrix b, Matrix.det_apply', LinearMap.toMatrix_apply]
  simp only [b, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    ContinuousLinearMap.coe_coe]
  fun_prop


/-- The scalar pullback Jacobian of a smooth diffeomorphism with respect to a positive volume form
is smooth. (Demailly, I (1.13), pp. 10–11) -/
theorem contMDiff_jacobian
    {o : OrientedAtlas (n := n) (M := M)} (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞) :
    ContMDiff 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, ℝ) ∞ (jacobian ν F) := by
  intro x
  obtain ⟨φ, hφ, hx⟩ := o.covers x
  obtain ⟨ψ, hψ, hFx⟩ := o.covers (F x)
  have hFx' : F (φ.symm (φ x)) ∈ ψ.source := by simpa only [φ.left_inv hx] using hFx
  let T : CoordinateSpace n → CoordinateSpace n := fun z ↦ ψ (F (φ.symm z))
  have hT : ContDiffAt ℝ ∞ T (φ x) := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact ((contMDiffAt_of_mem_maximalAtlas (o.compatible ψ hψ) hFx').comp _
      (F.contMDiff_toFun _)).comp _
        (contMDiffAt_symm_of_mem_maximalAtlas (o.compatible φ hφ) (φ.map_source hx))
  have hdT : ContDiffAt ℝ ∞ (fderiv ℝ T) (φ x) := hT.fderiv_right (by simp)
  have hdet : ContDiffAt ℝ ∞
      (fun z ↦ LinearMap.det (fderiv ℝ T z).toLinearMap) (φ x) :=
    coordinate_det_contDiff.contDiffAt.comp _ hdT
  have htarget : T (φ x) ∈ ψ.target := ψ.map_source hFx'
  have hnum : ContDiffAt ℝ ∞ (fun z ↦ chartDensity ν.form ψ (T z)) (φ x) :=
    ((ν.smooth ψ (o.compatible ψ hψ)).contDiffAt (ψ.open_target.mem_nhds htarget)).comp _ hT
  have hden : ContDiffAt ℝ ∞ (chartDensity ν.form φ) (φ x) :=
    (ν.smooth φ (o.compatible φ hφ)).contDiffAt
      (φ.open_target.mem_nhds (φ.map_source hx))
  have hratio := (hnum.mul hdet).div hden
    (ne_of_gt (ν.positive φ hφ _ (φ.map_source hx)))
  have hs := hratio.comp_contMDiffAt
    (contMDiffAt_of_mem_maximalAtlas (o.compatible φ hφ) hx)
  apply hs.congr_of_eventuallyEq
  filter_upwards [φ.open_source.mem_nhds hx,
    F.continuous.continuousAt.eventually (ψ.open_source.mem_nhds hFx)] with y hy hFy
  simpa only [Function.comp_apply, Pi.div_apply, T, φ.left_inv hy] using
    jacobian_eq_positive_chart_pair ν F φ ψ hφ hψ y hy hFy


/-- Top-form coefficients transform by coordinate derivative determinants. A positive volume form
has a unique smooth positive pullback Jacobian under every orientation-preserving
diffeomorphism. (Demailly, I (1.13), (1.16)–(1.17), pp. 10–11; Zhang, Lemma 4.3, eq. (31), p.
16) -/
theorem positiveVolumeForm_coordinateIdentities
    (o : OrientedAtlas (n := n) (M := M)) (ν : PositiveVolumeForm o) :
    (∀ (η : TopForm n M) (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n)),
      φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
      ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
      ∀ z ∈ φ.target, φ.symm z ∈ ψ.source →
        chartDensity η φ z = chartDensity η ψ (ψ (φ.symm z)) * transitionDet φ ψ z) ∧
    (∀ (η : TopForm n M)
      (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
      (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n)),
      φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
      ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
      ∀ z ∈ φ.target, F (φ.symm z) ∈ ψ.source →
        chartDensity (pullback η F) φ z =
          chartDensity η ψ (ψ (F (φ.symm z))) *
            LinearMap.det (fderiv ℝ (fun w ↦ ψ (F (φ.symm w))) z).toLinearMap) ∧
    DensityOverlapLaw o ν ∧
    (∀ (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
      (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n)),
      φ ∈ o.charts → ψ ∈ o.charts → ∀ x ∈ φ.source, F x ∈ ψ.source →
        jacobian ν F x = chartDensity ν.form ψ (ψ (F x)) *
          LinearMap.det (fderiv ℝ (fun w ↦ ψ (F (φ.symm w))) (φ x)).toLinearMap /
            chartDensity ν.form φ (φ x)) ∧
    (∀ (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞),
      PreservesOrientation o F →
        ContMDiff 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, ℝ) ∞ (jacobian ν F) ∧
        (∀ x, 0 < jacobian ν F x) ∧
        (∀ x, pullback ν.form F x = jacobian ν F x • ν.form x) ∧
        (∀ j : M → ℝ, (∀ x, pullback ν.form F x = j x • ν.form x) →
          j = jacobian ν F)) := by
  refine ⟨fun η φ ψ hφ hψ z hz hψz ↦ chartDensity_transition η φ ψ hφ hψ z hz hψz,
    fun η F φ ψ hφ hψ z hz hψz ↦ chartDensity_pullback_coordinate η F φ ψ hφ hψ z hz hψz,
    positiveVolumeForm_densityOverlapLaw o ν,
    fun F φ ψ hφ hψ x hx hFx ↦ jacobian_eq_positive_chart_pair ν F φ ψ hφ hψ x hx hFx,
    ?_⟩
  intro F hF
  exact ⟨contMDiff_jacobian ν F, jacobian_pos_of_preservesOrientation ν F hF,
    pullback_eq_jacobian_smul ν F, jacobian_unique_of_pullback ν F⟩


end HolomorphicAnosov.VolumePrototype
