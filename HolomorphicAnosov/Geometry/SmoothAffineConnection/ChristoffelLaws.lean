import HolomorphicAnosov.Geometry.SmoothAffineConnection.TangentCoefficientMulFunction
import HolomorphicAnosov.Geometry.SmoothAffineConnection.CoordinateCoefficientMulFunction

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Smooth Christoffel coordinate formulas and restriction compatibility imply the affine connection laws. Source: Andrews, Lecture 8, Definition 8.2.1, p.72, and Proposition 8.3.1, p.74. -/
theorem isSmoothAffineConnectionOperator_of_christoffel
    (cov : LocalBilinearCovariantDerivative E M)
    (hr : cov.RespectsRestriction) (hc : cov.HasSmoothChristoffelSymbols) :
    IsSmoothAffineConnectionOperator cov := by
  classical
  refine ⟨hr, ?_, ?_⟩
  · intro U X Y f hf
    ext p
    let b := Module.finBasis ℝ E
    let c := chartAt E p
    have hp : p ∈ c.source := mem_chart_source E p
    obtain ⟨Γ, _, hΓ⟩ := hc U (Module.finrank ℝ E) b c
      (chart_mem_maximalAtlas p)
    apply (mdifferentiable_chart (I := 𝓘(ℝ, E)) p).mfderiv_injective hp
    apply (NormedSpace.fromTangentSpace (c p)).injective
    apply b.repr.injective
    ext k
    change (cov U (X.mulFunction f hf) Y).tangentCoefficient b c p k =
      ((cov U X Y).mulFunction f hf).tangentCoefficient b c p k
    rw [LocalSmoothVectorField.tangentCoefficient_mulFunction,
      hΓ (X.mulFunction f hf) Y p hp k, hΓ X Y p hp k]
    simp_rw [LocalSmoothVectorField.tangentCoefficient_mulFunction]
    simp only [mul_assoc, Finset.mul_sum, mul_add]
  · intro U X Y f hf p
    let b := Module.finBasis ℝ E
    let c := chartAt E p
    have hp : p ∈ c.source := mem_chart_source E p
    obtain ⟨Γ, _, hΓ⟩ := hc U (Module.finrank ℝ E) b c
      (chart_mem_maximalAtlas p)
    apply (mdifferentiable_chart (I := 𝓘(ℝ, E)) p).mfderiv_injective hp
    apply (NormedSpace.fromTangentSpace (c p)).injective
    apply b.repr.injective
    ext k
    change (cov U X (Y.mulFunction f hf)).tangentCoefficient b c p k =
      b.repr (mvfderiv 𝓘(ℝ, E) c p
        (f p • cov U X Y p + mvfderiv 𝓘(ℝ, E) f p (X p) • Y p)) k
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
    change (cov U X (Y.mulFunction f hf)).tangentCoefficient b c p k =
      f p * (cov U X Y).tangentCoefficient b c p k +
        mvfderiv 𝓘(ℝ, E) f p (X p) * Y.tangentCoefficient b c p k
    rw [hΓ X (Y.mulFunction f hf) p hp k, hΓ X Y p hp k]
    simp_rw [LocalSmoothVectorField.tangentCoefficient_mulFunction]
    have hcs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm (c p) :=
      (contMDiffOn_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas p)).contMDiffAt
        (c.open_target.mem_nhds (c.map_source hp))
    have hfc : DifferentiableAt ℝ (fun z ↦ f (c.symm z)) (c p) := by
      have h := (hf (c.symm (c p))).comp (c p) hcs
      exact (contMDiffAt_iff_contDiffAt.mp h).differentiableAt (by simp)
    have hYt : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun q ↦ mvfderiv 𝓘(ℝ, E) c q (Y q)) p := by
      have h := (contMDiffAt_section p).mp (Y.contMDiff p)
      apply h.congr_of_eventuallyEq
      filter_upwards [c.open_source.mem_nhds hp] with q hq
      change mvfderiv 𝓘(ℝ, E) c q (Y q) =
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p ⟨q, Y q⟩).2
      rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
        (R := ℝ) _ hq, TangentBundle.continuousLinearMapAt_trivializationAt hq]
      rfl
    have hYc : DifferentiableAt ℝ (Y.coordinateCoefficient b c k) (c p) := by
      have hcomp := hYt.comp_of_eq hcs (c.left_inv hp)
      have hcoord := (b.coord k).toContinuousLinearMap.contMDiffAt.comp (c p) hcomp
      exact (contMDiffAt_iff_contDiffAt.mp hcoord).differentiableAt (by simp)
    have hprod := fderiv_fun_mul hfc hYc
    have hprod' : fderiv ℝ ((Y.mulFunction f hf).coordinateCoefficient b c k) (c p) =
        f p • fderiv ℝ (Y.coordinateCoefficient b c k) (c p) +
          Y.tangentCoefficient b c p k • fderiv ℝ (fun z ↦ f (c.symm z)) (c p) := by
      have hcoef : (Y.mulFunction f hf).coordinateCoefficient b c k =
          fun z ↦ f (c.symm z) * Y.coordinateCoefficient b c k z := by
        funext z
        exact LocalSmoothVectorField.coordinateCoefficient_mulFunction b c Y f hf k z
      rw [hcoef]
      have heval : Y.coordinateCoefficient b c k (c p) = Y.tangentCoefficient b c p k := by
        change Y.tangentCoefficient b c (c.symm (c p)) k = _
        rw [c.left_inv hp]
      simpa only [c.left_inv hp, heval] using hprod
    rw [hprod']
    simp only [add_apply, smul_apply, smul_eq_mul]
    have hchain : fderiv ℝ (fun z ↦ f (c.symm z)) (c p)
        (mvfderiv 𝓘(ℝ, E) c p (X p)) = mvfderiv 𝓘(ℝ, E) f p (X p) := by
      have heq : (fun q ↦ f (c.symm (c q))) =ᶠ[𝓝 p] f := by
        filter_upwards [c.open_source.mem_nhds hp] with q hq
        rw [c.left_inv hq]
      have hcomp := mvfderiv_comp_apply p
        (hfc.mdifferentiableAt)
        ((mdifferentiable_chart (I := 𝓘(ℝ, E)) p).mdifferentiableAt hp) (X p)
      rw [mvfderiv_eq_fderiv] at hcomp
      have hderiv := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ))
      change fderiv ℝ (fun z ↦ f (c.symm z)) (c p)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c p (X p)) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p (X p)
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun q ↦ f (c.symm (c q))) p (X p) = _ at hcomp
      rw [hderiv] at hcomp
      exact hcomp.symm
    have hsum : ∑ i, X.tangentCoefficient b c p i *
        fderiv ℝ (fun z ↦ f (c.symm z)) (c p) (b i) =
        mvfderiv 𝓘(ℝ, E) f p (X p) := by
      rw [← hchain]
      conv_rhs => rw [← b.sum_repr (mvfderiv 𝓘(ℝ, E) c p (X p))]
      simp only [map_sum, map_smul, smul_eq_mul, LocalSmoothVectorField.tangentCoefficient]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hfirst : ∑ i, X.tangentCoefficient b c p i *
        (f p * fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i)) =
        f p * ∑ i, X.tangentCoefficient b c p i *
          fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i) := by
      rw [Finset.mul_sum]
      congr 1
      ext i
      ring
    have hsecond : ∑ i, X.tangentCoefficient b c p i *
        (Y.tangentCoefficient b c p k *
          fderiv ℝ (fun z ↦ f (c.symm z)) (c p) (b i)) =
        mvfderiv 𝓘(ℝ, E) f p (X p) * Y.tangentCoefficient b c p k := by
      rw [← hsum, Finset.sum_mul]
      congr 1
      ext i
      ring
    have hchristoffel : ∑ i, ∑ j, X.tangentCoefficient b c p i *
        (f p * Y.tangentCoefficient b c p j) * Γ i j k p =
        f p * ∑ i, ∑ j, X.tangentCoefficient b c p i *
          Y.tangentCoefficient b c p j * Γ i j k p := by
      simp_rw [Finset.mul_sum]
      congr 1
      ext i
      congr 1
      ext j
      ring
    rw [hfirst, hsecond, hchristoffel]
    ring

end

end HolomorphicAnosov

