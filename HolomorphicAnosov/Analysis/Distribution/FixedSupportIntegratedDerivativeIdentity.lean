import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-!
# Derivatives of a fixed-support parameter integral

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Lemma 6.8,
pp.71–73. The parameter measure restricted to the integration set is finite.

The former statement for arbitrary measures was false. For scalar parameter p
and spatial variable y, take compactly supported smooth cutoffs χ and ρ equal
to one near zero and β(p,y) = χ(p)(p + y p²)ρ(y). Put atoms at p=1/n with
weights sqrt(n). Each nonzero spatial slice has divergent norm integral, so
its totalized Bochner integral is zero. At y=0 its spatial derivative has
positive finite integral (the tail is the convergent series n^(-3/2)). Thus
differentiation cannot commute with that integral. Finite measure on J excludes
this example and holds for the compact parameter support in the caller.
-/

set_option backward.isDefEq.respectTransparency false in
/-- Every spatial derivative commutes with integration over a finite-measure parameter set.
Source: Dyatlov Lemma 6.8, pp.71–73.

Write Dᵢ(p,y) for the i-th spatial derivative of the supported test Ψ(p).
The jet formula expresses Dᵢ as a fixed continuous linear map applied to the
joint derivative of β. Consequently Dᵢ is smooth and compactly supported.
Its norm and its first joint derivative norm have global constant bounds;
finite parameter measure makes these bounds integrable. Differentiation under
the integral therefore applies to y ↦ ∫ Dᵢ(p,y). Induct on i: at order zero
the jet formula identifies Ψ(p)(y) with β(p,y); at the successor step the
currying linear isomorphism identifies the derivative of Dᵢ with Dᵢ₊₁ and
commutes with the Bochner integral. Empty supports, zero measure, and
zero-dimensional parameter or spatial spaces require no separate case. -/
theorem fixed_support_integrated_derivative_identity
    {m k : ℕ} (J : Set (EuclideanSpace ℝ (Fin k)))
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure (μ.restrict J)]
    (Kc : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin m)))
    (β : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) → ℂ)
    (η₀ : EuclideanSpace ℝ (Fin m) → ℂ)
    (Ψ : EuclideanSpace ℝ (Fin k) →
      ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ Kc)
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m))
    (hβsmooth : ContDiff ℝ ∞ β)
    (hβsupport : HasCompactSupport β)
    (hηeq : ∀ y, η₀ y = ∫ p in J, β (p, y) ∂μ)
    (hJetFormula : ∀ i p y,
      iteratedFDeriv ℝ i (Ψ p) y =
        (iteratedFDeriv ℝ i β (p, y)).compContinuousLinearMap (fun _ ↦
          L)) :
    ∀ i y, iteratedFDeriv ℝ i η₀ y =
      ∫ p in J, iteratedFDeriv ℝ i (Ψ p) y ∂μ := by
  let D (i : ℕ) (z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) :=
    iteratedFDeriv ℝ i (Ψ z.1) z.2
  have hDeq (i : ℕ) : D i =
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (F := ℂ) (fun _ : Fin i ↦ L)) ∘ iteratedFDeriv ℝ i β := by
    funext z
    exact hJetFormula i z.1 z.2
  have hDsmooth (i : ℕ) : ContDiff ℝ ∞ (D i) := by
    rw [hDeq]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (F := ℂ) (fun _ : Fin i ↦ L)).contDiff.comp
        (hβsmooth.iteratedFDeriv_right (m := ∞) (i := i) (by simp))
  have hDcompact (i : ℕ) : HasCompactSupport (D i) := by
    rw [hDeq]
    exact (hβsupport.iteratedFDeriv i).comp_left (map_zero _)
  have hDint (i : ℕ) (y : EuclideanSpace ℝ (Fin m)) :
      Integrable (fun p ↦ D i (p, y)) (μ.restrict J) := by
    obtain ⟨C, hC⟩ := (hDsmooth i).continuous.bounded_above_of_compact_support (hDcompact i)
    exact (integrable_const C).mono'
      ((hDsmooth i).continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p ↦ hC (p, y))
  have hDderiv (i : ℕ) (y : EuclideanSpace ℝ (Fin m)) :
      HasFDerivAt (fun y ↦ ∫ p in J, D i (p, y) ∂μ)
        (∫ p in J, fderiv ℝ (iteratedFDeriv ℝ i (Ψ p)) y ∂μ) y := by
    have : SecondCountableTopologyEither (EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin m) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ EuclideanSpace ℝ (Fin m)) ℂ) :=
      ⟨Or.inl inferInstance⟩
    let R : EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) :=
      ContinuousLinearMap.inr ℝ _ _
    have hdf := (hDsmooth i).continuous_fderiv (by simp)
    obtain ⟨C, hC⟩ := hdf.bounded_above_of_compact_support
      ((hDcompact i).fderiv (𝕜 := ℝ))
    have hraw : HasFDerivAt (fun y ↦ ∫ p in J, D i (p, y) ∂μ)
        (∫ p in J, (fderiv ℝ (D i) (p, y)).comp R ∂μ) y := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun y p ↦ D i (p, y))
        (F' := fun y p ↦ (fderiv ℝ (D i) (p, y)).comp R)
        (μ := μ.restrict J) (s := univ) (bound := fun _ ↦ C) Filter.univ_mem
      · exact Filter.Eventually.of_forall (fun y ↦ (hDint i y).aestronglyMeasurable)
      · exact hDint i y
      · exact ((hdf.comp (continuous_id.prodMk continuous_const)).clm_comp
          continuous_const).aestronglyMeasurable
      · apply Filter.Eventually.of_forall
        intro p y _
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_of_le_one_right (norm_nonneg _)
            (ContinuousLinearMap.norm_inr_le_one ℝ _ _)).trans (hC (p, y)))
      · exact integrable_const C
      · apply Filter.Eventually.of_forall
        intro p y _
        exact (((hDsmooth i).differentiable (by simp) (p, y)).hasFDerivAt).comp y
          ((hasFDerivAt_const p y).prodMk (hasFDerivAt_id y))
    have heq (p : EuclideanSpace ℝ (Fin k)) :
        (fderiv ℝ (D i) (p, y)).comp R =
          fderiv ℝ (iteratedFDeriv ℝ i (Ψ p)) y := by
      symm
      exact ((((hDsmooth i).differentiable (by simp) (p, y)).hasFDerivAt).comp y
        ((hasFDerivAt_const p y).prodMk (hasFDerivAt_id y))).fderiv
    simpa only [heq] using hraw
  intro i
  induction i with
  | zero =>
    intro y
    ext v
    rw [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.integral_apply (hDint 0 y)]
    rw [hηeq]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro p
    have h := congrArg (fun T ↦ T (fun i ↦ Fin.elim0 i)) (hJetFormula 0 p y)
    simpa [D] using h.symm
  | succ i ih =>
    intro y
    let curry := continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (i + 1) ↦ EuclideanSpace ℝ (Fin m)) ℂ
    have hfun : iteratedFDeriv ℝ i η₀ = fun y ↦ ∫ p in J, D i (p, y) ∂μ :=
      funext ih
    change curry.symm (fderiv ℝ (iteratedFDeriv ℝ i η₀) y) = _
    rw [hfun, (hDderiv i y).fderiv]
    change curry.symm (∫ p in J, curry (D (i + 1) (p, y)) ∂μ) = _
    have hcomm := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
      (Fₗ := EuclideanSpace ℝ (Fin m) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ EuclideanSpace ℝ (Fin m)) ℂ)
      curry.toContinuousLinearEquiv.toContinuousLinearMap (hDint (i + 1) y)
    change curry.symm (∫ p in J, curry.toContinuousLinearEquiv.toContinuousLinearMap
      (D (i + 1) (p, y)) ∂μ) = _
    rw [hcomm]
    exact curry.symm_apply_apply _

end HolomorphicAnosov.Analysis

