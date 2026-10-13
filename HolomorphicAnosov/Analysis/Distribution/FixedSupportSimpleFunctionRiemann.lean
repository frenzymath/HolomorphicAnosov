import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-!
# Fixed-support convergence of sampled parameter integrals

Source: Dyatlov, *Lecture notes for 18.155*, Lemma 6.8, pp. 71–73.

The parameter measure restricted to `J` is finite, and each selected spatial derivative
is uniformly bounded over all parameters and spatial points. The sampling modulus makes
that derivative continuous as a bounded-continuous-function-valued map. Dominated
convergence in this Banach space gives convergence of its sampled integrals in the sup
norm. Continuous point evaluation commutes with the integral, so the integrated derivative
identity identifies the limit. Simple-function fibers identify each sampled integral with
the stated finite weighted sum. A finite supremum preserves convergence to zero.

The former unguarded statement was false, even for finite Lebesgue measure on `J = [0,1]`:
take `Ψ(p) = p • φ` for a nonzero compactly supported smooth function `φ`, and let the
finite-valued sample `q_r` equal `r` on `(0,1/r)` and otherwise approximate the identity
with error at most `1/r` on `[0,1]`. Extend it by finite truncation/quantization outside
`[0,1]`. These samples converge at every fixed point, and `Ψ` is Lipschitz in every fixed
finite seminorm, but the sampled integrals have an extra term tending to `φ`. The added
uniform bound rules out these escaping sample values; the caller obtains it from compact
support of its jointly smooth integrand. No hypothesis is added to the caller's theorem.
-/

/-- The fixed-support convergence conclusion, packaged for the compatibility wrapper. -/
structure FixedSupportSimpleFunctionRiemannData
    {m k : ℕ}
    (J : Set (EuclideanSpace ℝ (Fin k)))
    (μ : Measure (EuclideanSpace ℝ (Fin k)))
    (Kc : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin m)))
    (s : Finset ℕ)
    (Ψ : EuclideanSpace ℝ (Fin k) →
      ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ Kc)
    (ηK : ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ Kc)
    (q : ℕ → SimpleFunc (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))
    (hqpoint : ∀ p, Filter.Tendsto (fun r ↦ q r p) Filter.atTop (𝓝 p))
    (hSampling : ∀ ε > 0, ∃ δ > 0, ∀ p q,
      dist p q < δ →
        s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc) (Ψ p - Ψ q) ≤ ε)
    (hDerivativeIntegral : ∀ i y,
      iteratedFDeriv ℝ i (ηK : EuclideanSpace ℝ (Fin m) → ℂ) y =
        ∫ p in J, iteratedFDeriv ℝ i (Ψ p) y ∂μ) :
    Prop where
  limit :
    Filter.Tendsto
      (fun r ↦ s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc)
        ((∑ p ∈ (q r).range,
          ((μ.restrict J).real ((q r) ⁻¹' {p}) : ℂ) • Ψ p) - ηK))
      Filter.atTop (𝓝 0)

/-- Finite measure and globally bounded derivative coordinates give the sampled integral limit.
Source: Dyatlov Lemma 6.8, pp. 71–73. Apply dominated convergence to each selected derivative
as a bounded continuous function, identify its integral by evaluation, and take the finite
supremum of the resulting errors. This includes empty `s`, zero measure, and empty support. -/
theorem fixed_support_simple_function_riemann_core
    {m k : ℕ}
    (J : Set (EuclideanSpace ℝ (Fin k)))
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure (μ.restrict J)]
    (Kc : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin m)))
    (s : Finset ℕ)
    (Ψ : EuclideanSpace ℝ (Fin k) →
      ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ Kc)
    (ηK : ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ Kc)
    (q : ℕ → SimpleFunc (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))
    (hqpoint : ∀ p, Filter.Tendsto (fun r ↦ q r p) Filter.atTop (𝓝 p))
    (hSampling : ∀ ε > 0, ∃ δ > 0, ∀ p q,
      dist p q < δ →
        s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc) (Ψ p - Ψ q) ≤ ε)
    (hBound : ∀ i ∈ s, ∃ B : ℝ, ∀ p y, ‖iteratedFDeriv ℝ i (Ψ p) y‖ ≤ B)
    (hDerivativeIntegral : ∀ i y,
      iteratedFDeriv ℝ i (ηK : EuclideanSpace ℝ (Fin m) → ℂ) y =
        ∫ p in J, iteratedFDeriv ℝ i (Ψ p) y ∂μ) :
    FixedSupportSimpleFunctionRiemannData J μ Kc s Ψ ηK q hqpoint hSampling
      hDerivativeIntegral := by
  classical
  let ν := μ.restrict J
  let S := fun r ↦ ∑ p ∈ (q r).range, ((ν.real ((q r) ⁻¹' {p}) : ℂ)) • Ψ p
  have hiLimit (i : ℕ) (hi : i ∈ s) :
      Filter.Tendsto (fun r ↦ ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc i
        (S r - ηK)) Filter.atTop (𝓝 0) := by
    let A := ContDiffMapSupportedIn.structureMapCLM ℂ (E := EuclideanSpace ℝ (Fin m))
      (F := ℂ) (K := Kc) ⊤ i
    let V := BoundedContinuousFunction (EuclideanSpace ℝ (Fin m))
      ((EuclideanSpace ℝ (Fin m)) [×i]→L[ℝ] ℂ)
    let : ContinuousENorm V := @SeminormedAddGroup.toContinuousENorm V inferInstance
    let F := fun p ↦ A (Ψ p)
    have hFcont : Continuous F := by
      apply UniformContinuous.continuous
      apply Metric.uniformContinuous_iff.mpr
      intro ε hε
      obtain ⟨δ, hδ, hd⟩ := hSampling (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, fun p p' hpp' ↦ ?_⟩
      have hle := (Seminorm.le_finset_sup_apply (p := ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc) (x := Ψ p - Ψ p') hi).trans (hd p p' hpp')
      change ‖A (Ψ p - Ψ p')‖ ≤ ε / 2 at hle
      rw [map_sub] at hle
      have hd : dist (F p) (F p') = ‖F p - F p'‖ :=
        @dist_eq_norm V inferInstance (F p) (F p')
      rw [hd]
      exact hle.trans_lt (half_lt_self hε)
    obtain ⟨B, hB⟩ := hBound i hi
    have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
    have hFB (p) : ‖F p‖ ≤ B := by
      apply (BoundedContinuousFunction.norm_le hBnonneg).mpr
      intro y
      simpa only [F, A, ContDiffMapSupportedIn.structureMapCLM_top_apply] using hB p y
    have hFI : Integrable F ν := Integrable.of_bound (f := F) (μ := ν)
      hFcont.aestronglyMeasurable B
      (Filter.Eventually.of_forall hFB)
    have hlim : Filter.Tendsto (fun r ↦ ∫ p, F (q r p) ∂ν)
        Filter.atTop (𝓝 (∫ p, F p ∂ν)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ ↦ B)
      · intro r
        exact hFcont.stronglyMeasurable.comp_measurable (q r).measurable |>.aestronglyMeasurable
      · exact integrable_const B
      · intro r
        exact Filter.Eventually.of_forall (fun p ↦ hFB (q r p))
      · exact Filter.Eventually.of_forall (fun p ↦ hFcont.continuousAt.tendsto.comp (hqpoint p))
    have hint : (∫ p, F p ∂ν) = A ηK := by
      apply BoundedContinuousFunction.ext
      intro y
      let ev : V →L[ℝ] ((EuclideanSpace ℝ (Fin m)) [×i]→L[ℝ] ℂ) :=
        BoundedContinuousFunction.evalCLM ℝ y
      have hev := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (E := V)
        (Fₗ := (EuclideanSpace ℝ (Fin m)) [×i]→L[ℝ] ℂ) ev hFI
      change (∫ p, F p y ∂ν) = (∫ p, F p ∂ν) y at hev
      rw [← hev]
      simpa only [F, A, ContDiffMapSupportedIn.structureMapCLM_top_apply] using
        (hDerivativeIntegral i y).symm
    have hsum (r) : (∫ p, F (q r p) ∂ν) = A (S r) := by
      have heq : (fun p ↦ F (q r p)) = fun p ↦ ∑ a ∈ (q r).range,
          ((q r) ⁻¹' {a}).indicator (fun _ ↦ F a) p := by
        funext p
        simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
        rw [Finset.sum_eq_single (q r p)]
        · simp
        · intro b hb hne
          exact ite_eq_right (Ne.symm hne)
        · intro hn
          exact (hn (SimpleFunc.mem_range.mpr ⟨p, rfl⟩)).elim
      rw [heq, integral_finsetSum]
      · simp only [S, map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro p hp
        rw [integral_indicator_const _ ((q r).measurableSet_preimage {p})]
        exact_mod_cast (rfl : ν.real ((q r) ⁻¹' {p}) • F p = _)
      · intro p hp
        exact (integrable_const (F p)).indicator ((q r).measurableSet_preimage {p})
    rw [hint] at hlim
    simp_rw [hsum] at hlim
    have hl : Filter.Tendsto (fun r ↦ ‖A (S r) - A ηK‖) Filter.atTop (𝓝 0) := by
      exact (@tendsto_iff_norm_sub_tendsto_zero _ V inferInstance _ _ _).mp hlim
    simpa only [ContDiffMapSupportedIn.seminorm_apply, A, map_sub] using hl
  constructor
  change Filter.Tendsto (fun r ↦ s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc)
    (S r - ηK)) Filter.atTop (𝓝 0)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun r ↦ ha.trans_le (apply_nonneg _ _))
  · intro ε hε
    have hall : ∀ᶠ r in Filter.atTop, ∀ i ∈ s,
        ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc i (S r - ηK) < ε :=
      s.eventually_all.mpr (fun i hi ↦ (hiLimit i hi).eventually (gt_mem_nhds hε))
    exact hall.mono (fun r hr ↦ Seminorm.finset_sup_apply_lt hε hr)

/-- Simple-function sums converge in the selected fixed-support derivative seminorm.
Source: Dyatlov Lemma 6.8, pp. 71–73; this is the conclusion of the preceding Banach-valued
dominated-convergence argument, with finite measure and the required uniform derivative bounds. -/
theorem fixed_support_simple_function_riemann
    {m k : ℕ}
    (J : Set (EuclideanSpace ℝ (Fin k)))
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsFiniteMeasure (μ.restrict J)]
    (Kc : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin m)))
    (s : Finset ℕ)
    (Ψ : EuclideanSpace ℝ (Fin k) →
      ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ Kc)
    (ηK : ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ Kc)
    (q : ℕ → SimpleFunc (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)))
    (hqpoint : ∀ p, Filter.Tendsto (fun r ↦ q r p) Filter.atTop (𝓝 p))
    (hSampling : ∀ ε > 0, ∃ δ > 0, ∀ p q,
      dist p q < δ →
        s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc) (Ψ p - Ψ q) ≤ ε)
    (hBound : ∀ i ∈ s, ∃ B : ℝ, ∀ p y, ‖iteratedFDeriv ℝ i (Ψ p) y‖ ≤ B)
    (hDerivativeIntegral : ∀ i y,
      iteratedFDeriv ℝ i (ηK : EuclideanSpace ℝ (Fin m) → ℂ) y =
        ∫ p in J, iteratedFDeriv ℝ i (Ψ p) y ∂μ) :
    Filter.Tendsto
      (fun r ↦ s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc)
        ((∑ p ∈ (q r).range,
          ((μ.restrict J).real ((q r) ⁻¹' {p}) : ℂ) • Ψ p) - ηK))
      Filter.atTop (𝓝 0) := by
  exact (fixed_support_simple_function_riemann_core J μ Kc s Ψ ηK q
    hqpoint hSampling hBound hDerivativeIntegral).limit

end HolomorphicAnosov.Analysis

