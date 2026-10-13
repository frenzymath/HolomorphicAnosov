import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Differentiation of interval integrals over compact parameter neighborhoods. -/

open scoped Topology _root_.Topology
open Set Filter MeasureTheory

namespace HolomorphicAnosov

/-- Jointly continuous spatial derivatives on a compact neighborhood may be integrated over a fixed interval. (Bochner–Montgomery, Lemma 2, equation (13).) -/
theorem hasFDerivAt_intervalIntegral_of_compact_parameter
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → E → F) (f' : ℝ → E → E →L[ℝ] F)
    {a b : ℝ} {K : Set E} {x : E}
    (hK : IsCompact K) (hx : K ∈ 𝓝 x)
    (hf : ContinuousOn (Function.uncurry f) (uIcc a b ×ˢ K))
    (hf' : ContinuousOn (Function.uncurry f') (uIcc a b ×ˢ K))
    (hderiv : ∀ t ∈ uIcc a b, ∀ y ∈ K, HasFDerivAt (f t) (f' t y) y) :
    HasFDerivAt (fun y ↦ ∫ t in a..b, f t y) (∫ t in a..b, f' t x) x := by
  have htime (y : E) (hy : y ∈ K) : IntervalIntegrable (fun t ↦ f t y) volume a b :=
    (hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht ↦ ⟨ht, hy⟩)).intervalIntegrable
  have htime' : IntervalIntegrable (fun t ↦ f' t x) volume a b :=
    (hf'.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht ↦ ⟨ht, mem_of_mem_nhds hx⟩)).intervalIntegrable
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod hK).exists_bound_of_continuousOn hf'
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y t ↦ f' t y) (bound := fun _ ↦ C) hx
  · filter_upwards [hx] with y hy
    exact (htime y hy).def'.aestronglyMeasurable
  · exact htime x (mem_of_mem_nhds hx)
  · exact htime'.def'.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t ht y hy ↦ hC (t, y) ⟨uIoc_subset_uIcc ht, hy⟩)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t ht y hy ↦ hderiv t (uIoc_subset_uIcc ht) y hy)

end HolomorphicAnosov
