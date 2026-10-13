import Mathlib.Analysis.ODE.ExistUnique

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

lemma integral_solution_deriv (hab : a < b) (ht0 : t0 ∈ Icc a b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b))
    (x0 : E) (y : ℝ → E) (hy : ContinuousOn y (Icc a b))
    (heq : ∀ t ∈ Icc a b, y t = x0 + ∫ s in t0..t, A s (y s)) :
    (∀ t ∈ Ioo a b, HasDerivAt y (A t (y t)) t) ∧
    HasDerivWithinAt y (A a (y a)) (Ici a) a ∧
    HasDerivWithinAt y (A b (y b)) (Iic b) b := by
  let f : ℝ → E := IccExtend hab.le (fun t ↦ A t (y t))
  have hf : Continuous f := Continuous.Icc_extend' (continuousOn_iff_continuous_domRestrict.mp (hA.clm_apply hy))
  let F : ℝ → E := fun t ↦ x0 + ∫ s in t0..t, f s
  have hF : ∀ t, HasDerivAt F (f t) t := fun t ↦
    (integral_hasDerivAt_right (hf.intervalIntegrable t0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_add x0
  have hfy : ∀ t ∈ Icc a b, f t = A t (y t) := by
    intro t ht
    exact IccExtend_of_mem hab.le _ ht
  have hFy : EqOn F y (Icc a b) := by
    intro t ht
    rw [heq t ht]
    change x0 + (∫ s in t0..t, f s) = x0 + _
    congr 1
    exact integral_congr (fun s hs ↦ hfy s (uIcc_subset_Icc ht0 ht hs))
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt y (A t (y t)) (Icc a b) t := by
    rw [← hfy t ht]
    exact (hF t).hasDerivWithinAt.congr (fun s hs ↦ (hFy hs).symm) (hFy ht).symm
  refine ⟨fun t ht ↦ (hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2), ?_, ?_⟩
  · have h := hderiv a ⟨le_rfl, hab.le⟩
    apply h.mono_of_mem_nhdsWithin
    exact Filter.inter_mem (self_mem_nhdsWithin) (nhdsWithin_le_nhds (Iic_mem_nhds hab))
  · have h := hderiv b ⟨hab.le, le_rfl⟩
    apply h.mono_of_mem_nhdsWithin
    exact Filter.inter_mem (nhdsWithin_le_nhds (Ici_mem_nhds hab)) self_mem_nhdsWithin

end HolomorphicAnosov
