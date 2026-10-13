import Mathlib.Analysis.ODE.ExistUnique

/-! Auxiliary result for Teschl, Ordinary Differential Equations and Dynamical Systems,
Corollary 2.6 and estimate (2.29), pp. 40–41; Theorem 3.9, p. 81. -/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b t0 : ℝ}

omit [CompleteSpace E] in
lemma linear_ode_unique (_hab : a < b) (ht0 : t0 ∈ Icc a b)
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b))
    (x y : ℝ → E) (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hx' : ∀ t ∈ Ioo a b, HasDerivAt x (A t (x t)) t)
    (hy' : ∀ t ∈ Ioo a b, HasDerivAt y (A t (y t)) t)
    (hxa : HasDerivWithinAt x (A a (x a)) (Ici a) a)
    (hya : HasDerivWithinAt y (A a (y a)) (Ici a) a)
    (hxb : HasDerivWithinAt x (A b (x b)) (Iic b) b)
    (hyb : HasDerivWithinAt y (A b (y b)) (Iic b) b)
    (h0 : y t0 = x t0) : EqOn y x (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hK : ∀ t ∈ Icc a b, LipschitzOnWith K (A t) univ := fun t ht ↦
    ((A t).lipschitzWith_of_opNorm_le ((hC t ht).trans (le_max_left _ _))).lipschitzOnWith
  by_cases hleft : t0 = a
  · subst t0
    apply ODE_solution_unique_of_mem_Icc_right (fun t ht ↦ hK t (Ico_subset_Icc_self ht))
      hy ?_ (fun _ _ ↦ mem_univ _) hx ?_ (fun _ _ ↦ mem_univ _) h0
    · intro t ht
      by_cases he : t = a
      · simpa only [he] using hya
      · exact (hy' t ⟨lt_of_le_of_ne ht.1 (Ne.symm he), ht.2⟩).hasDerivWithinAt
    · intro t ht
      by_cases he : t = a
      · simpa only [he] using hxa
      · exact (hx' t ⟨lt_of_le_of_ne ht.1 (Ne.symm he), ht.2⟩).hasDerivWithinAt
  by_cases hright : t0 = b
  · subst t0
    apply ODE_solution_unique_of_mem_Icc_left (fun t ht ↦ hK t (Ioc_subset_Icc_self ht))
      hy ?_ (fun _ _ ↦ mem_univ _) hx ?_ (fun _ _ ↦ mem_univ _) h0
    · intro t ht
      by_cases he : t = b
      · simpa only [he] using hyb
      · exact (hy' t ⟨ht.1, lt_of_le_of_ne ht.2 he⟩).hasDerivWithinAt
    · intro t ht
      by_cases he : t = b
      · simpa only [he] using hxb
      · exact (hx' t ⟨ht.1, lt_of_le_of_ne ht.2 he⟩).hasDerivWithinAt
  apply ODE_solution_unique_of_mem_Icc
    (fun t ht ↦ hK t (Ioo_subset_Icc_self ht))
    ⟨lt_of_le_of_ne ht0.1 (Ne.symm hleft), lt_of_le_of_ne ht0.2 hright⟩
    hy hy' (fun _ _ ↦ mem_univ _) hx hx' (fun _ _ ↦ mem_univ _) h0

end HolomorphicAnosov
