import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Complex.ReImTopology

/-! Endpoint closure for the straight-side argument in the Schwarz--Christoffel
construction.  Bak--Newman, *Complex Analysis* (3rd ed., 2010), pp.189--190,
uses continuity of the primitive on the closed side after the constant phase
calculation on the open side. -/

open Set
noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- The endpoint passage in the straight-side argument of Bak--Newman,
pp.189--190. For two ordered points of the closed interval, choose two intermediate
interior points. Continuity extends the weak inequalities to the endpoints, and
the strict inequality between the interior points yields strictness overall. -/
theorem strictMonoOn_Icc_of_strictMonoOn_Ioo
    {a b : ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hm : StrictMonoOn f (Ioo a b)) :
    StrictMonoOn f (Icc a b) := by
  intro x hx y hy hxy
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  obtain ⟨v, huv, hvy⟩ := exists_between huy
  have hu : u ∈ Ioo a b := ⟨hx.1.trans_lt hxu, huy.trans_le hy.2⟩
  have hv : v ∈ Ioo a b := ⟨hu.1.trans huv, hvy.trans_le hy.2⟩
  have hlow : f x ≤ f u := by
    apply le_on_closure (s := Ioo x u) (f := f) (g := fun _ ↦ f u)
    · intro t ht
      exact (hm ⟨hx.1.trans_lt ht.1, ht.2.trans hu.2⟩ hu ht.2).le
    · rw [closure_Ioo hxu.ne]
      exact hc.mono (Icc_subset_Icc hx.1 hu.2.le)
    · exact continuousOn_const
    · rw [closure_Ioo hxu.ne]
      exact ⟨le_rfl, hxu.le⟩
  have hhigh : f v ≤ f y := by
    apply le_on_closure (s := Ioo v y) (f := fun _ ↦ f v) (g := f)
    · intro t ht
      exact (hm hv ⟨hv.1.trans ht.1, ht.2.trans_le hy.2⟩ ht.1).le
    · exact continuousOn_const
    · rw [closure_Ioo hvy.ne]
      exact hc.mono (Icc_subset_Icc hv.1.le hy.2)
    · rw [closure_Ioo hvy.ne]
      exact ⟨hvy.le, le_rfl⟩
  exact hlow.trans_lt ((hm hu hv huv).trans_le hhigh)

/-- A continuous vertical side with strictly increasing imaginary coordinate on
its open parameter interval covers exactly the whole closed segment between its
endpoint images. Source: Bak--Newman, pp.189--190. Extend the constant real
coordinate and strict monotonicity to the endpoints by continuity, then apply
the intermediate value theorem to the imaginary coordinate. -/
theorem complex_central_side_coverage
    {a b c : ℝ} (hab : a < b) (F : ℝ → ℂ)
    (hc : ContinuousOn F (Icc a b))
    (hm : StrictMonoOn (fun t ↦ (F t).im) (Ioo a b))
    (hreal : ∀ t ∈ Ioo a b, (F t).re = c) :
    StrictMonoOn (fun t ↦ (F t).im) (Icc a b) ∧
      (∀ t ∈ Icc a b, (F t).re = c) ∧
      F '' Icc a b = Complex.reProdIm {c} (Icc (F a).im (F b).im) := by
  have hcRe : ContinuousOn (fun t ↦ (F t).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn hc
  have hcIm : ContinuousOn (fun t ↦ (F t).im) (Icc a b) :=
    Complex.continuous_im.comp_continuousOn hc
  have heqRe : Set.EqOn (fun t ↦ (F t).re) (fun _ ↦ c) (Icc a b) := by
    apply Set.EqOn.of_subset_closure (s := Ioo a b) (t := Icc a b)
      (f := fun t ↦ (F t).re) (g := fun _ ↦ c)
    · exact hreal
    · exact hcRe
    · exact continuousOn_const
    · exact Ioo_subset_Icc_self
    · rw [← closure_Ioo hab.ne]
  have himStrict := strictMonoOn_Icc_of_strictMonoOn_Ioo hcIm hm
  have himImage : (fun t ↦ (F t).im) '' Icc a b = Icc (F a).im (F b).im :=
    ContinuousOn.image_Icc_of_monotoneOn hab.le hcIm himStrict.monotoneOn
  refine ⟨himStrict, fun t ht ↦ heqRe ht, ?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    exact ⟨heqRe ht, himStrict.monotoneOn (left_mem_Icc.mpr hab.le) ht ht.1,
      himStrict.monotoneOn ht (right_mem_Icc.mpr hab.le) ht.2⟩
  · intro z hz
    obtain ⟨t, ht, htim⟩ := himImage.symm ▸ hz.2
    refine ⟨t, ht, ?_⟩
    exact Complex.ext ((heqRe ht).trans hz.1.symm) htim

end HolomorphicAnosov.Analysis.MarkedRectangle

