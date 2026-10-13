import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# An interval loop with no other identifications is a Jordan curve

Source: the endpoint-identified chord construction in Tao, *246C Notes 2* (2018),
§2, Theorem 20, final proof paragraph. This lemma supplies its quotient-map step.
-/

namespace HolomorphicAnosov.Topology

open Set

/-- A continuous interval map with equal endpoints, injective on the half-open interval,
parametrizes an embedded circle with the same image.

Source: Tao, *246C Notes 2*, §2, Theorem 20, final proof paragraph.
Proof: descend the interval map to `AddCircle 1` using its equal endpoint values.
Each circle class has a unique representative in `[0,1)`, so injectivity on this
interval proves injectivity of the descended map. Compactness of the circle and
the Hausdorff target upgrade continuous injectivity to an embedding. The endpoint
at one has the same image as zero, so the closed and half-open interval images agree. -/
theorem intervalLoop_circle_embedding {X : Type*} [TopologicalSpace X] [T2Space X]
    (f : ℝ → X) (hf : ContinuousOn f (Icc 0 1)) (hend : f 0 = f 1)
    (hinj : InjOn f (Ico 0 1)) :
    ∃ j : Circle → X, _root_.Topology.IsEmbedding j ∧ range j = f '' Icc 0 1 := by
  let g : AddCircle (1 : ℝ) → X := AddCircle.liftIco 1 0 f
  have hg : Continuous g := AddCircle.liftIco_zero_continuous hend hf
  have hg_inj : Function.Injective g := by
    intro a b hab
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    apply hinj
    · simpa using (AddCircle.equivIco (1 : ℝ) 0 a).property
    · simpa using (AddCircle.equivIco (1 : ℝ) 0 b).property
    · exact hab
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  refine ⟨g ∘ e.symm, ((hg.comp e.symm.continuous).isClosedEmbedding (hg_inj.comp e.symm.injective)).isEmbedding, ?_⟩
  rw [range_comp, e.symm.surjective.range_eq, image_univ]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(AddCircle.equivIco (1 : ℝ) 0 a).val,
      by simpa using (Ico_subset_Icc_self (AddCircle.equivIco (1 : ℝ) 0 a).property), rfl⟩
  · rintro ⟨t, ht, rfl⟩
    by_cases h : t = 1
    · subst t
      refine ⟨0, ?_⟩
      change AddCircle.liftIco 1 0 f 0 = f 1
      rw [← hend]
      exact AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 1)
    · refine ⟨(t : AddCircle (1 : ℝ)), ?_⟩
      exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 h⟩


end HolomorphicAnosov.Topology
