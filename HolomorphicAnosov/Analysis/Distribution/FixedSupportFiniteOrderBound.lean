import HolomorphicAnosov.Analysis.TestFunctionFixedSupport

noncomputable section
open Set MeasureTheory
open scoped ContDiff Distributions NNReal
namespace HolomorphicAnosov.Analysis

/-- A continuous complex-linear functional on the LF test space is bounded on each
fixed compact-support carrier by finitely many derivative seminorms. -/
theorem distribution_fixed_support_finite_order_bound
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (s : Finset ℕ) (C : ℝ≥0), C ≠ 0 ∧
      ∀ f : ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ ⟨K,hK⟩,
      ‖T (TestFunction.ofSupportedIn hKU f)‖ ≤
        C • s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ ⟨K,hK⟩) f := by
  let inc : ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ ⟨K,hK⟩ →L[ℂ]
      TestFunction U ℂ ⊤ := TestFunction.ofSupportedInCLM ℂ hKU
  let q : Seminorm ℂ (ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ ⟨K,hK⟩) :=
    (normSeminorm ℂ ℂ).comp (T.toLinearMap ∘ₗ inc.toLinearMap)
  have hcomp : Continuous (fun f : ContDiffMapSupportedIn
      (EuclideanSpace ℝ (Fin m)) ℂ ⊤ ⟨K,hK⟩ ↦ T (inc f)) :=
    (ContinuousLinearMap.continuous T).comp inc.continuous
  have hq : Continuous q := by
    exact continuous_norm.comp hcomp
  have hb := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ ⊤ ⟨K,hK⟩) q hq
  rcases hb with ⟨s,C,hC,hle⟩
  exact ⟨s,C,hC,fun f ↦ hle f⟩

end HolomorphicAnosov.Analysis
