import HolomorphicAnosov.Analysis.Distribution.FixedSupportFiniteOrderBound

/-!
# Fixed-support seminorm remainder estimate

This elementary bridge applies a finite-order distribution bound to a supported
remainder whose controlling derivative seminorms are uniformly bounded.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Distributions NNReal

namespace HolomorphicAnosov.Analysis

/-- A finite-order fixed-support bound turns uniform bounds on each controlling
jet seminorm into a scalar pairing bound. -/
theorem distribution_pairing_fixed_support_seminorm_remainder
    {m : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (s : Finset ℕ) (C : ℝ≥0)
    (hboundT : ∀ F : ContDiffMapSupportedIn
      (EuclideanSpace ℝ (Fin m)) ℂ ⊤ ⟨K, hK⟩,
      ‖T (TestFunction.ofSupportedIn hKU F)‖ ≤
        C • s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ ⟨K, hK⟩) F)
    (F : ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ ⟨K, hK⟩)
    (B : ℝ) (hB : 0 ≤ B)
    (hjet : ∀ i ∈ s,
      ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ ⟨K, hK⟩ i F ≤ B) :
    ‖T (TestFunction.ofSupportedIn hKU F)‖ ≤ (C : ℝ) * B := by
  calc
    ‖T (TestFunction.ofSupportedIn hKU F)‖ ≤
        C • s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ ⟨K, hK⟩) F := hboundT F
    _ ≤ (C : ℝ) * B := by
      change (C : ℝ) *
        (s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ ⟨K, hK⟩) F) ≤ (C : ℝ) * B
      gcongr
      exact Seminorm.finset_sup_apply_le hB hjet

end HolomorphicAnosov.Analysis
