import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion

open scoped Topology _root_.Topology BigOperators
open Filter MeasureTheory TopologicalSpace Set

namespace HolomorphicAnosov.ConnectionFlatEstimates

/-- Every coefficient of a closed current-valued `(1,0)` one-form has vanishing antiholomorphic
derivatives. (Zhang, Lemma 2.3, p. 7) -/
theorem closed_typeOne_current_dbar_zero {n : ℕ}
    (Ω : Opens (Fin n → ℂ)) (T : Fin n → TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hclosed : ∀ (v w : Fin n → ℂ) (φ : TestFunction Ω ℂ ⊤),
      (∑ j : Fin n, (-T j (TestFunction.lineDerivCLM ℂ v φ) * w j +
        T j (TestFunction.lineDerivCLM ℂ w φ) * v j)) = 0)
    (j k : Fin n) (φ : TestFunction Ω ℂ ⊤) :
    -T j ((2 : ℂ)⁻¹ •
      ((TestFunction.lineDerivCLM ℂ (Pi.single k 1) φ : TestFunction Ω ℂ ⊤) +
        Complex.I • (TestFunction.lineDerivCLM ℂ (Pi.single k Complex.I) φ :
          TestFunction Ω ℂ ⊤))) = 0 := by
  classical
  have hreal := hclosed (Pi.single k 1) (Pi.single j 1) φ
  have himag := hclosed (Pi.single k Complex.I) (Pi.single j 1) φ
  simp only [Finset.sum_add_distrib] at hreal himag
  simp [Pi.single_apply] at hreal himag
  simp only [map_smul, map_add, smul_eq_mul]
  linear_combination (norm := ring_nf)
    (2 : ℂ)⁻¹ * hreal + ((2 : ℂ)⁻¹ * Complex.I) * himag
  simp [Complex.I_sq]

end HolomorphicAnosov.ConnectionFlatEstimates

