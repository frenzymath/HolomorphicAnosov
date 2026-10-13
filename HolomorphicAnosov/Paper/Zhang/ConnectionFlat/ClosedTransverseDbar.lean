import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

open scoped Manifold ContDiff Topology _root_.Topology
open Filter MeasureTheory TopologicalSpace Set
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates
open scoped BigOperators

/-- If the current-valued one-form `T dz_j₀` is closed, every antiholomorphic derivative of `T`
vanishes. (Zhang, Lemma 2.3, p. 7) -/
theorem closed_transverse_current_dbar_zero {n : ℕ}
    (Ω : TopologicalSpace.Opens (Fin n → ℂ)) (j₀ : Fin n)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hclosed : ∀ (v w : Fin n → ℂ) (φ : TestFunction Ω ℂ ⊤),
      -T (TestFunction.lineDerivCLM ℂ v φ) * w j₀ +
        T (TestFunction.lineDerivCLM ℂ w φ) * v j₀ = 0)
    (j : Fin n) (φ : TestFunction Ω ℂ ⊤) :
    -T ((2 : ℂ)⁻¹ •
      ((TestFunction.lineDerivCLM ℂ (Pi.single j 1) φ : TestFunction Ω ℂ ⊤) +
        Complex.I • (TestFunction.lineDerivCLM ℂ (Pi.single j Complex.I) φ :
          TestFunction Ω ℂ ⊤))) = 0 := by
  have hdir (v : Fin n → ℂ) :
      T (TestFunction.lineDerivCLM ℂ v φ) =
        T (TestFunction.lineDerivCLM ℂ (Pi.single j₀ 1) φ) * v j₀ := by
    have h := hclosed v (Pi.single j₀ 1) φ
    simp only [Pi.single_eq_same, mul_one] at h
    linear_combination -h
  simp only [map_smul, map_add, smul_eq_mul]
  rw [hdir (Pi.single j 1), hdir (Pi.single j Complex.I)]
  by_cases hj : j = j₀
  · subst j
    simp [← mul_assoc]
    ring_nf
    simp [Complex.I_sq]
  · simp [Pi.single_eq_of_ne (Ne.symm hj)]

end ConnectionFlatEstimates
end HolomorphicAnosov
