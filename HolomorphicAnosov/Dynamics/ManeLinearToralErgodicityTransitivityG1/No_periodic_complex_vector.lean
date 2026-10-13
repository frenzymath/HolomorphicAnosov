import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions

import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Matrix

namespace HolomorphicAnosov.Dynamics
open MeasureTheory
noncomputable section

open scoped Matrix.Norms.Operator in
theorem no_periodic_complex_vector {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hroot : ∀ μ : ℂ, Module.End.HasEigenvalue A.mulVecLin μ → ¬ IsOfFinOrder μ)
    (r : ℕ) (hr : 0 < r) (v : Fin n → ℂ) (hv : v ≠ 0) :
    (A.transpose ^ r).mulVec v ≠ v := by
  intro hperiod
  have he : Module.End.HasEigenvalue (A.transpose ^ r).mulVecLin (1 : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hperiod), hv⟩)
  have hspec : (1 : ℂ) ∈ spectrum ℂ (A.transpose ^ r) := by
    rw [← Matrix.spectrum_toLin']
    exact he.mem_spectrum
  rw [spectrum.map_pow] at hspec
  obtain ⟨μ, hμ, hμpow⟩ := hspec
  have hμA : μ ∈ spectrum ℂ A := by simpa using hμ
  have heA : Module.End.HasEigenvalue A.mulVecLin μ := by
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    change μ ∈ spectrum ℂ A.toLin'
    rw [Matrix.spectrum_toLin']
    exact hμA
  exact hroot μ heA (isOfFinOrder_iff_pow_eq_one.mpr ⟨r, hr, hμpow⟩)

end
end HolomorphicAnosov.Dynamics
