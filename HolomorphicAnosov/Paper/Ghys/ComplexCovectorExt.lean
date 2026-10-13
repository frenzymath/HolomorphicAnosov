import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

namespace HolomorphicAnosov.Ghys

/-- A degree-one homogeneous scalar function on the punctured complex line extends uniquely to a
continuous complex-linear covector on the whole line. (Ghys, §3, p. 592; Kriegl–Michor, §§37.12,
37.16, pp. 381–383, 385) -/
theorem homogeneous_complex_covector_extension (F : ℂˣ → ℂ)
    (hF : ∀ a b : ℂˣ, F (a * b) = (a : ℂ) * F b) :
    ∃! L : ℂ →L[ℂ] ℂ, ∀ a : ℂˣ, L (a : ℂ) = F a := by
  let L : ℂ →L[ℂ] ℂ := (ContinuousLinearMap.id ℂ ℂ).smulRight (F 1)
  have hformula (a : ℂˣ) : F a = (a : ℂ) * F 1 := by
    simpa only [mul_one] using hF a 1
  refine ⟨L, ?_, ?_⟩
  · intro a
    exact (hformula a).symm
  · intro K hK
    apply ContinuousLinearMap.ext_ring
    simpa [L] using hK 1

end HolomorphicAnosov.Ghys
