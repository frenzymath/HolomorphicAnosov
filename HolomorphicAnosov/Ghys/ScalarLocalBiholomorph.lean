import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Basic

/-! A local complex diffeomorphism from a nonzero derivative (Rudin) -/
open Set
open scoped Topology _root_.Topology ContDiff
namespace HolomorphicAnosov.Ghys

/-- A complex smooth scalar function with nonzero derivative at zero has a smooth local inverse on an open source containing zero. (Rudin, Thm. 10.30) -/
theorem scalar_local_biholomorph (f : ℂ → ℂ) (hf : ContDiff ℂ ∞ f)
    (h0 : deriv f 0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      0 ∈ e.source ∧ (e : ℂ → ℂ) = f ∧
      ContDiffOn ℂ ∞ e e.source ∧ ContDiffOn ℂ ∞ e.symm e.target := by
  let hf' := (hf.differentiable (by simp) 0).hasDerivAt.hasFDerivAt_equiv h0
  let e₀ := hf.contDiffAt.toOpenPartialHomeomorph f hf' (by simp)
  let s : Set ℂ := {z | deriv f z ≠ 0}
  have hs : IsOpen s := (hf.continuous_deriv (by simp)).isOpen_preimage _ isOpen_ne
  let e := e₀.restrOpen s hs
  have he : (e : ℂ → ℂ) = f := rfl
  refine ⟨e, ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hf' (by simp), h0⟩,
    he, ?_, ?_⟩
  · simpa only [he] using hf.contDiffOn (s := e.source)
  · intro z hz
    have hne : deriv f (e.symm z) ≠ 0 := (e.map_target hz).2
    have hder : HasDerivAt e (deriv f (e.symm z)) (e.symm z) := by
      simpa only [he] using (hf.differentiable (by simp) (e.symm z)).hasDerivAt
    exact (e.contDiffAt_symm_deriv hne hz hder (by simpa only [he] using hf.contDiffAt)).contDiffWithinAt

end HolomorphicAnosov.Ghys
