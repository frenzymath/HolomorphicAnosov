import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

open Set Filter
open scoped Topology
namespace HolomorphicAnosov

/-- On an open simply connected plane domain a nonvanishing holomorphic function
has a holomorphic square root, with either choice of sign at a prescribed point.
Source: Conway II XVI §4, proof of Theorem 4.2 p.125. The continuous root comes
from the covering-space lifting theorem. Near a nonzero root value, the square
map has nonzero derivative and a holomorphic local inverse. Continuity keeps the
root in this inverse sheet, proving its holomorphy. Negating it if necessary
makes its real part at the prescribed point nonpositive. -/
theorem holomorphic_square_root_nonpos_re_g7 {G : Set ℂ}
    (hG : IsOpen G) (hc : IsSimplyConnected G) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f G) (hnz : ∀ z ∈ G, f z ≠ 0) (a : ℂ) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g G ∧ (∀ z ∈ G, g z ^ 2 = f z) ∧
      (g a).re ≤ 0 := by
  obtain ⟨g, hgc, hsq⟩ := Complex.exists_continuousOn_pow_eq hc hG hf.continuousOn
    (by rintro ⟨z, hz, he⟩; exact hnz z hz he) (by decide : (2 : ℕ) ≠ 0)
  have hhol : DifferentiableOn ℂ g G := by
    intro z hz
    have hg0 : g z ≠ 0 := by
      intro he
      have := hsq z
      rw [he, zero_pow (by decide)] at this
      exact hnz z hz this.symm
    have hp : HasStrictDerivAt (fun w : ℂ ↦ w ^ 2) (2 * g z) (g z) := by
      simpa using hasStrictDerivAt_pow 2 (g z)
    have hd : 2 * g z ≠ 0 := mul_ne_zero (by norm_num) hg0
    let r := hp.localInverse (fun w : ℂ ↦ w ^ 2) (2 * g z) (g z) hd
    have hr : DifferentiableAt ℂ r (f z) := by
      rw [← hsq z]
      exact (hp.to_localInverse hd).hasDerivAt.differentiableAt
    have heq : g =ᶠ[𝓝 z] r ∘ f := by
      have he := (hgc.continuousAt (hG.mem_nhds hz)).eventually
        (hp.eventually_left_inverse hd)
      filter_upwards [he] with w hw
      change g w = r (f w)
      rw [← hsq w]
      exact hw.symm
    exact ((hr.comp z (hf.differentiableAt (hG.mem_nhds hz))).congr_of_eventuallyEq
      heq).differentiableWithinAt
  by_cases hsign : (g a).re ≤ 0
  · exact ⟨g, hhol, fun z _ ↦ hsq z, hsign⟩
  · refine ⟨fun z ↦ -g z, hhol.neg, ?_, ?_⟩
    · intro z hz
      simpa using hsq z
    · simpa using (neg_nonpos.mpr (le_of_not_ge hsign))

end HolomorphicAnosov
