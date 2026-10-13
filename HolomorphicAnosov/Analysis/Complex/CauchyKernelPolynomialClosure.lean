import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.ContinuousMap.Polynomial

/-!
# Cauchy kernels in the closure of polynomial restrictions

Agent proof using Mathlib's closed-subalgebra spectral permanence theorem.
For a compact complex set with preconnected plane complement, the coordinate
function has spectrum exactly the compact set in C(K, ℂ). Its spectrum in the
closed polynomial subalgebra is unchanged. Therefore z minus the coordinate
is invertible in that subalgebra for every z outside K. Evaluating the inverse
identity at each point identifies its inverse with the Cauchy kernel.
-/

open Set
open scoped _root_.Topology

namespace HolomorphicAnosov.Analysis.Complex

/-- On a compact set with preconnected complement, every Cauchy kernel with
pole outside the set lies in the uniform closure of polynomial restrictions.
The proof is the spectral argument described above; empty compact sets are allowed. -/
theorem cauchy_kernel_mem_polynomial_closure {K : Set ℂ} (hK : IsCompact K)
    (hc : IsPreconnected Kᶜ) (z : ℂ) (hz : z ∉ K) :
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    (⟨fun w : K ↦ (z - w.val)⁻¹, (continuous_const.sub continuous_subtype_val).inv₀
      (fun w ↦ sub_ne_zero.mpr (fun he ↦ hz (by simpa only [he] using w.property)))⟩ : C(K, ℂ)) ∈
      (polynomialFunctions K).topologicalClosure := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S := (polynomialFunctions K).topologicalClosure
  have : IsClosed (S : Set C(K, ℂ)) := (polynomialFunctions K).isClosed_topologicalClosure
  let x : C(K, ℂ) := Polynomial.toContinuousMapOnAlgHom K Polynomial.X
  have hx : x ∈ S := (polynomialFunctions K).le_topologicalClosure
    (by change x ∈ (polynomialFunctions K : Set C(K, ℂ)); rw [polynomialFunctions_coe]; exact ⟨Polynomial.X, rfl⟩)
  have hspec : spectrum ℂ x = K := by
    rw [ContinuousMap.spectrum_eq_range]
    have hxcoe : ⇑x = (fun w : K ↦ (w : ℂ)) := by
      funext w
      simp [x]
    rw [hxcoe, Subtype.range_coe]
  have he := Subalgebra.spectrum_eq_of_isPreconnected_compl S (⟨x, hx⟩ : S)
    (by simpa [hspec] using hc)
  have hunit : IsUnit (algebraMap ℂ S z - ⟨x, hx⟩) := by
    apply spectrum.notMem_iff.mp
    rw [he, hspec]
    exact hz
  let v : S := (hunit.unit⁻¹ : (Sˣ))
  have hm : (algebraMap ℂ S z - ⟨x, hx⟩) * v = 1 := hunit.mul_val_inv
  have hv : (v : C(K, ℂ)) =
      ⟨fun w : K ↦ (z - w.val)⁻¹, (continuous_const.sub continuous_subtype_val).inv₀
        (fun w ↦ sub_ne_zero.mpr (fun he ↦ hz (by simpa only [he] using w.property)))⟩ := by
    ext w
    have hh := congrArg (fun t : S ↦ (t : C(K, ℂ)) w) hm
    have hxw : x w = w.val := by simp [x]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_algebraMap,
      Subalgebra.coe_one, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
      ContinuousMap.one_apply, hxw] at hh
    exact eq_inv_of_mul_eq_one_right hh
  exact hv ▸ v.property

end HolomorphicAnosov.Analysis.Complex
