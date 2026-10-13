import HolomorphicAnosov.Topology.OnePointCompactComplement
import HolomorphicAnosov.Analysis.Complex.CauchyKernelPolynomialClosure
import HolomorphicAnosov.Analysis.Normed.RudinAnnihilatorClosure
import HolomorphicAnosov.Analysis.Complex.ConwayFinitePolygonCauchyRepresentation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Compact polynomial approximation with connected complement

Rudin, Real and Complex Analysis, third edition, Theorem 13.7, printed p.271
(positive-epsilon form). The proof below is an agent alternative to the Riesz
representation and Cauchy-transform proof of Theorem 13.6: closed-subalgebra
spectral permanence supplies the required polynomial closure of each Cauchy
kernel directly.

First the compact-complement component comparison transfers connectedness
from the one-point compactification to preconnectedness of the plane complement.
Let Φ be a bounded complex-linear functional on C(K, ℂ) vanishing on polynomial
restrictions. It also vanishes on their closure, hence on every Cauchy kernel
with pole outside K. The finite polygon Cauchy representation expresses f|K
as a finite linear combination of C(K, ℂ)-valued integrals of these kernels
multiplied by f along the edges. The kernel depends continuously on its pole
in the complement, so the edge integrands are continuous on [0,1] and genuinely
interval integrable. Evaluation commutes with those integrals and verifies the
representation pointwise. Φ commutes with them as well, giving Φ(f|K)=0.
The annihilator criterion then puts f|K in the polynomial closure. A norm ball
of radius ε supplies a polynomial and the supremum norm gives the asserted
pointwise error. No nonemptiness or connectedness of K or U is required.
-/

open Set
open scoped _root_.Topology

namespace HolomorphicAnosov.Analysis.Complex

/-- Rudin 13.7: polynomial approximation on compact sets whose complement in
the one-point compactification is connected. The complete proof is above. -/
theorem rudin_compact_connected_complement_polynomial_approximation
    (U : Set ℂ) (hU : IsOpen U) (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (hcompl : IsConnected (OnePoint.some '' K)ᶜ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let fK : C(K, ℂ) := ⟨fun z ↦ f z.val, (hf.continuousOn.mono hKU).domRestrict⟩
  have hplane : IsPreconnected Kᶜ := by
    by_cases hn : Kᶜ.Nonempty
    · obtain ⟨a, ha⟩ := hn
      have he : connectedComponentIn Kᶜ a = Kᶜ := by
        apply Set.Subset.antisymm (connectedComponentIn_subset _ _)
        intro b hb
        apply HolomorphicAnosov.Topology.onePoint_complex_complement_component hK ha hb
        rw [hcompl.isPreconnected.connectedComponentIn (by simpa using ha)]
        simpa using hb
      rw [← he]
      exact isPreconnected_connectedComponentIn
    · rw [Set.not_nonempty_iff_eq_empty.mp hn]
      exact isPreconnected_empty
  let M := (polynomialFunctions K).toSubmodule
  have hclosure : fK ∈ closure (M : Set C(K, ℂ)) := by
    apply (HolomorphicAnosov.rudin_bounded_functional_annihilator_closure M fK).mpr
    intro Φ hΦ
    have hker : (polynomialFunctions K).topologicalClosure.toSubmodule ≤ Φ.ker := by
      intro g hg
      exact closure_minimal hΦ (isClosed_eq Φ.continuous continuous_const) hg
    let r (z : {z : ℂ // z ∉ K}) : C(K, ℂ) :=
      ⟨fun w ↦ (z.val - w.val)⁻¹, (continuous_const.sub continuous_subtype_val).inv₀
        (fun w ↦ sub_ne_zero.mpr (fun he ↦ z.property (by simpa only [he] using w.property)))⟩
    have hr : Continuous r := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (continuous_subtype_val.comp continuous_fst |>.sub
        (continuous_subtype_val.comp continuous_snd)).inv₀
        (by
          intro p he
          apply p.1.property
          have he' : p.1.val = p.2.val := sub_eq_zero.mp he
          rw [he']
          exact p.2.property)
    have hrzero (z : {z : ℂ // z ∉ K}) : Φ (r z) = 0 :=
      hker (cauchy_kernel_mem_polynomial_closure hK hplane z.val z.property)
    obtain ⟨n, m, v, hm, hv, hedge, hrepr⟩ :=
      conway_finite_polygon_cauchy_representation U K hU hK hKU
    let F (j : Fin n) (k : Fin (m j)) (t : ℝ) : C(K, ℂ) :=
      if ht : t ∈ Icc (0 : ℝ) 1 then
        f (AffineMap.lineMap (v j k.castSucc) (v j k.succ) t) •
          r ⟨AffineMap.lineMap (v j k.castSucc) (v j k.succ) t, (hedge j k t ht).2⟩
      else 0
    have hFc (j : Fin n) (k : Fin (m j)) : ContinuousOn (F j k) (Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hγ : Continuous (fun t : Icc (0 : ℝ) 1 ↦
          AffineMap.lineMap (v j k.castSucc) (v j k.succ) t.val) := by fun_prop
      have hfγ := hf.continuousOn.comp_continuous hγ
        (fun t ↦ (hedge j k t.val t.property).1)
      have hrγ := hr.comp (hγ.subtype_mk (fun t ↦ (hedge j k t.val t.property).2))
      convert hfγ.smul hrγ using 1
      ext t z
      simp only [F, dite_eq_left t.property, ContinuousMap.smul_apply, smul_eq_mul, Set.domRestrict_apply]
      rfl
    have hFi (j : Fin n) (k : Fin (m j)) :
        IntervalIntegrable (F j k) MeasureTheory.volume 0 1 :=
      (hFc j k).intervalIntegrable_of_Icc (by norm_num)
    have hFzero (j : Fin n) (k : Fin (m j)) :
        Φ (∫ t in (0 : ℝ)..1, F j k t) = 0 := by
      rw [← Φ.intervalIntegral_comp_comm (hFi j k)]
      suffices he : (fun t ↦ Φ (F j k t)) = fun _ ↦ 0 by rw [he]; simp
      funext t
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · simp only [F, dite_eq_left ht, map_smul, hrzero, smul_zero]
      · simp only [F, dite_eq_right ht, map_zero]
    have hFeval (j : Fin n) (k : Fin (m j)) (z : K) :
        (∫ t in (0 : ℝ)..1, F j k t) z = ∫ t in (0 : ℝ)..1,
          f (AffineMap.lineMap (v j k.castSucc) (v j k.succ) t) /
            (AffineMap.lineMap (v j k.castSucc) (v j k.succ) t - z.val) := by
      change (ContinuousMap.evalCLM ℂ z) (∫ t in (0 : ℝ)..1, F j k t) = _
      rw [← (ContinuousMap.evalCLM ℂ z).intervalIntegral_comp_comm (hFi j k)]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
      simp only [F, dite_eq_left ht', r, div_eq_mul_inv, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, ContinuousMap.coe_mk, smul_eq_mul]
    have hrep : fK = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        ∑ j : Fin n, ∑ k : Fin (m j), (v j k.succ - v j k.castSucc) •
          ∫ t in (0 : ℝ)..1, F j k t := by
      ext z
      simpa only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul, hFeval] using!
        hrepr f hf z.val z.property
    rw [hrep]
    simp [map_smul, hFzero]
  obtain ⟨g, hg, hgε⟩ := Metric.mem_closure_iff.mp hclosure ε hε
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, Polynomial.toContinuousMapOnAlgHom K p = g := by
    change g ∈ (polynomialFunctions K : Set C(K, ℂ)) at hg
    rwa [polynomialFunctions_coe] at hg
  refine ⟨p, fun z hz ↦ ?_⟩
  have hh := (ContinuousMap.norm_coe_le_norm (fK - g) ⟨z, hz⟩).trans_lt
    (show ‖fK - g‖ < ε by simpa [dist_eq_norm] using hgε)
  simpa [fK, ← hp, ContinuousMap.coe_mk] using! hh


end HolomorphicAnosov.Analysis.Complex
