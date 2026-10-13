import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.FlowEndpoint
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.PasteSmooth
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Tactic.Linarith

/-!
Reusable ExtendEndpoint declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07FlowContinuation

open Set Filter
open scoped Manifold ContDiff Topology _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [BoundarylessManifold I N] [T2Space N]
  {V : (x : N) → TangentSpace I x}

theorem extend_endpoint
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    {s t δ : ℝ} {z q : N} (hδ : 0 < δ)
    {U : Set N} {Ψ : N × ℝ → N}
    (hΨ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ Ψ (U ×ˢ Ioo (-δ) δ))
    (hzero : ∀ w ∈ U, Ψ (w, 0) = w)
    (hcurve : ∀ w ∈ U, IsMIntegralCurveOn (fun r ↦ Ψ (w, r)) V (Ioo (-δ) δ))
    (hq : q ∈ U) (ht : t - s ∈ Ioo (-δ) δ) (hz : Endpoint V s z q) :
    Endpoint V t z (Ψ (q, t - s)) := by
  classical
  obtain ⟨a, b, γ, h0, hs, hγ, hcγ, hγ0, hγs⟩ := hz
  let η : ℝ → N := fun r ↦ Ψ (q, r - s)
  have hcη : IsMIntegralCurveOn η V (Ioo (s - δ) (s + δ)) := by
    have hh := (isMIntegralCurveOn_comp_sub (dt := s)).mpr (hcurve q hq)
    have heq : {r : ℝ | r - s ∈ Ioo (-δ) δ} = Ioo (s - δ) (s + δ) := by
      ext r
      simp only [mem_ofPred_eq, mem_Ioo]
      constructor <;> intro hr <;> constructor <;> linarith [hr.1, hr.2]
    rw [heq] at hh
    exact hh
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ η (Ioo (s - δ) (s + δ)) := by
    apply hΨ.comp ((contMDiffOn_const (c := q)).prodMk
      ((contMDiff_id.sub contMDiff_const).contMDiffOn))
    intro r hr
    change q ∈ U ∧ r - s ∈ Ioo (-δ) δ
    exact ⟨hq, by constructor <;> linarith [hr.1, hr.2]⟩
  have hs' : s ∈ Ioo (s - δ) (s + δ) := ⟨by linarith, by linarith⟩
  have het : γ s = η s := by simp only [η, sub_self, hzero q hq, hγs]
  have hunion := Ioo_union_Ioo' (show s - δ < b by linarith [hs.2])
    (show a < s + δ by linarith [hs.1])
  let κ := piecewise (Ioo a b) γ η
  refine ⟨min a (s - δ), max b (s + δ), κ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨lt_of_le_of_lt (min_le_left ..) h0.1, lt_of_lt_of_le h0.2 (le_max_left ..)⟩
  · exact ⟨by have := min_le_right a (s - δ); linarith [ht.1],
      by have := le_max_right b (s + δ); linarith [ht.2]⟩
  · rw [← hunion]
    exact paste_smooth hV hγ hη hcγ hcη ⟨hs, hs'⟩ het
  · rw [← hunion]
    exact isMIntegralCurveOn_piecewise (hV.of_le (by simp)) hcγ hcη ⟨hs, hs'⟩ het
  · simpa only [κ, piecewise, ite_eq_left h0] using hγ0
  · exact eqOn_piecewise_of_isMIntegralCurveOn_Ioo (hV.of_le (by simp)) hcγ hcη
      ⟨hs, hs'⟩ het (by constructor <;> linarith [ht.1, ht.2])

end HolomorphicAnosov.W07FlowContinuation
