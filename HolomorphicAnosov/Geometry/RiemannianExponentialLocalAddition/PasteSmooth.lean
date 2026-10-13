import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
Reusable PasteSmooth declarations from the Riemannian exponential construction.
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

theorem paste_smooth
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    {a b c d s : ℝ} {γ η : ℝ → N}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Ioo a b))
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ η (Ioo c d))
    (hcγ : IsMIntegralCurveOn γ V (Ioo a b))
    (hcη : IsMIntegralCurveOn η V (Ioo c d))
    (hs : s ∈ Ioo a b ∩ Ioo c d) (he : γ s = η s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (piecewise (Ioo a b) γ η) (Ioo a b ∪ Ioo c d) := by
  classical
  have heq := eqOn_piecewise_of_isMIntegralCurveOn_Ioo (hV.of_le (by simp)) hcγ hcη hs he
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · apply ContMDiffAt.contMDiffWithinAt
    apply (hγ.contMDiffAt (isOpen_Ioo.mem_nhds hmem)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
    simp [piecewise, hu]
  · have hmem' : t ∈ Ioo c d := ht.resolve_left hmem
    apply ContMDiffAt.contMDiffWithinAt
    apply (hη.contMDiffAt (isOpen_Ioo.mem_nhds hmem')).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hmem'] with u hu
    exact heq hu

end HolomorphicAnosov.W07FlowContinuation
