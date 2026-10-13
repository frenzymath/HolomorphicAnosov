import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.ExtendEndpoint

/-!
Reusable ExtendCertificate declarations from the Riemannian exponential construction.
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

theorem extend_certificate
    (hV : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle I N)))
    {s t δ : ℝ} {z q : N} (hδ : 0 < δ)
    {U : Set N} {Ψ : N × ℝ → N} (hU : IsOpen U)
    (hΨ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ Ψ (U ×ˢ Ioo (-δ) δ))
    (hzero : ∀ w ∈ U, Ψ (w, 0) = w)
    (hcurve : ∀ w ∈ U, IsMIntegralCurveOn (fun r ↦ Ψ (w, r)) V (Ioo (-δ) δ))
    (hq : q ∈ U) (ht : t - s ∈ Ioo (-δ) δ)
    (hz : ∃ W, IsOpen W ∧ z ∈ W ∧ ∃ F : N → N,
      ContMDiffOn I I ∞ F W ∧ F z = q ∧ ∀ w ∈ W, Endpoint V s w (F w)) :
    ∃ W, IsOpen W ∧ z ∈ W ∧ ∃ F : N → N,
      ContMDiffOn I I ∞ F W ∧ F z = Ψ (q, t - s) ∧
        ∀ w ∈ W, Endpoint V t w (F w) := by
  obtain ⟨W, hW, hzW, F, hF, hFz, hend⟩ := hz
  let W' := W ∩ F ⁻¹' U
  refine ⟨W', hF.continuousOn.isOpen_inter_preimage hW hU, ⟨hzW, ?_⟩,
    fun w ↦ Ψ (F w, t - s), ?_, ?_, ?_⟩
  · simpa only [mem_preimage, hFz] using hq
  · exact hΨ.comp ((hF.mono inter_subset_left).prodMk contMDiffOn_const)
      (fun w hw ↦ ⟨hw.2, ht⟩)
  · change Ψ (F z, t - s) = _
    rw [hFz]
  · intro w hw
    exact extend_endpoint hV hδ hΨ hzero hcurve hw.2 ht (hend w hw.1)

end HolomorphicAnosov.W07FlowContinuation
