import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray
import HolomorphicAnosov.Geometry.SmoothLocalFlow
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.TangentHausdorff

/-!
Reusable GeodesicInitial declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Every actual initial tangent vector has a geodesic on an open interval about zero. The trajectory is the projection of the chosen connection spray's genuine local flow. -/
lemma exists_connectionGeodesic_initial (nabla : SmoothAffineConnection E M)
    (z : TangentBundle 𝓘(ℝ, E) M) :
    ∃ (J : Set ℝ) (γ : ℝ → M), IsOpen J ∧ OrdConnected J ∧ (0 : ℝ) ∈ J ∧
      IsConnectionGeodesicOn nabla γ J ∧ curveTangentLift (E := E) γ 0 = z := by
  obtain ⟨G, hG, hGc, hGu, hG0, hGcurve⟩ := exists_connectionGeodesicSpray nabla
  let : T2Space (TangentBundle 𝓘(ℝ, E) M) := tangentBundle_t2Space
  obtain ⟨U, δ, Ψ, hU, hzU, hδ, hΨ, hΨ0, hΨcurve, huniq, hgroup, hdiff⟩ :=
    exists_smoothLocalFlow (𝓘(ℝ, E)).tangent G hG z
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hinput : ContMDiff 𝓘(ℝ, ℝ) ((𝓘(ℝ, E)).tangent.prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ ↦ (z, t)) := contMDiff_const.prodMk contMDiff_id
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
      (fun t : ℝ ↦ Ψ (z, t)) (Ioo (-δ) δ) :=
    hΨ.comp hinput.contMDiffOn (fun t ht ↦ ⟨hzU, ht⟩)
  have hgeo := (hGcurve (Ioo (-δ) δ) isOpen_Ioo ordConnected_Ioo _ hc).mp
    (hΨcurve z hzU)
  refine ⟨Ioo (-δ) δ, (fun t ↦ (Ψ (z, t)).proj), isOpen_Ioo,
    ordConnected_Ioo, hzero, hgeo.1, ?_⟩
  exact (hgeo.2 hzero).symm.trans (hΨ0 z hzU)

end
end HolomorphicAnosov
