import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageStep
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageDerivative

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov

/-- HPS pp.56–58 and pp.33–34: construct the actual preimage representative
of a linear unit graph and identify its derivative. The full preimage step
gives a centered unit-Lipschitz graph, hence continuity. Exact graph equality
gives its horizontal equation. The continuous preimage derivative theorem
then identifies its derivative from the supplied invertible horizontal
linearization. Neither G nor its lower block is required to be invertible. -/
theorem parameter_graph_affine_preimage
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V)
    (G : X × Y → U × V) (hG : G 0 = 0)
    (a k ε : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a) (hk : ‖S‖ ≤ k)
    (hsmall : (a : ℝ) * (2 * ε) < 1)
    (hslope : (a : ℝ) * ((k : ℝ) + 2 * ε) < 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (P : V →L[ℝ] U) (hP : ‖P‖ ≤ 1)
    (F : X × Y →L[ℝ] U × V) (hF : HasFDerivAt G F 0)
    (J : X ≃L[ℝ] U)
    (hJ : ∀ x, J x = (F (x,0)).1 - P (F (x,0)).2) :
    ∃ s : Y → X, s 0 = 0 ∧ LipschitzWith 1 s ∧
      G ⁻¹' Set.range (fun v ↦ (P v,v)) = Set.range (fun y ↦ (s y,y)) ∧
      HasFDerivAt s
        (-(J.symm.toContinuousLinearMap.comp
          (((ContinuousLinearMap.fst ℝ U V).comp F -
            P.comp ((ContinuousLinearMap.snd ℝ U V).comp F)).comp
              (ContinuousLinearMap.inr ℝ X Y)))) 0 := by
  have hPlip : LipschitzWith 1 (P : V → U) := P.lipschitzWith_of_opNorm_le hP
  obtain ⟨s, hs0, hs, hgraph⟩ :=
    parameter_graph_preimage_step T S G hG a k ε ha hk hsmall hslope hR P P.map_zero hPlip
  refine ⟨s, hs0, hs, hgraph, ?_⟩
  have heq (y : Y) : (G (s y,y)).1 = P (G (s y,y)).2 := by
    have hm : (s y,y) ∈ G ⁻¹' Set.range (fun v ↦ (P v,v)) := by
      rw [hgraph]
      exact ⟨y,rfl⟩
    obtain ⟨v,hv⟩ := hm
    have h1 := congrArg Prod.fst hv
    have h2 := congrArg Prod.snd hv
    change P v = (G (s y,y)).1 at h1
    change v = (G (s y,y)).2 at h2
    exact h1.symm.trans (congrArg P h2)
  exact parameter_graph_preimage_derivative G P s 0 hs.continuous.continuousAt
    (Eventually.of_forall heq) F (by convert hF using 1; simp [hs0]) J hJ

end HolomorphicAnosov
