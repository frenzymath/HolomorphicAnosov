import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImagePointComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJetTransport

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov
open BoundedLipschitzJets

/-- HPS pp.54–55 and pp.33–34: contraction of local image graph jets.
The local inverse parameters H,J have the same horizontal image. The
pointwise graph comparison bounds the output difference by
(k+ε)/(1−aε) times the input difference at J(u). If J tends to zero and
has slope at most c, jet transport supplies the factor c. Taking
c=a/(1−aε) gives the parent's image-jet contraction coefficient. Only
eventual horizontal equations are needed, not global inverse identities. -/
theorem parameter_graph_image_jet_comparison
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (a k ε c : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a) (hk : ‖S‖ ≤ k)
    (hsmall : (a : ℝ) * ε < 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (s t : X → Y) (hs : LipschitzWith 1 s) (H J : U → X)
    (P : BoundedRepresentative X Y) (Q : BoundedRepresentative U V)
    (hP : ∀ x, (P : X → Y) x = s x - t x)
    (hQ : ∀ u, (Q : U → V) u =
      (G (H u,s (H u))).2 - (G (J u,t (J u))).2)
    (heq : ∀ᶠ u in 𝓝 (0 : U), (G (H u,s (H u))).1 = (G (J u,t (J u))).1)
    (hJ : ContinuousAt J 0) (hJ0 : J 0 = 0)
    (hJb : ∀ᶠ u in 𝓝 (0 : U), ‖J u‖ ≤ (c : ℝ) * ‖u‖) :
    ‖jetClass U V Q‖ ≤ ((k : ℝ) + ε) * c / (1 - (a : ℝ) * ε) *
      ‖jetClass X Y P‖ := by
  let b : NNReal := ⟨((k : ℝ) + ε) / (1 - (a : ℝ) * ε),
    div_nonneg (add_nonneg k.2 ε.2) (sub_pos.mpr hsmall).le⟩
  have hc : ∀ᶠ u in 𝓝 (0 : U),
      ‖(Q : U → V) u‖ ≤ (b : ℝ) * ‖(P : X → Y) (J u)‖ := by
    filter_upwards [heq] with u hu
    rw [hQ, hP]
    exact parameter_graph_image_point_comparison T S G a k ε ha hk hsmall hR
      s t hs (H u) (J u) hu
  have h := parameter_graph_jet_transport Q P J hJ hJ0 b c hJb hc
  change _ ≤ ((k : ℝ) + ε) / (1 - (a : ℝ) * ε) * (c : ℝ) * ‖jetClass X Y P‖ at h
  convert h using 1
  ring

end HolomorphicAnosov
