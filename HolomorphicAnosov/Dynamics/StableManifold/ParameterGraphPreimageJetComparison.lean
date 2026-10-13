import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimagePointComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJetTransport

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov
open BoundedLipschitzJets

/-- HPS pp.57–58: contraction of the local preimage graph jets. Center the
receiving and output graph differences at their common anchor. The graph
equations are required only near that anchor. The pointwise comparison
gives the inverse horizontal factor a/(1−2aε). The actual vertical return
has slope at most c and tends to zero; jet transport gives the additional
factor c. In the parent application c=k+ε. A singular return is allowed. -/
theorem parameter_graph_preimage_jet_comparison
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : X ≃L[ℝ] U) (S : Y →L[ℝ] V) (G : X × Y → U × V)
    (a ε c : NNReal) (ha : ‖T.symm.toContinuousLinearMap‖ ≤ a)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hR : LipschitzWith ε (fun z ↦ G z - (T z.1, S z.2)))
    (t t' : V → U) (ht : LipschitzWith 1 t) (s s' : Y → X)
    (P : BoundedRepresentative V U) (Q : BoundedRepresentative Y X)
    (hP : ∀ v, (P : V → U) v = t v - t' v)
    (hQ : ∀ y, (Q : Y → X) y = s y - s' y)
    (heq : ∀ᶠ y in 𝓝 (0 : Y),
      (G (s y,y)).1 = t (G (s y,y)).2 ∧
      (G (s' y,y)).1 = t' (G (s' y,y)).2)
    (hK : ContinuousAt (fun y ↦ (G (s' y,y)).2) 0)
    (hK0 : (G (s' 0,0)).2 = 0)
    (hKb : ∀ᶠ y in 𝓝 (0 : Y), ‖(G (s' y,y)).2‖ ≤ (c : ℝ) * ‖y‖) :
    ‖jetClass Y X Q‖ ≤ (a : ℝ) * c / (1 - 2 * (a : ℝ) * ε) *
      ‖jetClass V U P‖ := by
  let b : NNReal := ⟨(a : ℝ) / (1 - 2 * (a : ℝ) * ε),
    div_nonneg a.2 (sub_pos.mpr hsmall).le⟩
  have hc : ∀ᶠ y in 𝓝 (0 : Y),
      ‖(Q : Y → X) y‖ ≤ (b : ℝ) * ‖(P : V → U) (G (s' y,y)).2‖ := by
    filter_upwards [heq] with y hy
    rw [hQ, hP]
    exact parameter_graph_preimage_point_comparison T S G a ε ha hsmall hR
      t t' ht (s y) (s' y) y hy.1 hy.2
  have h := parameter_graph_jet_transport Q P (fun y ↦ (G (s' y,y)).2)
    hK hK0 b c hKb hc
  change _ ≤ (a : ℝ) / (1 - 2 * (a : ℝ) * ε) * (c : ℝ) * ‖jetClass V U P‖ at h
  convert h using 1
  ring

end HolomorphicAnosov
