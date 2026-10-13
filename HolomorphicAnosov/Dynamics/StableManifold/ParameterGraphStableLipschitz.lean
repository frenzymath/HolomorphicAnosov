import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageCarrier
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierComplete
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedPoint

/-! A centered unit-Lipschitz invariant stable graph family is constructed by a parameterized graph transform (HPS, pp.56–57, 62). -/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- A centered unit-Lipschitz invariant full-preimage graph family (HPS, pp.56–57, 62). -/
theorem parameter_graph_stable_lipschitz
    {A : Type*} (E₁ E₂ : A → Type*)
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [∀ p, CompleteSpace (E₁ p)] (h : A → A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p)) (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p)) (hG : ∀ p, G p 0 = 0)
    (a k ε : NNReal)
    (ha : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hk : ∀ p, ‖T₂ p‖ ≤ k)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hslope : (a : ℝ) * ((k : ℝ) + 2 * ε) < 1)
    (hcoeff : (a : ℝ) * ((k : ℝ) + ε) / (1 - 2 * (a : ℝ) * ε) < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2))) :
    ∃ t : ∀ p, E₂ p → E₁ p,
      (∀ p, t p 0 = 0 ∧ LipschitzWith 1 (t p)) ∧
      ∀ p, G p ⁻¹' Set.range (fun y ↦ (t (h p) y, y)) =
        Set.range (fun y ↦ (t p y, y)) := by
  let q : NNReal := ⟨(a : ℝ) * ((k : ℝ) + ε) / (1 - 2 * (a : ℝ) * ε),
    div_nonneg (mul_nonneg a.2 (add_nonneg k.2 ε.2)) (sub_pos.mpr hsmall).le⟩
  obtain ⟨Φ, hΦ, hgraph⟩ := parameter_graph_preimage_carrier E₁ E₂ h T₁ T₂ G hG
    a k ε q ha hk hsmall hslope le_rfl hcoeff hR
  obtain ⟨_, hcomplete, hnonempty⟩ := parameter_graph_carrier_complete E₂ E₁
  have := hcomplete
  have : Nonempty {s : ParameterGraphCarrier E₂ E₁ // s ∈ parameterGraphUnitSet E₂ E₁} :=
    hnonempty.to_subtype
  obtain ⟨t, ht, _⟩ := parameter_graph_fixedPoint Φ q hΦ
  refine ⟨parameterGraphValue E₂ E₁ t.1, ?_, ?_⟩
  · intro p
    exact ⟨by simp [parameterGraphValue], t.2 p⟩
  · intro p
    simpa only [ht] using hgraph t p

end HolomorphicAnosov
