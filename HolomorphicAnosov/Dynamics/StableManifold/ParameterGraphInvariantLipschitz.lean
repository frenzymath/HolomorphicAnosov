import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierComplete
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageCarrier
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphStableLipschitz
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphContractionThreshold
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedPoint

/-!
# Parameter-dependent invariant Lipschitz graphs

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977),
Sublemma 5.2, printed pp.54–57, and Theorem 5.5 parameter insertion, p.62.
DAG node: `hps.parameter_graph_invariant_lipschitz_g12`.
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- The invariant Lipschitz graphs of HPS pp.54–57, with the moving-fibre parameter
insertion of p.62. The strict uniform linear bounds give one perturbation threshold
for both graph transforms. The centered unit-slope carriers are nonempty complete
metric spaces, so each transform has a fixed point. Evaluating these fixed points
recovers centered unit-Lipschitz maps, and the transform identities give exactly the
image and full-preimage graph equalities. Empty bases and zero fibres are included;
the lower linear block need not be invertible. -/
theorem parameter_graph_invariant_lipschitz
    {A : Type*} (E₁ E₂ : A → Type*)
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [∀ p, CompleteSpace (E₁ p)] [∀ p, CompleteSpace (E₂ p)]
    (h : A ≃ A) (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p)) (a k : NNReal) (ρ : ℝ)
    (hρ : 0 < ρ) (ha : (a : ℝ) < ρ⁻¹) (hk : (k : ℝ) < ρ)
    (hT₁ : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hT₂ : ∀ p, ‖T₂ p‖ ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p)),
        (∀ p, G p 0 = 0) →
        (∃ ε : NNReal, (ε : ℝ) < δ ∧ ∀ p,
          LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2))) →
        ∃ s : ∀ p, E₁ p → E₂ p, ∃ t : ∀ p, E₂ p → E₁ p,
          (∀ p, s p 0 = 0 ∧ t p 0 = 0 ∧
            LipschitzWith 1 (s p) ∧ LipschitzWith 1 (t p)) ∧
          (∀ p, G p '' Set.range (fun x ↦ (x, s p x)) =
            Set.range (fun x ↦ (x, s (h p) x))) ∧
          (∀ p, G p ⁻¹' Set.range (fun y ↦ (t (h p) y, y)) =
            Set.range (fun y ↦ (t p y, y))) := by
  classical
  obtain ⟨δ, hδ, hthreshold⟩ :=
    parameter_graph_contraction_threshold a k ρ a.2 k.2 hρ ha hk
  refine ⟨δ, hδ, ?_⟩
  intro G hG hLip
  obtain ⟨ε, hεδ, hR⟩ := hLip
  obtain ⟨hsmall, hden, hden₂, hq₁, hq₂, _, hslope, _⟩ :=
    hthreshold ε ε.2 hεδ
  let q₁ : NNReal := ⟨(a : ℝ) * ((k : ℝ) + ε) / (1 - (a : ℝ) * ε) ^ 2,
    by positivity⟩
  obtain ⟨Φ, hΦ, himage⟩ := parameter_graph_image_carrier E₁ E₂ h T₁ T₂ G hG
    a k ε q₁ hT₁ hT₂ (by linarith) hslope.le le_rfl hq₁ hR
  obtain ⟨t, ht, hpreimage⟩ := parameter_graph_stable_lipschitz E₁ E₂ h T₁ T₂ G hG
    a k ε hT₁ hT₂ hsmall hslope hq₂ hR
  obtain ⟨_, hsComplete, hsNonempty⟩ := parameter_graph_carrier_complete E₁ E₂
  let := hsComplete
  let : Nonempty {s : ParameterGraphCarrier E₁ E₂ // s ∈ parameterGraphUnitSet E₁ E₂} :=
    hsNonempty.to_subtype
  obtain ⟨s, hsfix, _⟩ := parameter_graph_fixedPoint Φ q₁ hΦ
  refine ⟨parameterGraphValue E₁ E₂ s.1, t, ?_, ?_, hpreimage⟩
  · intro p
    exact ⟨by simp [parameterGraphValue], (ht p).1, s.2 p, (ht p).2⟩
  · intro p
    simpa only [hsfix] using himage s p

end HolomorphicAnosov
