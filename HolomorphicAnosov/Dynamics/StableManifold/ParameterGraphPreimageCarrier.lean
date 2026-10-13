import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierRealization
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierMetric
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageStep
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphVerticalEstimate
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Full-preimage graph contraction on parameter families

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977),
Sublemma 5.2, pp.54–57, and parameter insertion in Theorem 5.5, p.62.
DAG node: `hps.parameter_graph_preimage_carrier_g12`.
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- HPS pp.56–57 and parameter insertion p.62: the full preimage transform is a
contraction on normalized centered unit-slope families. Solve each horizontal graph
equation with the preimage-step theorem, then normalize the resulting family. Compare
two solutions using the preimage estimate. Their vertical coordinate has norm at most
`(k+ε)‖y‖`, by centeredness, unit slope, and the vertical difference estimate. The weighted
carrier norm criterion converts the pointwise bound to a contraction. Only forward
evaluation at `h p` occurs, so no invertibility of `h` or of the lower block is required. -/
theorem parameter_graph_preimage_carrier
    {A : Type*} (E₁ E₂ : A → Type*)
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [∀ p, CompleteSpace (E₁ p)] (h : A → A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p)) (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p)) (hG : ∀ p, G p 0 = 0)
    (a k ε q : NNReal)
    (ha : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hk : ∀ p, ‖T₂ p‖ ≤ k)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hslope : (a : ℝ) * ((k : ℝ) + 2 * ε) < 1)
    (hcoeff : (a : ℝ) * ((k : ℝ) + ε) / (1 - 2 * (a : ℝ) * ε) ≤ q)
    (hq : q < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2))) :
    ∃ Φ : {s : ParameterGraphCarrier E₂ E₁ // s ∈ parameterGraphUnitSet E₂ E₁} →
        {s : ParameterGraphCarrier E₂ E₁ // s ∈ parameterGraphUnitSet E₂ E₁},
      ContractingWith q Φ ∧ ∀ s p,
        G p ⁻¹' Set.range (fun y ↦ (parameterGraphValue E₂ E₁ s.1 (h p) y, y)) =
          Set.range (fun y ↦ (parameterGraphValue E₂ E₁ (Φ s).1 p y, y)) := by
  classical
  let Z := {s : ParameterGraphCarrier E₂ E₁ // s ∈ parameterGraphUnitSet E₂ E₁}
  have hex (s : Z) : ∃ s' : Z, ∀ p,
      G p ⁻¹' Set.range (fun y ↦ (parameterGraphValue E₂ E₁ s.1 (h p) y, y)) =
        Set.range (fun y ↦ (parameterGraphValue E₂ E₁ s'.1 p y, y)) := by
    have hp (p : A) := parameter_graph_preimage_step (T₁ p) (T₂ p) (G p) (hG p)
      a k ε (ha p) (hk p) (by nlinarith [hsmall]) hslope (hR p)
      (parameterGraphValue E₂ E₁ s.1 (h p)) (by simp [parameterGraphValue]) (s.2 (h p))
    choose t ht0 ht heq using hp
    obtain ⟨r, hr, hvalue⟩ := parameter_graph_carrier_realization E₂ E₁ t ht0 ht
    refine ⟨⟨r, hr⟩, ?_⟩
    intro p
    simpa only [hvalue] using heq p
  choose Φ hΦ using hex
  have heq (s : Z) (p : A) (y : E₂ p) :
      (G p (parameterGraphValue E₂ E₁ (Φ s).1 p y, y)).1 =
        parameterGraphValue E₂ E₁ s.1 (h p)
          (G p (parameterGraphValue E₂ E₁ (Φ s).1 p y, y)).2 := by
    have hm : (parameterGraphValue E₂ E₁ (Φ s).1 p y, y) ∈
        G p ⁻¹' Set.range (fun v ↦ (parameterGraphValue E₂ E₁ s.1 (h p) v, v)) := by
      rw [hΦ s p]
      exact ⟨y, rfl⟩
    obtain ⟨v, hv⟩ := hm
    have hx := congrArg Prod.fst hv
    have hy := congrArg Prod.snd hv
    simpa only [← hy] using hx.symm
  refine ⟨Φ, ⟨hq, ?_⟩, hΦ⟩
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro s t
  simp only [Subtype.dist_eq, dist_eq_norm]
  apply (parameter_graph_carrier_norm_le_iff E₂ E₁ _ _ _ (by positivity)).2
  intro p y
  have hvertical : ‖(G p (parameterGraphValue E₂ E₁ (Φ t).1 p y, y)).2‖ ≤
      ((k : ℝ) + ε) * ‖y‖ := by
    have htbound : ‖parameterGraphValue E₂ E₁ (Φ t).1 p y‖ ≤ ‖y‖ := by
      simpa [parameterGraphValue] using ((Φ t).2 p).norm_sub_le y 0
    have hv := parameter_graph_vertical_estimate (T₁ p).toContinuousLinearMap
      (T₂ p) (G p) k ε (hk p) (hR p)
      (parameterGraphValue E₂ E₁ (Φ t).1 p y) 0 y 0
    simpa only [show G p (0, 0) = 0 from hG p, Prod.snd_zero, sub_zero,
      max_eq_right htbound, add_mul] using hv
  have hdiff : ∀ v, ‖parameterGraphValue E₂ E₁ s.1 (h p) v -
      parameterGraphValue E₂ E₁ t.1 (h p) v‖ ≤ ‖s.1 - t.1‖ * ‖v‖ :=
    (parameter_graph_carrier_norm_le_iff E₂ E₁ s.1 t.1 _ (norm_nonneg _)).1 le_rfl (h p)
  have hc := parameter_graph_preimage_comparison (T₁ p) (T₂ p) (G p)
    a k ε ‖s.1 - t.1‖₊ (ha p) hsmall (hR p)
    (parameterGraphValue E₂ E₁ s.1 (h p)) (parameterGraphValue E₂ E₁ t.1 (h p))
    (s.2 (h p)) hdiff (parameterGraphValue E₂ E₁ (Φ s).1 p y)
    (parameterGraphValue E₂ E₁ (Φ t).1 p y) y (heq s p y) (heq t p y) hvertical
  exact hc.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)) (norm_nonneg _))

end HolomorphicAnosov
