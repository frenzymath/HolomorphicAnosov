import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierRealization
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierMetric
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageStep
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageWeightedComparison
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Image graph transform on the normalized parameter carrier

Source: Hirsch–Pugh–Shub, Invariant Manifolds (1977), Sublemma 5.2 and
its graph-transform estimates, pp.54–57, and parameter insertion on p.62.
DAG node: `hps.parameter_graph_image_carrier_g12`.
The dependent normalized carrier preserves each original fibre norm. The
base bijection reindexes the source-wise graph images to receiving fibres.
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- HPS Sublemma 5.2, pp.54–55, with parameter insertion p.62: the image transform
is a contraction on normalized centered unit-slope families. Construct each image graph
by the single-fibre horizontal inverse, reindex the receiving fibres with the base
bijection, and normalize. For two output values at a common horizontal coordinate,
choose their source graph points using the image identity. The inverse horizontal
estimate bounds the second source coordinate; the weighted comparison then gives
`a(k+ε)/(1-aε)^2` times the input carrier distance. No vertical inverse is used. -/
theorem parameter_graph_image_carrier
    {A : Type*} (E₁ E₂ : A → Type*)
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [∀ p, CompleteSpace (E₁ p)] (h : A ≃ A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p)) (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p)) (hG : ∀ p, G p 0 = 0)
    (a k ε q : NNReal)
    (ha : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hk : ∀ p, ‖T₂ p‖ ≤ k)
    (hsmall : (a : ℝ) * ε < 1)
    (hslope : (a : ℝ) * ((k : ℝ) + 2 * ε) ≤ 1)
    (hcoeff : (a : ℝ) * ((k : ℝ) + ε) / (1 - (a : ℝ) * ε) ^ 2 ≤ q)
    (hq : q < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2))) :
    ∃ Φ : {s : ParameterGraphCarrier E₁ E₂ // s ∈ parameterGraphUnitSet E₁ E₂} →
        {s : ParameterGraphCarrier E₁ E₂ // s ∈ parameterGraphUnitSet E₁ E₂},
      ContractingWith q Φ ∧ ∀ s p,
        G p '' Set.range (fun x ↦ (x, parameterGraphValue E₁ E₂ s.1 p x)) =
          Set.range (fun x ↦ (x, parameterGraphValue E₁ E₂ (Φ s).1 (h p) x)) := by
  classical
  let Z := {s : ParameterGraphCarrier E₁ E₂ // s ∈ parameterGraphUnitSet E₁ E₂}
  have hex (s : Z) : ∃ s' : Z, ∀ p,
      G p '' Set.range (fun x ↦ (x, parameterGraphValue E₁ E₂ s.1 p x)) =
        Set.range (fun x ↦ (x, parameterGraphValue E₁ E₂ s'.1 (h p) x)) := by
    have hp (p : A) := parameter_graph_image_step (T₁ p) (T₂ p) (G p) (hG p)
      a k ε (ha p) (hk p) hsmall hslope (hR p)
      (parameterGraphValue E₁ E₂ s.1 p) (by simp [parameterGraphValue]) (s.2 p)
    choose H t hH hH0 hinv ht0 ht heq using hp
    let t' : ∀ p, E₁ p → E₂ p := Equiv.piCongrLeft (fun p ↦ E₁ p → E₂ p) h t
    have ht' (p : A) : t' (h p) = t p := by
      simp only [t', Equiv.piCongrLeft_apply_apply]
    have ht'0 (p : A) : t' p 0 = 0 := by
      obtain ⟨p, rfl⟩ := h.surjective p
      rw [ht']
      exact ht0 p
    have ht'lip (p : A) : LipschitzWith 1 (t' p) := by
      obtain ⟨p, rfl⟩ := h.surjective p
      rw [ht']
      exact ht p
    obtain ⟨r, hr, hvalue⟩ := parameter_graph_carrier_realization E₁ E₂ t' ht'0 ht'lip
    refine ⟨⟨r, hr⟩, ?_⟩
    intro p
    simpa only [hvalue, ht'] using heq p
  choose Φ hΦ using hex
  refine ⟨Φ, ⟨hq, ?_⟩, hΦ⟩
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro s t
  simp only [Subtype.dist_eq, dist_eq_norm]
  apply (parameter_graph_carrier_norm_le_iff E₁ E₂ _ _ _ (by positivity)).2
  intro p u
  obtain ⟨p, rfl⟩ := h.surjective p
  have hmem (s : Z) : (u, parameterGraphValue E₁ E₂ (Φ s).1 (h p) u) ∈
      G p '' Set.range (fun x ↦ (x, parameterGraphValue E₁ E₂ s.1 p x)) := by
    rw [hΦ s p]
    exact ⟨u, rfl⟩
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hmem s
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hmem t
  have hdiff : ∀ v, ‖parameterGraphValue E₁ E₂ s.1 p v -
      parameterGraphValue E₁ E₂ t.1 p v‖ ≤ ‖s.1 - t.1‖ * ‖v‖ :=
    (parameter_graph_carrier_norm_le_iff E₁ E₂ s.1 t.1 _ (norm_nonneg _)).1 le_rfl p
  obtain ⟨H, _, hH, hH0, hinv, _⟩ := parameter_graph_image_step
    (T₁ p) (T₂ p) (G p) (hG p) a k ε (ha p) (hk p) hsmall hslope (hR p)
    (parameterGraphValue E₁ E₂ t.1 p) (by simp [parameterGraphValue]) (t.2 p)
  have hHy : H y = u := (hH y).trans (congrArg Prod.fst hy)
  have hybound : ‖y‖ ≤ (a : ℝ) / (1 - (a : ℝ) * ε) * ‖u‖ := by
    have hb := hinv (H y) (H 0)
    simp only [Homeomorph.symm_apply_apply] at hb
    simpa only [hHy, hH0, sub_zero] using hb
  have hc := parameter_graph_image_weighted_comparison (T₁ p) (T₂ p) (G p)
    a k ε ‖s.1 - t.1‖₊ (ha p) (hk p) hsmall (hR p)
    (parameterGraphValue E₁ E₂ s.1 p) (parameterGraphValue E₁ E₂ t.1 p)
    (s.2 p) hdiff x y u (congrArg Prod.fst hx) (congrArg Prod.fst hy) hybound
  rw [hx, hy] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)) (norm_nonneg _))

end HolomorphicAnosov
