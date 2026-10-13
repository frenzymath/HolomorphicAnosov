import HolomorphicAnosov.Topology.ManningBowenInitialCoverUniformSaturation
import HolomorphicAnosov.Dynamics.Bowen.BracketCovarianceOfGuards

namespace HolomorphicAnosov.Dynamics.Bowen

open Set

/-- A uniform small radius makes the one-step bracket transport valid whenever
both source and image pairs lie in that radius. Source: Bowen (1970), Lemma 11(a),
with the compact closed-pair continuity margin in the parent proof's Step 2.
The bracket is controlled only on its given closed close-pair domain. -/
theorem exists_bracket_covariance_radius
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData f γ lam) :
    ∃ r : ℝ, 0 < r ∧ r ≤ H.closeRadius ∧
      ∀ x y : X, dist x y ≤ r → dist (f x) (f y) ≤ r →
        f (H.bracket x y) = H.bracket (f x) (f y) := by
  have hdiag (y : X) : H.bracket y y = y := by
    symm
    apply H.bracket_unique y y y (by simpa using H.closeRadius_pos.le)
    constructor <;> intro n <;> simpa using H.gamma_pos.le
  have hcore : IsCompact {p : X × X | dist p.1 p.2 ≤ H.closeRadius} :=
    (isClosed_le (continuous_fst.dist continuous_snd) continuous_const).isCompact
  have huc := hcore.uniformContinuousOn_of_continuous H.bracket_continuous
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) γ H.gamma_pos
  obtain ⟨η, hη, hηmod⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  refine ⟨min H.closeRadius (η / 2), lt_min H.closeRadius_pos (half_pos hη),
    min_le_left _ _, ?_⟩
  intro x y hxy hfxfy
  have hxycore := hxy.trans (min_le_left _ _)
  apply bracket_covariance_of_guards f γ lam H hxycore
    (hfxfy.trans (min_le_left _ _))
  apply (hfδ ?_).le
  have hyy : (y, y) ∈ {p : X × X | dist p.1 p.2 ≤ H.closeRadius} := by
    simpa using H.closeRadius_pos.le
  have hdist : dist (x, y) (y, y) < η := by
    simp only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact (hxy.trans (min_le_right _ _)).trans_lt (half_lt_self hη)
  simpa only [hdiag] using hηmod (x, y) hxycore (y, y) hyy hdist

end HolomorphicAnosov.Dynamics.Bowen
