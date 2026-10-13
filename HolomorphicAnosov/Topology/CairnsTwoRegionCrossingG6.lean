import Mathlib.Analysis.Normed.Module.Convex
import HolomorphicAnosov.Topology.PolygonEdgeLocalLine
import HolomorphicAnosov.Topology.TwoLocalSidesSeparation

open Set
namespace HolomorphicAnosov

/-- A single transverse edge crossing swaps the labels in any two disjoint open
regions covering the polygon complement and accumulating on every boundary point.
Source: Cairns (1951), Theorem 2.1, p.860. The two local half-balls have opposite
labels since both regions accumulate at the crossing; connectedness of the path
before and after the unique crossing propagates those labels to its endpoints. -/
theorem cairns_two_region_crossing_g6 {n : ℕ} (p : Polygon ℂ (n + 1))
    (hne : p.HasNondegenerateEdges)
    (hsimple : ∀ i j : Fin (n + 1), i ≠ j →
      p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
        p.vertices '' ({i, finRotate (n + 1) i} ∩ {j, finRotate (n + 1) j}))
    (Q E : Set ℂ) (h9 : IsOpen Q) (h10 : IsOpen E)
    (h5 : Disjoint Q E) (h4 : Q ∪ E = (p.boundary ℝ)ᶜ)
    (hclQ : p.boundary ℝ ⊆ closure Q) (hclE : p.boundary ℝ ⊆ closure E)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Icc 0 1)) (hfinj : InjOn f (Icc 0 1))
    (hcross : ∃ i : Fin (n + 1), ∃ t ∈ Ioo (0 : ℝ) 1,
      f '' Icc 0 1 ∩ p.boundary ℝ = {f t} ∧
      f t ∈ openSegment ℝ (p i) (p (finRotate (n + 1) i)) ∧
      ∃ δ > 0, δ < t ∧ δ < 1 - t ∧
        ∀ s ∈ Ioo (t - δ) t, ∀ u ∈ Ioo t (t + δ),
          (star (p (finRotate (n + 1) i) - p i) * (f s - p i)).im *
            (star (p (finRotate (n + 1) i) - p i) * (f u - p i)).im < 0) :
    (f 0 ∈ Q ∧ f 1 ∈ E) ∨ (f 0 ∈ E ∧ f 1 ∈ Q) := by
  classical
  let c := p.boundary ℝ
  obtain ⟨i, t, ht, hinter, hedge, δ, hδ, hδt, hδ1, hsign⟩ := hcross
  have havoid : ∀ s ∈ Icc (0 : ℝ) 1, s ≠ t → f s ∉ c := by
    intro s hs hst hmem
    have heq : f s = f t := by
      have : f s ∈ ({f t} : Set ℂ) := hinter ▸ ⟨⟨s, hs, rfl⟩, hmem⟩
      exact Set.mem_singleton_iff.mp this
    exact hst (hfinj hs ⟨ht.1.le, ht.2.le⟩ heq)
  have hleft : IsPreconnected (f '' Ico (0 : ℝ) t) :=
    isPreconnected_Ico.image f (hf.mono (by
      intro s hs
      exact ⟨hs.1, hs.2.le.trans ht.2.le⟩))
  have hright : IsPreconnected (f '' Ioc t (1 : ℝ)) :=
    isPreconnected_Ioc.image f (hf.mono (by
      intro s hs
      exact ⟨ht.1.le.trans hs.1.le, hs.2⟩))
  have hleftsub : f '' Ico (0 : ℝ) t ⊆ Q ∪ E := by
    rw [h4]
    rintro _ ⟨s, hs, rfl⟩
    exact havoid s ⟨hs.1, hs.2.le.trans ht.2.le⟩ hs.2.ne
  have hrightsub : f '' Ioc t (1 : ℝ) ⊆ Q ∪ E := by
    rw [h4]
    rintro _ ⟨s, hs, rfl⟩
    exact havoid s ⟨ht.1.le.trans hs.1.le, hs.2⟩ hs.1.ne'
  have hlocal : ∃ s ∈ Ico (0 : ℝ) t, ∃ u ∈ Ioc t (1 : ℝ),
      (f s ∈ Q ∧ f u ∈ E) ∨ (f s ∈ E ∧ f u ∈ Q) := by
    obtain ⟨ε, hε, hball⟩ := polygon_edge_local_line p hne hsimple i hedge
    let L : ℂ →ₗ[ℝ] ℝ :=
      Complex.imLm.comp (LinearMap.mulLeft ℝ (star (p (finRotate (n + 1) i) - p i)))
    have hL (z : ℂ) :
        (star (p (finRotate (n + 1) i) - p i) * (z - p i)).im = L z - L (p i) := by
      simp only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        mul_sub, Complex.sub_im]
      rfl
    let P := Metric.ball (f t) ε ∩ {z : ℂ | L (p i) < L z}
    let N := Metric.ball (f t) ε ∩ {z : ℂ | L z < L (p i)}
    have hP : IsPreconnected P :=
      ((convex_ball (f t) ε).inter (convex_halfSpace_gt L.isLinear (L (p i)))).isPreconnected
    have hN : IsPreconnected N :=
      ((convex_ball (f t) ε).inter (convex_halfSpace_lt L.isLinear (L (p i)))).isPreconnected
    have hsides : Metric.ball (f t) ε \ c = P ∪ N := by
      ext z
      constructor
      · rintro ⟨hzb, hzc⟩
        have hne : L z - L (p i) ≠ 0 := by
          rw [← hL]
          exact fun hz ↦ hzc ((hball z hzb).mpr hz)
        rcases lt_or_gt_of_ne (sub_ne_zero.mp hne) with hn | hp
        · exact Or.inr ⟨hzb, hn⟩
        · exact Or.inl ⟨hzb, hp⟩
      · rintro (⟨hzb, hp⟩ | ⟨hzb, hn⟩)
        · refine ⟨hzb, ?_⟩
          intro hzc
          have hz := (hball z hzb).mp hzc
          rw [hL] at hz
          exact (sub_pos.mpr hp).ne' hz
        · refine ⟨hzb, ?_⟩
          intro hzc
          have hz := (hball z hzb).mp hzc
          rw [hL] at hz
          exact (sub_neg.mpr hn).ne hz
    have hftc : f t ∈ c := by
      exact mem_iUnion.mpr ⟨i, by
        simpa only [Polygon.edgeSet, affineSegment_eq_segment] using
          openSegment_subset_segment ℝ _ _ hedge⟩
    have hlabels := two_local_sides_separation h9 h10 h5 h4
      (hclQ hftc)
      (hclE hftc)
      Metric.isOpen_ball (Metric.mem_ball_self hε) hP hN hsides
    have hft : ContinuousAt f t := hf.continuousAt (Icc_mem_nhds ht.1 ht.2)
    obtain ⟨ρ, hρ, hfρ⟩ := Metric.continuousAt_iff.mp hft ε hε
    let η := min δ ρ / 2
    have hη : 0 < η := half_pos (lt_min hδ hρ)
    have hηδ : η < δ := (half_lt_self (lt_min hδ hρ)).trans_le (min_le_left _ _)
    have hηρ : η < ρ := (half_lt_self (lt_min hδ hρ)).trans_le (min_le_right _ _)
    have hs : t - η ∈ Ico (0 : ℝ) t := ⟨by linarith, by linarith⟩
    have hu : t + η ∈ Ioc t (1 : ℝ) := ⟨by linarith, by linarith⟩
    have hsball : f (t - η) ∈ Metric.ball (f t) ε := by
      apply hfρ
      rw [Real.dist_eq]
      have habs : |t - η - t| = η := by rw [show t - η - t = -η by ring, abs_neg, abs_of_pos hη]
      rwa [habs]
    have huball : f (t + η) ∈ Metric.ball (f t) ε := by
      apply hfρ
      rw [Real.dist_eq]
      have habs : |t + η - t| = η := by rw [show t + η - t = η by ring, abs_of_pos hη]
      rwa [habs]
    have hprod := hsign (t - η) ⟨by linarith, by linarith⟩
      (t + η) ⟨by linarith, by linarith⟩
    rw [hL, hL] at hprod
    refine ⟨t - η, hs, t + η, hu, ?_⟩
    rcases mul_neg_iff.mp hprod with ⟨hspos, huneg⟩ | ⟨hsneg, hupos⟩
    · have hsP : f (t - η) ∈ P := ⟨hsball, sub_pos.mp hspos⟩
      have huN : f (t + η) ∈ N := ⟨huball, sub_neg.mp huneg⟩
      exact hlabels.elim (fun h ↦ Or.inl ⟨h.1 hsP, h.2 huN⟩)
        (fun h ↦ Or.inr ⟨h.1 hsP, h.2 huN⟩)
    · have hsN : f (t - η) ∈ N := ⟨hsball, sub_neg.mp hsneg⟩
      have huP : f (t + η) ∈ P := ⟨huball, sub_pos.mp hupos⟩
      exact hlabels.elim (fun h ↦ Or.inr ⟨h.2 hsN, h.1 huP⟩)
        (fun h ↦ Or.inl ⟨h.2 hsN, h.1 huP⟩)
  obtain ⟨s, hs, u, hu, hsu⟩ := hlocal
  have h0 : f 0 ∈ f '' Ico (0 : ℝ) t := ⟨0, ⟨le_rfl, ht.1⟩, rfl⟩
  have h1' : f 1 ∈ f '' Ioc t (1 : ℝ) := ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩
  have hsm : f s ∈ f '' Ico (0 : ℝ) t := ⟨s, hs, rfl⟩
  have hum : f u ∈ f '' Ioc t (1 : ℝ) := ⟨u, hu, rfl⟩
  rcases hleft.subset_or_subset h9 h10 h5 hleftsub with hL | hL <;>
    rcases hright.subset_or_subset h9 h10 h5 hrightsub with hR | hR
  · rcases hsu with hsu | hsu
    · exact (Set.disjoint_left.mp h5 (hR hum) hsu.2).elim
    · exact (Set.disjoint_left.mp h5 (hL hsm) hsu.1).elim
  · exact Or.inl ⟨hL h0, hR h1'⟩
  · exact Or.inr ⟨hL h0, hR h1'⟩
  · rcases hsu with hsu | hsu
    · exact (Set.disjoint_left.mp h5 hsu.1 (hL hsm)).elim
    · exact (Set.disjoint_left.mp h5 hsu.2 (hR hum)).elim

end HolomorphicAnosov
