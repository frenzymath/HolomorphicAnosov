import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Compact image and boundary contacts of a round-disk crosscut

Source: Cairns (1951), Lemma 5.1, p.866, opening round-disk reduction.
Injectivity is unnecessary for these preliminary facts: continuity and the
locations of the endpoints and interior suffice.
-/

open Set Metric

namespace HolomorphicAnosov

/-- A continuous arc with endpoints on the unit circle and all other points in
the open disk has compact connected image, precisely the two prescribed circle
contacts, and an open complement in the disk after removal of its open arc.

Source: the compactness and boundary-contact step in the round-disk case of
Cairns, Lemma 5.1, p.866. Continuity sends the compact connected interval to a
compact connected image. An interior parameter cannot map to the circle because
the ball and sphere are disjoint, so every circle contact is an endpoint.
Conversely each endpoint is a circle contact. A parameter whose image is in the
ball is neither endpoint, hence is strictly between zero and one. Thus the ball
meets the full image exactly in the open-parameter image. Removing either image
from the ball gives the same set, which is open because the full image is closed.
Every circle point away from the endpoints is outside the compact image, and
thus has a ball missing that image. Its inward cap is convex and nonempty, since
the circle point is in the closure of the open disk. The proof allows coincident
endpoints and noninjective paths. -/
theorem roundDiskCrosscutGeometry
    (γ : unitInterval → ℂ) (hγ : Continuous γ)
    (h0 : γ 0 ∈ sphere (0 : ℂ) 1) (h1 : γ 1 ∈ sphere (0 : ℂ) 1)
    (hinterior : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      γ t ∈ ball (0 : ℂ) 1) :
    let K := range γ
    let Kopen := γ '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
    IsCompact K ∧ IsConnected K ∧
      K ∩ sphere (0 : ℂ) 1 = {γ 0, γ 1} ∧
      K ∩ ball (0 : ℂ) 1 = Kopen ∧
      ball (0 : ℂ) 1 \ Kopen = ball (0 : ℂ) 1 \ K ∧
      IsOpen (ball (0 : ℂ) 1 \ Kopen) ∧
      (∀ a ∈ sphere (0 : ℂ) 1, a ≠ γ 0 → a ≠ γ 1 →
        ∃ ε : ℝ, 0 < ε ∧ Disjoint (ball a ε) K ∧
          IsConnected (ball a ε ∩ ball (0 : ℂ) 1)) := by
  dsimp only
  have hcompact : IsCompact (range γ) := isCompact_range hγ
  have hcontacts : range γ ∩ sphere (0 : ℂ) 1 = {γ 0, γ 1} := by
    apply Subset.antisymm
    · rintro z ⟨⟨t, rfl⟩, ht⟩
      by_cases ht0 : t = 0
      · simp [ht0]
      by_cases ht1 : t = 1
      · simp [ht1]
      have hlt0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
        (fun h ↦ ht0 (Subtype.ext h.symm))
      have hlt1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
        (fun h ↦ ht1 (Subtype.ext h))
      exact False.elim (Set.disjoint_left.1 sphere_disjoint_ball ht
        (hinterior t hlt0 hlt1))
    · intro z hz
      rcases mem_insert_iff.1 hz with rfl | hz
      · exact ⟨mem_range_self 0, h0⟩
      · have hz' := mem_singleton_iff.1 hz
        subst z
        exact ⟨mem_range_self 1, h1⟩
  have hopenimage : range γ ∩ ball (0 : ℂ) 1 =
      γ '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} := by
    apply Subset.antisymm
    · rintro z ⟨⟨t, rfl⟩, ht⟩
      have ht0 : t ≠ 0 := by
        intro heq
        exact Set.disjoint_left.1 sphere_disjoint_ball h0 (heq ▸ ht)
      have ht1 : t ≠ 1 := by
        intro heq
        exact Set.disjoint_left.1 sphere_disjoint_ball h1 (heq ▸ ht)
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · exact lt_of_le_of_ne t.property.1 (fun h ↦ ht0 (Subtype.ext h.symm))
      · exact lt_of_le_of_ne t.property.2 (fun h ↦ ht1 (Subtype.ext h))
    · rintro z ⟨t, ⟨ht0, ht1⟩, rfl⟩
      exact ⟨mem_range_self t, hinterior t ht0 ht1⟩
  have hdiff : ball (0 : ℂ) 1 \
      γ '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} =
      ball (0 : ℂ) 1 \ range γ := by
    rw [← hopenimage]
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  exact ⟨hcompact, isConnected_range hγ, hcontacts, hopenimage, hdiff,
    hdiff ▸ isOpen_ball.sdiff hcompact.isClosed, fun a ha ha0 ha1 ↦ by
      have haK : a ∉ range γ := by
        intro h
        have : a ∈ ({γ 0, γ 1} : Set ℂ) := hcontacts ▸ ⟨h, ha⟩
        simp [ha0, ha1] at this
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcompact.isClosed.isOpen_compl a haK
      refine ⟨ε, hε, disjoint_left.2 (fun z hz hzK ↦ hball hz hzK), ?_⟩
      apply ((convex_ball a ε).inter (convex_ball (0 : ℂ) 1)).isConnected
      apply (_root_.mem_closure_iff.1 ?_) (ball a ε) isOpen_ball (mem_ball_self hε)
      rw [closure_ball (0 : ℂ) one_ne_zero]
      exact sphere_subset_closedBall ha⟩

end HolomorphicAnosov
