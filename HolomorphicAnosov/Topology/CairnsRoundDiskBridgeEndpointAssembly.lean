import HolomorphicAnosov.Topology.CairnsRoundDiskTwoWalkPolygonAssemblyResidual
import HolomorphicAnosov.Topology.CairnsPolygonCompletionRoundDisk
import HolomorphicAnosov.Topology.RoundDiskCrosscutGeometry
import HolomorphicAnosov.Topology.CairnsRoundDiskOppositeArcMarkers
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.UnitInterval

/-! # Endpoint selection and polygon assembly for the round-disk bridge

Source: Cairns (1951), Lemma 5.1, printed p.866.
DAG node: `topo.cairns_round_disk_bridge_endpoint_assembly_g20`.
-/

open Set Metric

namespace HolomorphicAnosov

/-- Under the failure-of-separation hypothesis, select one point on each complementary
circle arc and assemble the finite inner connector with an exterior connector into
Cairns's simple polygon certificate. The certificate records the exact finite data
needed by the subsequent crossing argument.

Source: Cairns p.866: choose a polygonal bridge between the two circle arcs avoiding
the crosscut, complete it outside the circle to a simple closed polygon, and retain
the two radial contacts. Select markers using the proved two-arc midpoint lemma.
Compactness of the crosscut image gives obstacle-free balls at those markers. Take
eta=min(epsilon,1)/2; the inward endpoint has distance eta from its marker and norm
1-eta, so convexity gives a short disjoint radial collar ending in the open disk.
The same-component hypothesis joins the inward endpoints in one component. Applying
the existing polygon-completion theorem gives the required polygon certificate.
Finite loop erasure and edge bookkeeping remain transitive prerequisites of that
completion theorem. -/
theorem cairns_round_disk_bridge_endpoint_assembly
    (g : unitInterval → closedBall (0 : ℂ) 1) (hg : Topology.IsEmbedding g)
    (h0 : (g 0 : ℂ) ∈ sphere (0 : ℂ) 1)
    (h1 : (g 1 : ℂ) ∈ sphere (0 : ℂ) 1) (h01 : g 0 ≠ g 1)
    (hinterior : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      (g t : ℂ) ∈ ball (0 : ℂ) 1)
    (hsame : ∀ x y : ℂ,
      x ∈ ball (0 : ℂ) 1 \
        (fun t : unitInterval ↦ (g t : ℂ)) ''
          {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} →
      y ∈ ball (0 : ℂ) 1 \
        (fun t : unitInterval ↦ (g t : ℂ)) ''
          {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} →
      connectedComponentIn (ball (0 : ℂ) 1 \
        (fun t : unitInterval ↦ (g t : ℂ)) ''
          {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) x =
      connectedComponentIn (ball (0 : ℂ) 1 \
        (fun t : unitInterval ↦ (g t : ℂ)) ''
          {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}) y) :
    ∃ a b : ℂ,
      a ∈ sphere (0 : ℂ) 1 \ ({(g 0 : ℂ), (g 1 : ℂ)} : Set ℂ) ∧
      b ∈ sphere (0 : ℂ) 1 \ ({(g 0 : ℂ), (g 1 : ℂ)} : Set ℂ) ∧
      b ∉ connectedComponentIn
        (sphere (0 : ℂ) 1 \ ({(g 0 : ℂ), (g 1 : ℂ)} : Set ℂ)) a ∧
      CairnsTwoWalkPolygonCertificate (Set.range (fun t : unitInterval ↦ (g t : ℂ))) a b := by
  obtain ⟨a, b, ha, hb, harcs⟩ :=
    cairns_round_disk_opposite_arc_markers g hg h0 h1 h01
  refine ⟨a, b, ha, hb, harcs, ?_⟩
  let γ : unitInterval → ℂ := fun t ↦ (g t : ℂ)
  let K := range γ
  obtain ⟨hcompact, hconnected, hcontacts, hopenimage, hdiff, hopen, hcaps⟩ :=
    roundDiskCrosscutGeometry γ (continuous_subtype_val.comp hg.continuous)
      h0 h1 hinterior
  have hcollar (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1 \ {γ 0, γ 1}) :
      ∃ η : ℝ, (0 < η ∧ η < 1) ∧ Disjoint (segment ℝ z ((1 - η) • z)) K ∧
        (1 - η) • z ∈ ball (0 : ℂ) 1 \ K := by
    have hzK : z ∉ K := fun h ↦ hz.2 (hcontacts ▸ ⟨h, hz.1⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcompact.isClosed.isOpen_compl z hzK
    let η := min ε 1 / 2
    have hη : 0 < η := half_pos (lt_min hε zero_lt_one)
    have hηε : η < ε := (half_lt_self (lt_min hε zero_lt_one)).trans_le (min_le_left _ _)
    have hη1 : η < 1 := (half_lt_self (lt_min hε zero_lt_one)).trans_le (min_le_right _ _)
    have hnorm : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz.1
    have hnear : (1 - η) • z ∈ ball z ε := by
      rw [mem_ball, dist_eq_norm,
        show (1 - η) • z - z = (-η) • z by
          rw [sub_smul, one_smul, sub_sub_cancel_left, neg_smul],
        norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hη, hnorm, mul_one]
      exact hηε
    have hseg : segment ℝ z ((1 - η) • z) ⊆ Kᶜ :=
      ((convex_ball z ε).segment_subset (mem_ball_self hε) hnear).trans hball
    refine ⟨η, ⟨hη, hη1⟩, disjoint_left.mpr (fun w hw hwK ↦ hseg hw hwK), ?_⟩
    refine ⟨?_, hseg (right_mem_segment ℝ _ _)⟩
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hη1), hnorm, mul_one]
    exact sub_lt_self _ hη
  obtain ⟨ηa, hηa, hca, hxa⟩ := hcollar a ha
  obtain ⟨ηb, hηb, hcb, hxb⟩ := hcollar b hb
  have hsameK : connectedComponentIn (ball (0 : ℂ) 1 \ K) ((1 - ηa) • a) =
      connectedComponentIn (ball (0 : ℂ) 1 \ K) ((1 - ηb) • b) := by
    rw [← hdiff] at hxa hxb ⊢
    exact hsame _ _ hxa hxb
  have hcomponent : (1 - ηb) • b ∈
      connectedComponentIn (ball (0 : ℂ) 1 \ K) ((1 - ηa) • a) := by
    rw [hsameK]
    exact mem_connectedComponentIn hxb
  have hKdisk : K ⊆ closedBall (0 : ℂ) 1 := by
    rintro z ⟨t, rfl⟩
    exact (g t).property
  obtain ⟨n, P, hn, hinj, hnd, hint, hdisj, hcircle, htrans, hcl⟩ :=
    cairns_polygon_completion_across_round_disk K hcompact hKdisk (γ 0) (γ 1) a b
      h0 h1 (fun h ↦ h01 (Subtype.ext h)) hcontacts ha hb harcs
      ηa ηb hηa hηb hca hcb hcomponent
  refine ⟨n, P, hn, hinj, hnd, hint, hdisj, hcircle, ?_⟩
  intro z hz
  obtain ⟨i, r, s, hr, hs, hseg, hdot⟩ := htrans z hz
  exact ⟨i, r, s, hr, hs, hseg⟩

end HolomorphicAnosov

