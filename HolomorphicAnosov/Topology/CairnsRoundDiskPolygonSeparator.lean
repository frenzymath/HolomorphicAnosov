import HolomorphicAnosov.Topology.CairnsRoundDiskBridgeEndpointAssembly
import HolomorphicAnosov.Topology.CircleRadialEdgeCrossing
import HolomorphicAnosov.Topology.CairnsContinuousPolygonCrossing

/-!
# Opposite-side contradiction for a round-disk crosscut

Source: Cairns (1951), Lemma 5.1, p.866, polygonal crossing argument.
DAG node: `topo.cairns_round_disk_polygon_separator_g20`.
-/

open Set Metric
namespace HolomorphicAnosov

/-- The open-disk complement of an embedded crosscut cannot have all its points
in one connected-component class.

Source: Cairns (1951), Lemma 5.1 p.866. The assumed failure of separation
supplies the polygon certificate, disjoint from the crosscut and meeting the
unit circle at one radial contact in each of its two complementary arcs.
The directed-circle selection lemma chooses the closed arc through the first
contact and excludes the other. The radial determinant calculation makes
this a single transverse polygon crossing, so its endpoints lie in different
polygon-complement components. The crosscut image is connected, disjoint from
the polygon, and contains both endpoints. Its containment in one component
contradicts that crossing conclusion. -/
theorem cairns_round_disk_polygon_separator
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
    False := by
  obtain ⟨a, b, ha, hb, harcs, n, P, hn, hinj, hnd, hint, hdisj, hcircle, hrad⟩ :=
    cairns_round_disk_bridge_endpoint_assembly g hg h0 h1 h01 hinterior hsame
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hp : IsSimpleClosedPolygon P := by
    refine ⟨hn, hinj, hnd, ?_⟩
    intro i j hij
    rw [Set.image_inter hinj, Set.image_pair, Set.image_pair]
    exact (hint i j hij).le
  let u : Circle := ⟨(g 0 : ℂ), h0⟩
  let v : Circle := ⟨(g 1 : ℂ), h1⟩
  have huv : u ≠ v := by
    intro h
    exact h01 (Subtype.ext (congrArg (fun z : Circle ↦ (z : ℂ)) h))
  obtain ⟨x, y, hends, hxy, t, ht, hat, havoid⟩ :=
    circleAngularArc_select u v huv a b ha hb harcs
  obtain ⟨i, r, q, hr, hq, hedge⟩ := hrad a (mem_insert _ _)
  have hcross := circleAngularArc_crossesPolygonOnce P x y hxy a b t ht hat havoid
    hcircle i r q hr hq (hnd i) hedge
  have hsep := cairns_continuous_polygon_crossing P hp (circleAngularArc x y)
    (circleAngularArc_continuous x y).continuousOn (circleAngularArc_injOn x y hxy) hcross
  rw [circleAngularArc_zero, circleAngularArc_one] at hsep
  let K := Set.range (fun t : unitInterval ↦ (g t : ℂ))
  have hconn : IsPreconnected K :=
    isPreconnected_range (continuous_subtype_val.comp hg.continuous)
  have hKsub : K ⊆ (P.boundary ℝ)ᶜ := by
    intro z hz
    exact fun hzP ↦ Set.disjoint_left.mp hdisj hzP hz
  have hpair : ({(x : ℂ), (y : ℂ)} : Set ℂ) ⊆ K := by
    rw [hends]
    rintro z (hz | hz)
    · exact hz ▸ Set.mem_range_self 0
    · exact hz ▸ Set.mem_range_self 1
  have hxK : (x : ℂ) ∈ K := hpair (Set.mem_insert _ _)
  have hyK : (y : ℂ) ∈ K := hpair (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact hsep (connectedComponentIn_eq (hconn.subset_connectedComponentIn hxK hKsub hyK))

end HolomorphicAnosov
