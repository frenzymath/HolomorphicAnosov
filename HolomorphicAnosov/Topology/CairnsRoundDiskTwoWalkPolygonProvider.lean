import HolomorphicAnosov.Topology.CircleComplementRegions
import HolomorphicAnosov.Topology.CairnsRoundDiskTwoWalkPolygonAssemblyResidual
import HolomorphicAnosov.Topology.OpenConnectedSegmentChain
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic

open Set

namespace HolomorphicAnosov

/--
Named residual provider for the finite two-walk polygon assembly in Cairns's
round-disk completion.

Source: Stewart S. Cairns, *An Elementary Proof of the Jordan-Schoenflies
Theorem* (1951), Lemma 5.1 and the polygonal-completion paragraph on printed
p.866 (PDF p.8).  Cairns states that the interior connector can be completed
outside the round circle, but leaves the finite subdivision, loop-erasure,
radial-stub retention, cyclic vertex enumeration, and exact edge-intersection
bookkeeping implicit.  This provider isolates precisely that omitted finite
assembly after the parent has supplied the compact obstacle, the finite inner
connector chain, the far exterior chain, and the local radial clearance.

Proof plan (the remaining implementation obligation): subdivide the two finite
segment chains at all endpoints and pairwise intersections, retain the radial
collar subedges at `a` and `b`, and erase loops in each finite embedded graph by
shortest-path selection.  The inner and exterior chains lie on opposite sides
of the unit circle away from the contacts; local clearance keeps the retained
radial germs disjoint from the other edges.  Concatenate the two vertex-simple
walks cyclically.  At each contact, merge the collinear inward and outward
subedges with the redundant-vertex deletion argument.  The resulting cyclic
array has injective vertices, nondegenerate edges, exact pairwise edge
intersections, obstacle-disjoint boundary, and circle intersection `{a,b}`.
The retained radial edges put each contact in an open segment, and their
positive radial scalar difference gives the later transversality calculation.
All post-assembly closure and arc conclusions are proved by the parent.

The assumptions are the exact local data established immediately before the
parent's `hpolygon` goal.  This theorem is intentionally a named provider with
one documented `sorry`; it does not alter or weaken the target statement.
Dependencies: `topo.open_preconnected_segment_chain_g10`,
`topo.circle_complement_regions_g6`, `mathlib.convex_closedBall_g6`, and the
proved polygon deletion/intersection APIs used by the finite cleanup.
-/
theorem cairns_round_disk_two_walk_polygon_provider
    (K : Set ℂ) (hK : IsCompact K)
    (hKdisk : K ⊆ Metric.closedBall (0 : ℂ) 1)
    (u v a b : ℂ) (hu : u ∈ Metric.sphere (0 : ℂ) 1)
    (hv : v ∈ Metric.sphere (0 : ℂ) 1) (huv : u ≠ v)
    (hKcircle : K ∩ Metric.sphere (0 : ℂ) 1 = {u, v})
    (ha : a ∈ Metric.sphere (0 : ℂ) 1 \ {u, v})
    (hb : b ∈ Metric.sphere (0 : ℂ) 1 \ {u, v})
    (harcs : b ∉ connectedComponentIn (Metric.sphere (0 : ℂ) 1 \ {u, v}) a)
    (eta_a eta_b : ℝ) (heta_a : 0 < eta_a ∧ eta_a < 1)
    (heta_b : 0 < eta_b ∧ eta_b < 1)
    (hcollar_a : Disjoint (segment ℝ a ((1 - eta_a) • a)) K)
    (hcollar_b : Disjoint (segment ℝ b ((1 - eta_b) • b)) K)
    (hcomponent : (1 - eta_b) • b ∈
      connectedComponentIn (Metric.ball (0 : ℂ) 1 \ K) ((1 - eta_a) • a))
    (S : Finset (ℂ × ℂ))
    (hSwalk : Relation.ReflTransGen (fun p q ↦ (p, q) ∈ S)
      ((1 - eta_a) • a) ((1 - eta_b) • b))
    (hSdisk : (⋃ q ∈ S, segment ℝ q.1 q.2) ⊆
      Metric.ball (0 : ℂ) 1 \ K)
    (hScompact : IsCompact (⋃ q ∈ S, segment ℝ q.1 q.2))
    (hclearance : ∀ z ∈ ({a, b} : Set ℂ), ∃ δ : ℝ,
      0 < δ ∧ Metric.closedBall z δ ⊆
        (⋃ q ∈ S, segment ℝ q.1 q.2)ᶜ)
    (hexterior_far : Relation.ReflTransGen
      (fun p q : ℂ ↦ segment ℝ p q ⊆ (Metric.closedBall (0 : ℂ) 2)ᶜ)
      ((4 : ℝ) • a) ((4 : ℝ) • b))
    (houteravoid : ∀ z ∈ ({a, b} : Set ℂ),
      Disjoint (segment ℝ z ((4 : ℝ) • z)) K)
    (hprotected_crossing : ∀ z ∈ ({a, b} : Set ℂ), ∃ ε : ℝ,
      0 < ε ∧ ε < eta_a ∧ ε < eta_b ∧ ε < 1 / 2 ∧
      z ∈ openSegment ℝ ((1 - ε) • z) ((1 + ε) • z) ∧
      Disjoint (segment ℝ ((1 - ε) • z) ((1 + ε) • z))
        (⋃ q ∈ S, segment ℝ q.1 q.2) ∧
      ∀ p q : ℂ, segment ℝ p q ⊆ (Metric.closedBall (0 : ℂ) 2)ᶜ →
        Disjoint (segment ℝ ((1 - ε) • z) ((1 + ε) • z)) (segment ℝ p q)) :
    ∃ (n : ℕ) (P : Polygon ℂ n),
      3 ≤ n ∧ Function.Injective P.vertices ∧ P.HasNondegenerateEdges ∧
      (∀ i j : Fin n, i ≠ j →
        P.edgeSet ℝ i ∩ P.edgeSet ℝ j =
          ({P i, P (finRotate n i)} ∩ {P j, P (finRotate n j)})) ∧
      Disjoint (P.boundary ℝ) K ∧
      P.boundary ℝ ∩ Metric.sphere (0 : ℂ) 1 = {a, b} ∧
      (∀ z ∈ ({a, b} : Set ℂ), ∃ (i : Fin n) (r s : ℝ),
        P i = r • z ∧ P (finRotate n i) = s • z ∧
        z ∈ openSegment ℝ (P i) (P (finRotate n i))) := by
  have c : CairnsTwoWalkPolygonCertificate K a b := cairns_round_disk_two_walk_polygon_assembly_residual
    (K := K) (_hK := hK) (hKdisk := hKdisk) (u := u) (v := v)
    (a := a) (b := b) (_hu := hu) (_hv := hv) (_huv := huv)
    (_hKcircle := hKcircle) (ha := ha) (hb := hb) (harcs := harcs)
    (eta_a := eta_a) (eta_b := eta_b) (heta_a := heta_a)
    (heta_b := heta_b) (hcollar_a := hcollar_a)
    (hcollar_b := hcollar_b) (hcomponent := hcomponent) (S := S)
    (hSwalk := hSwalk) (hSdisk := hSdisk) (_hScompact := hScompact)
    (hclearance := hclearance) (hexterior_far := hexterior_far)
    (houteravoid := houteravoid)
    (hprotected_crossing := hprotected_crossing)
  exact c

end HolomorphicAnosov
