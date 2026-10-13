import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Join
import HolomorphicAnosov.Topology.HalfSectorSegmentCompactConnected
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.LocallyConvex.Separation

open Set

namespace HolomorphicAnosov

/-- The hull used in Cairns's half-sector construction omits its apex when the
curve omits the apex and the apex is outside the opposite base segment.

Source: agent-written separation argument for Cairns (1951), §3 Case II, p.863.
Strictly separate the apex from the closed base segment. Every triangle point
other than the apex has a positive base coefficient, so its functional value
is strictly larger than that of the apex. Both sets of hull generators lie in
this strict half-space, which is convex; their convex hull therefore omits the
apex. The curve need not be closed, and the triangle may be degenerate. -/
theorem halfSector_hull_apex_notMem
    (M P D : ℂ) (C : Set ℂ) (hMC : M ∉ C)
    (hMbase : M ∉ segment ℝ D P) :
    M ∉ convexHull ℝ ((C ∩ convexHull ℝ {M, P, D}) ∪ segment ℝ D P) := by
  obtain ⟨f, u, hMu, hbase⟩ := geometric_hahn_banach_point_closed
    (convex_segment D P) (halfSector_segment_compact_connected D P).1.isClosed hMbase
  have htriangle : ∀ x ∈ convexHull ℝ {M, P, D}, x ≠ M → f M < f x := by
    intro x hx hxM
    rw [convexHull_insert (insert_nonempty P {D}), convexHull_pair,
      mem_convexJoin] at hx
    obtain ⟨a, ha, y, hy, r, s, hr, hs, hrs, hxy⟩ := hx
    have haM : a = M := mem_singleton_iff.mp ha
    subst a
    have hspos : 0 < s := lt_of_le_of_ne hs (by
      intro h
      have hr1 : r = 1 := by linarith
      apply hxM
      simp [← hxy, ← h, hr1])
    have hyf : f M < f y := hMu.trans (hbase y (by simpa [segment_symm] using hy))
    rw [← hxy, map_add, map_smul, map_smul]
    dsimp
    nlinarith [mul_pos hspos (sub_pos.mpr hyf),
      congrArg (fun t : ℝ ↦ t * f M) hrs]
  have hgen : (C ∩ convexHull ℝ {M, P, D}) ∪ segment ℝ D P ⊆
      {x | f M < f x} := by
    rintro x (hx | hx)
    · exact htriangle x hx.2 (fun h ↦ hMC (h ▸ hx.1))
    · exact hMu.trans (hbase x hx)
  have hHull := convexHull_min hgen
    (convex_halfSpace_gt f.toLinearMap.isLinear (f M))
  exact fun h ↦ (lt_irrefl (f M)) (hHull h)

end HolomorphicAnosov

