import HolomorphicAnosov.Topology.Homology.CanonicalNonzeroLocalFamily
import HolomorphicAnosov.Topology.Homology.CompactChartSupport

/-!
# CanonicalNonzeroLocalFamilyCompatible

DAG node: `topo.mod2_canonical_local_family_compatible`.
Source: Hatcher, Algebraic Topology, pp.234–237; geometric chart constructions use
Mathlib open partial homeomorphisms and Euclidean balls.
-/

noncomputable section

namespace HolomorphicAnosov

universe u

open Set CategoryTheory HatcherCompactSupport

/-- The canonical nonzero local classes are realized on open coordinate balls by restricting
compact convex chart-support classes (Hatcher pp.234–235). 

Source: Hatcher, Algebraic Topology, pp.234–235, local consistency and the canonical mod-two orientation; p.237, Lemma 3.27 step (3).

Proof: Fix x and choose a full-target chart c through it. Take the nonempty compact convex support A given by the closed unit chart ball, which contains the open coordinate unit ball W.
The convex-support theorem supplies a class a supported on A whose restriction at every point of A is nonzero. Restrict a to W by the canonical support restriction.
For y in W, functoriality of the relative singular homology maps identifies the point restriction of the W-class with the point restriction of a directly from A. The former composition and direct map are induced by the identical inclusion of complement pairs.
This value is nonzero, and the chosen canonical class at y is also nonzero. Uniqueness of the nonzero local class equates the two. The chart and radius one have the required source/target guards, proving local compatibility. Empty M is vacuous and n=0 is included.
-/
theorem canonicalNonzeroLocalFamily_locallyCompatible {n : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    LocallyCompatible n (canonicalNonzeroLocalFamily (n := n) (M := M)) := by
  intro x
  obtain ⟨c, hx, hc⟩ := fullTargetChart (n := n) x
  let e : c.source ≃ₜ EuclideanSpace ℝ (Fin n) :=
    c.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr hc).trans (Homeomorph.Set.univ _))
  obtain ⟨A, hA, hAc, hAs, hAv, hWA⟩ := compactChartSupport c hc x hx
  have hlocal := Topology.Homology.hatcher_convex_support_mod2_local_homology n M
    c.source c.open_source e A hA hAc hAs hAv
  obtain ⟨a, ha, _⟩ := hlocal.2.2
  refine ⟨c, 1, hx, zero_lt_one, ?_, supportRestriction hWA n a, ?_⟩
  · rw [hc]; exact subset_univ _
  · intro y
    have hcomp :
        supportToPoint (chartBall c (c x) 1) n y (supportRestriction hWA n a) =
          supportToPoint A n ⟨y.val, hWA y.property⟩ a := by
      change ((Topology.Homology.modTwoSupportRestriction M A _ hWA n) ≫
        (Topology.Homology.modTwoSupportRestriction M _ {y.val}
          (singleton_subset_iff.mpr y.property) n)) a = _
      rw [← SSetPair.homologyMap_comp]
      rfl
    rw [hcomp]
    exact (uniqueNonzeroLocalClass (n := n) y.val).unique
      (ha.2 ⟨y.val, hWA y.property⟩) (canonicalNonzeroLocalFamily_ne_zero y.val)

end HolomorphicAnosov

