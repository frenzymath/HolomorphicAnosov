import HolomorphicAnosov.Topology.Homology.FullTargetChart
import HolomorphicAnosov.Topology.Homology.ConvexSupportModTwoLocalHomology
import HolomorphicAnosov.Topology.Homology.ModTwoLocalHomologyCompatibleFamily

/-!
# UniqueNonzeroLocalClass

DAG node: `topo.mod2_unique_nonzero_local_class`.
Source: Hatcher, Algebraic Topology, pp.234–237; geometric chart constructions use
Mathlib open partial homeomorphisms and Euclidean balls.
-/

noncomputable section

namespace HolomorphicAnosov

universe u

open Set CategoryTheory HatcherCompactSupport

/-- The supplied convex-support calculation produces a unique nonzero local class.
This deduction uses a singleton support inside a chart with full Euclidean target. 

Source: Hatcher, Algebraic Topology, pp.233–235, local homology and canonical mod-two orientation; convex-support calculation in Lemma 3.27 step (3), p.237.

Proof: Choose a chart containing x with full Euclidean target and regard it as a homeomorphism from its source subtype to Euclidean space.
The image of the singleton support in this homeomorphism is the singleton containing the image of x; singleton sets are compact, nonempty and convex, and the support is contained in the chart source.
Apply the convex-support local homology calculation to this singleton. Its local-top-group clause gives exactly one nonzero element in the singleton support group. The source local calculation includes n=0, so no positivity restriction appears.
-/
theorem uniqueNonzeroLocalClass {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    ∃! a : HatcherCompactSupport.SupportHomology ({x} : Set M) n, a ≠ 0 := by
  obtain ⟨c, hx, hc⟩ := fullTargetChart (n := n) x
  let e : c.source ≃ₜ EuclideanSpace ℝ (Fin n) :=
    c.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr hc).trans (Homeomorph.Set.univ _))
  have hconv : Convex ℝ (e '' {z : c.source | z.val ∈ ({x} : Set M)}) := by
    have heq : e '' {z : c.source | z.val ∈ ({x} : Set M)} = {e ⟨x, hx⟩} := by
      ext v
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzx : z = ⟨x, hx⟩ := Subtype.ext (Set.mem_singleton_iff.mp hz)
        simp [hzx]
      · intro hv
        exact ⟨⟨x, hx⟩, Set.mem_singleton x, Set.mem_singleton_iff.mp hv |>.symm⟩
    rw [heq]
    exact convex_singleton _
  have hlocal := Topology.Homology.hatcher_convex_support_mod2_local_homology n M
    c.source c.open_source e {x} (Set.singleton_nonempty x) (isCompact_singleton)
    (Set.singleton_subset_iff.mpr hx) hconv
  exact (hlocal.2.1 ⟨x, Set.mem_singleton x⟩).2.2

end HolomorphicAnosov

