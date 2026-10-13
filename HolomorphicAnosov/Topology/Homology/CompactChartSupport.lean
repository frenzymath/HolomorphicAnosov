import HolomorphicAnosov.Topology.Homology.ModTwoLocalHomologyCompatibleFamily
import Mathlib.Analysis.Normed.Module.Convex

/-!
# CompactChartSupport

DAG node: `topo.compact_convex_chart_support`.
Source: Hatcher, Algebraic Topology, pp.234–237; geometric chart constructions use
Mathlib open partial homeomorphisms and Euclidean balls.
-/

noncomputable section

namespace HolomorphicAnosov

universe u

open Set CategoryTheory HatcherCompactSupport

/-- Closed balls in a full-target chart give compact supports with their literal convex images. 

Source: Hatcher, Algebraic Topology, p.237, Lemma 3.27 steps (2)–(3), compact convex chart supports; native compactness and convexity of closed Euclidean balls.

Proof: Let D be the closed unit ball centered at c(x), and A its image under the inverse chart. Full target places D in the inverse source. The inverse chart maps D into the original chart source, and c(x) in D gives x in A.
D is compact in finite-dimensional Euclidean space. The inverse chart is continuous on its target, hence on D, so its image A is compact.
The chart and inverse-chart identities identify the image of A in Euclidean space with D. This image is convex because closed balls in a real normed space are convex.
A point y in the open coordinate unit ball has c(y) in D; the identity c inverse of c(y) equals y then gives y in A. In dimension zero D is the singleton model space and the same proof applies.
-/
theorem compactChartSupport {n : ℕ} {M : Type u} [TopologicalSpace M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c.target = Set.univ) (x : M) (hx : x ∈ c.source) :
    let e : c.source ≃ₜ EuclideanSpace ℝ (Fin n) :=
      c.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr hc).trans (Homeomorph.Set.univ _))
    ∃ A : Set M, A.Nonempty ∧ IsCompact A ∧ A ⊆ c.source ∧
      Convex ℝ (e '' {z : c.source | z.val ∈ A}) ∧ chartBall c (c x) 1 ⊆ A := by
  intro e
  let D := Metric.closedBall (c x) 1
  let A := c.symm '' D
  have hD : D ⊆ c.target := by rw [hc]; exact subset_univ _
  have hAs : A ⊆ c.source := by
    rintro _ ⟨v, hv, rfl⟩
    exact c.map_target (hD hv)
  refine ⟨A, ?_, ?_, hAs, ?_, ?_⟩
  · refine ⟨x, c x, ?_, c.left_inv hx⟩
    exact Metric.mem_closedBall_self zero_le_one
  · exact (isCompact_closedBall (c x) 1).image_of_continuousOn
      (c.continuousOn_symm.mono hD)
  · have heq : e '' {z : c.source | z.val ∈ A} = D := by
      ext v
      constructor
      · rintro ⟨z, ⟨w, hw, hzw⟩, rfl⟩
        change c z.val ∈ D
        rw [← hzw, c.right_inv (hD hw)]
        exact hw
      · intro hv
        refine ⟨⟨c.symm v, c.map_target (hD hv)⟩, ⟨v, hv, rfl⟩, ?_⟩
        exact c.right_inv (hD hv)
    rw [heq]
    exact convex_closedBall _ _
  · intro y hy
    exact ⟨c y, Metric.ball_subset_closedBall hy.2, c.left_inv hy.1⟩

end HolomorphicAnosov

