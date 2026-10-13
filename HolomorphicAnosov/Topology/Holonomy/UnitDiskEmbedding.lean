import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

noncomputable section
open scoped ContDiff Manifold Topology
open Set Filter _root_.Topology

namespace HolomorphicAnosov

/-- Shrink a source native coordinate domain around a prescribed point and rescale to the
fixed unit disk. HPS p.115 product-chart restriction, implemented by Mathlib
`Metric.isOpen_iff`, `OpenPartialHomeomorph.unitBallBall`, and the subtype open-embedding API.
The rescaled map is an actual open embedding into the GIVEN source coordinate domain and its
image contains the prescribed coordinate center. This works in rank zero as well.
-/
theorem unit_disk_embedding_in_domain {r : ℕ}
    (D : TopologicalSpace.Opens (Fin r → ℝ)) (x : D) :
    ∃ j : FoliationCoordinateDisk r → D, IsOpenEmbedding j ∧ x ∈ Set.range j := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp D.isOpen x x.property
  let a := OpenPartialHomeomorph.unitBallBall (E := Fin r → ℝ) x.val ε hε
  let b : FoliationCoordinateDisk r ≃ₜ ↥(Metric.ball x.val ε) := a.toHomeomorphSourceTarget
  let j : FoliationCoordinateDisk r → D := fun z ↦ ⟨(b z).val, hsub (b z).property⟩
  have hj : IsOpenEmbedding j := by
    apply D.isOpen.isOpenEmbedding_subtypeVal.of_comp j
    exact Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp b.isOpenEmbedding
  refine ⟨j, hj, ?_⟩
  obtain ⟨z, hz⟩ := b.surjective ⟨x.val, Metric.mem_ball_self hε⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact congrArg (fun q : ↥(Metric.ball x.val ε) ↦ q.val) hz



end HolomorphicAnosov
