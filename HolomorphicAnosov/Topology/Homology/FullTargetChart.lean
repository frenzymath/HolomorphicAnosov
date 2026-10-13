import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
Charts can be shrunk and reparametrized to have full Euclidean target. (Hatcher, pp. 234–237)
-/

noncomputable section

namespace HolomorphicAnosov

universe u

open Set

/-- An ordinary Euclidean chart can be shrunk and reparametrized to have full target. (Hatcher, pp. 234–237) -/
theorem fullTargetChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x ∈ c.source ∧ c.target = Set.univ := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 c.open_target (c x) (mem_chart_target _ x)
  let b := OpenPartialHomeomorph.univBall (E := EuclideanSpace ℝ (Fin n)) (c x) r
  refine ⟨c.trans b.symm, ?_, ?_⟩
  · change x ∈ c.source ∩ c ⁻¹' b.target
    refine ⟨mem_chart_source _ x, ?_⟩
    simpa [b, OpenPartialHomeomorph.univBall_target _ hr] using (Metric.mem_ball_self hr : c x ∈ Metric.ball (c x) r)
  · rw [OpenPartialHomeomorph.trans_target]
    apply Set.eq_univ_of_forall
    intro v
    refine ⟨?_, ?_⟩
    · simp [b]
    · have hv : v ∈ b.source := by simp [b]
      exact hsub (by simpa [b, OpenPartialHomeomorph.univBall_target _ hr] using b.map_source hv)

end HolomorphicAnosov

