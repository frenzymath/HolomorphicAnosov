import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
Reusable FibreChart declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07FibreInsertionDerivative

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem fibre_chart (p : M) (v : E) :
    extChartAt (I.prod 𝓘(ℝ, E))
      (⟨p, 0⟩ : TangentBundle I M)
      (⟨p, (tangentSpaceCastModel I p).symm v⟩ : TangentBundle I M) =
        (extChartAt I p p, v) := by
  change (extChartAt I p p, tangentCoordChange I p p p v) = (extChartAt I p p, v)
  rw [tangentCoordChange_self (I := I) (mem_extChartAt_source p)]

end
end HolomorphicAnosov.W07FibreInsertionDerivative
