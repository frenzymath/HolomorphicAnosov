import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.FibreHasMFDeriv

/-!
Reusable FibreMFDeriv declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07FibreInsertionDerivative

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The exact native manifold derivative of fixed-fibre insertion. Source: the preceding chart computation and uniqueness of the manifold derivative. -/
theorem mfderiv_fibreInsertion (p : M) :
    let ι : E → TangentBundle I M := fun v ↦ ⟨p, (tangentSpaceCastModel I p).symm v⟩
    mfderiv 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E)) ι 0 =
      (tangentSpaceCastModel (I.prod 𝓘(ℝ, E)) (ι 0)).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inr ℝ E E).comp
          (tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).toContinuousLinearMap) :=
  (hasMFDerivAt_fibreInsertion (I := I) p).mfderiv

end
end HolomorphicAnosov.W07FibreInsertionDerivative
