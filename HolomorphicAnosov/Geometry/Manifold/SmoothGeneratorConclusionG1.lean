import HolomorphicAnosov.Geometry.Manifold.TangentFieldFromLocalGeneratorsG1

/-! # Packaging the smooth generator conclusion The final Bochner--Montgomery statement consists of a smooth tangent section and the pointwise manifold derivative certificate for every action orbit. This file packages those two outputs once their local construction has been assembled. -/

open scoped Manifold ContDiff Topology _root_.Topology

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- The conclusion of the one-parameter smooth-generator theorem consists of a smooth tangent field and pointwise action-orbit derivative witnesses. -/
theorem smooth_generator_conclusion_g1
    (a : ℝ → M → M)
    (X : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hX : CMDiff ∞ (T% X))
    (hderiv : ∀ x, ∃ L : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ]
        TangentSpace 𝓘(ℝ, E) (a 0 x),
      HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t x) 0 L ∧
        X x = tangentSpaceCast (𝓘(ℝ, E)) (a 0 x) x
          (L ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1)) ) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      CMDiff ∞ (T% X) ∧
        ∀ x, ∃ L : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ] TangentSpace 𝓘(ℝ, E) (a 0 x),
          HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t x) 0 L ∧
            X x = tangentSpaceCast (𝓘(ℝ, E)) (a 0 x) x
              (L ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1)) := by
  exact ⟨X, hX, hderiv⟩

end HolomorphicAnosov

