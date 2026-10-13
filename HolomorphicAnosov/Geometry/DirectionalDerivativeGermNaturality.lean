import HolomorphicAnosov.Geometry.SmoothAffineConnection
import HolomorphicAnosov.Geometry.SmoothOpenInclusionDifferentialInjective

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- Directional differentiation commutes with smooth extension of scalar and vector-field germs
through an open inclusion. -/
theorem directional_derivative_germ_naturality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (U : Opens M) (p : U)
    (f : U → ℝ) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ F)
    (X : LocalSmoothVectorField E M U)
    (AX : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (hf : ∀ᶠ q in 𝓝 p, F q.1 = f q)
    (hX : ∀ᶠ q in 𝓝 p, AX q.1 =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (X q)) :
    mvfderiv 𝓘(ℝ, E) f p (X p) = mvfderiv 𝓘(ℝ, E) F p.1 (AX p.1) := by
  have hfg : (F ∘ Subtype.val) =ᶠ[𝓝 p] f := hf
  have hd := hfg.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ))
  have hv : mvfderiv 𝓘(ℝ, E) (F ∘ Subtype.val) p = mvfderiv 𝓘(ℝ, E) f p := by
    ext v
    have hh := congrArg (fun d ↦ d v) hd
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (F ∘ Subtype.val) p v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p v at hh
    exact hh
  rw [← hv]
  rw [mvfderiv_comp_apply p ((hF p.1).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞) p).mdifferentiableAt
      (by simp))]
  rw [← hX.self_of_nhds]


end
end HolomorphicAnosov
