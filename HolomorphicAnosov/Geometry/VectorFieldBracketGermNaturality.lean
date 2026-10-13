import HolomorphicAnosov.Geometry.SmoothAffineConnection
import HolomorphicAnosov.Geometry.SmoothOpenInclusionDifferentialInjective
import HolomorphicAnosov.Geometry.SmoothOpenInclusionDifferentialInvertible
import Mathlib.Geometry.Manifold.VectorField.LieBracket

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- The differential of an open inclusion carries the Lie bracket of local smooth vector fields to
the bracket of smooth ambient fields agreeing with their pushforwards near the point. -/
theorem bracket_germ_naturality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (U : Opens M) (p : U)
    (X Y : LocalSmoothVectorField E M U)
    (AX AY : ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (hX : ∀ᶠ q in nhds p, AX q.1 =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (X q))
    (hY : ∀ᶠ q in nhds p, AY q.1 =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (Y q)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) p
        (VectorField.mlieBracket 𝓘(ℝ, E) (fun q ↦ X q) (fun q ↦ Y q) p) =
      VectorField.mlieBracket 𝓘(ℝ, E) (fun q ↦ AX q) (fun q ↦ AY q) p.1 := by
  have : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by simp)
  let ι : U → M := Subtype.val
  have hinv (q : U) : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι q).IsInvertible :=
    smooth_open_inclusion_mfderiv_invertible U q
  have hPX : VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) ι (fun q ↦ AX q)
      =ᶠ[nhds p] (fun q ↦ X q) := by
    filter_upwards [hX] with q hq
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι q).inverse (AX q.1) = X q
    rw [hq, (hinv q).inverse_apply_self]
  have hPY : VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) ι (fun q ↦ AY q)
      =ᶠ[nhds p] (fun q ↦ Y q) := by
    filter_upwards [hY] with q hq
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι q).inverse (AY q.1) = Y q
    rw [hq, (hinv q).inverse_apply_self]
  have hn := VectorField.mpullback_mlieBracket (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (f := ι) (x₀ := p) ((AX.contMDiff p.1).mdifferentiableAt (by simp))
    ((AY.contMDiff p.1).mdifferentiableAt (by simp))
    (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞) p) (by simp)
  rw [hPX.mlieBracket_vectorField_eq hPY] at hn
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι p).inverse
    (VectorField.mlieBracket 𝓘(ℝ, E) (fun q ↦ AX q) (fun q ↦ AY q) p.1) = _ at hn
  rw [← hn, (hinv p).self_apply_inverse]


end
end HolomorphicAnosov
