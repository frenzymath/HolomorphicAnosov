import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Tangent coordinates commute with open inclusion via the derivative of the inverse chart.
(Gallier–Quaintance, Props. 16.7–16.8, pp.451–454; Andrews, Lecture 8, Prop. 8.3.1, pp.74–75;
Lecture 10, Prop. 10.3.1, pp.96–98) -/

open IsManifold TopologicalSpace
open scoped Manifold ContDiff

namespace HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false in
/-- A tangent vector with chart coordinate `a` maps under open inclusion to the derivative of the
included inverse chart applied to `a`. (Andrews, Lecture 8, Prop. 8.3.1, pp.74–75; Lecture 10,
Prop. 10.3.1, pp.96–98; Gallier–Quaintance, Props. 16.7–16.8, pp.451–454) -/
lemma gauss_coordinate_frame_inclusion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (U : Opens M) (c : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U) (p : U) (hp : p ∈ c.source)
    (v : TangentSpace 𝓘(ℝ, E) p) (a : E)
    (hv : mvfderiv 𝓘(ℝ, E) c p v = a) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun q : U ↦ (q : M)) p v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (c.symm z : M)) (c p) a := by
  have hcD : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
  have hd := (hcD.mfderiv hp).symm_apply_apply v
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p)
    (mvfderiv 𝓘(ℝ, E) c p v) = v at hd
  rw [hv] at hd
  change @Eq E _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val ∘ c.symm) (c p) a)
  erw [mfderiv_comp (c p)
    ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞)
      (c.symm (c p))).mdifferentiableAt (by simp))
    (hcD.symm.mdifferentiableAt (c.map_source hp)), ContinuousLinearMap.comp_apply,
    hd, c.left_inv hp]

end HolomorphicAnosov

