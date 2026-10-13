import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray

/-! The velocity of the image of an affine curve is given by the manifold differential. -/

open scoped Manifold

namespace HolomorphicAnosov

/-- The velocity of `t ↦ f (v + t • w)` equals the manifold differential of `f` applied to `w`.
(Andrews, §8.11, pp.83–86; Gallier–Quaintance, Prop. 16.8) -/
theorem gauss_affine_curve_velocity_public
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    {f : V → M} {v w y : V} {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) f y) (hy : v + t • w = y) :
    curveVelocity (fun s ↦ f (v + s • w)) t =
      mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f y
        ((NormedSpace.fromTangentSpace y).symm w) := by
  have hl : HasDerivAt (fun s : ℝ ↦ v + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add v
  have h := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, V))
    (I'' := 𝓘(ℝ, E)) (x := t) hf hl.hasFDerivAt.hasMFDerivAt.mdifferentiableAt hy
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1)
  rw [hl.hasFDerivAt.hasMFDerivAt.mfderiv] at h
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s ↦ f (v + s • w)) t
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1) =
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f y ((1 : ℝ) • w) at h
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s ↦ f (v + s • w)) t
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1) =
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f y w
  simpa only [one_smul] using h

end HolomorphicAnosov
