import HolomorphicAnosov.Geometry.SmoothLeviCivitaConnection

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix
namespace HolomorphicAnosov

/-- A tangent vector with chart coordinates `a` equals the inverse-chart differential applied to
`a`, after inclusion. (Gallier–Quaintance, Props. 16.7–16.8) -/
private lemma coordinate_frame_inclusion_public
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
  have hd := congrArg (fun d ↦ d v) (hcD.symm_comp_deriv hp)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c p)
    (mvfderiv 𝓘(ℝ, E) c p v) = v at hd
  rw [hv] at hd
  change @Eq E _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val ∘ c.symm) (c p) a)
  erw [mfderiv_comp (c p)
    ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞)
      (c.symm (c p))).mdifferentiableAt (by simp))
    (hcD.symm.mdifferentiableAt (c.map_source hp)), ContinuousLinearMap.comp_apply,
    hd, c.left_inv hp]

/-- The metric pairing of two vector fields with constant chart-coordinate germs agrees locally with
the corresponding inverse-chart metric entry. (Gallier–Quaintance, Props. 16.7–16.8, pp.451–454;
Andrews, Prop. 8.3.1, pp.74–75; Prop. 10.3.1, pp.95–98) -/
theorem gauss_metric_coordinate_pairing_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (U : Opens M) (c : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U) (p : U) (hp : p ∈ c.source)
    (X Y : LocalSmoothVectorField E M U) (v w : E)
    (hX : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (X q) = v)
    (hY : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (Y q) = w) :
    (fun q : U ↦ g.inner q.1
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (X q))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q (Y q))) =ᶠ[𝓝 p]
    (fun q : U ↦ g.inner (c.symm (c q)).1
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (c.symm z : M)) (c q) v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (c.symm z : M)) (c q) w)) := by
  filter_upwards [hX, hY, c.open_source.mem_nhds hp] with q hx hy hq
  have hx' := coordinate_frame_inclusion_public U c hc q hq (X q) v hx
  have hy' := coordinate_frame_inclusion_public U c hc q hq (Y q) w hy
  erw [← hx', ← hy', c.left_inv hq]

end HolomorphicAnosov
