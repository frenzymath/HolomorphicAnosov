import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov

/-- The metric pairing of two tangent vectors equals the inverse-chart pullback metric evaluated on
their chart derivatives. (Gallier–Quaintance, Prop. 15.12, pp.437–438; Prop. 16.8, pp.452–454) -/
theorem gauss_native_coordinate_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : M) (hp : (⟨p, mem_univ p⟩ : ConnectionWhole M) ∈ c.source)
    (v w : TangentSpace 𝓘(ℝ, E) p) :
    let ψ : E → M := fun z ↦ (c.symm z : M)
    let x := connectionChartMap c p
    let d := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c) p
    g.inner (ψ x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ x (d v))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ x (d w)) = g.inner p v w := by
  let ψ : E → M := fun z ↦ (c.symm z : M)
  have hchart : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c) p := by
    apply ContMDiffAt.mdifferentiableAt (n := ∞) _ (by simp)
    apply (contMDiffAt_subtype_iff (U := ⊤) (x := ⟨p, mem_univ p⟩)).mp
    exact contMDiffAt_of_mem_maximalAtlas hc hp
  have hinv : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (connectionChartMap c p) := by
    apply ContMDiffAt.mdifferentiableAt (n := ∞) _ (by simp)
    exact (contMDiff_subtype_val.comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas hc)).contMDiffAt
        (c.open_target.mem_nhds (c.map_source hp))
  have he : ψ ∘ connectionChartMap c =ᶠ[𝓝 p] id := by
    have hcont : ContinuousAt (fun q : M ↦ (⟨q, mem_univ q⟩ : ConnectionWhole M)) p :=
      (continuous_id.subtype_mk fun q : M ↦ mem_univ q).continuousAt
    filter_upwards [hcont.eventually (c.open_source.mem_nhds hp)] with q hq
    exact congrArg Subtype.val (c.left_inv hq)
  have hd (a : TangentSpace 𝓘(ℝ, E) p) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (connectionChartMap c p)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c) p a) = a := by
    rw [← mfderiv_comp_apply (x := p) hinv hchart, he.mfderiv_eq, mfderiv_id]
    rfl
  dsimp only
  change g.inner (ψ (connectionChartMap c p)) _ _ = _
  rw [hd v, hd w]
  have hbase : ψ (connectionChartMap c p) = p := he.self_of_nhds
  erw [hbase]

end HolomorphicAnosov
