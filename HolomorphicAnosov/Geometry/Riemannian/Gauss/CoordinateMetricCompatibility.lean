import HolomorphicAnosov.Geometry.ConnectionCovariantConstantCoordinateGerms
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray
import HolomorphicAnosov.Geometry.Riemannian.Gauss.SmoothMetricPullbackEntry
import HolomorphicAnosov.Geometry.Riemannian.Gauss.ScalarCoordinateGermDerivative
import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateFrameInclusion
import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateFrameGerm
import HolomorphicAnosov.Geometry.Riemannian.Gauss.MetricCoordinatePairingGerm

/-! Metric compatibility is expressed in the inverse-chart frame. (Gallier–Quaintance, Props.
16.7–16.8, pp.451–454; Andrews, Lecture 8, Prop. 8.3.1, pp.74–75; Lecture 10, Prop. 10.3.1,
pp.95–98) -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- The directional derivative of the metric pairing in the inverse-chart frame equals the sum of
the two pairings with the Christoffel bilinear expression. (Gallier–Quaintance, Props.
16.7–16.8, pp.451–454; Andrews, Lecture 10, Prop. 10.3.1, pp.95–98) -/
theorem gauss_coordinate_metric_compatibility
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : ConnectionWhole M) (hp : p ∈ c.source) (u v w : E) :
    let ψ : E → M := fun z ↦ (c.symm z : M)
    let B := fun (z a d : E) ↦ g.inner (ψ z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z a) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z d)
    fderiv ℝ (fun z ↦ B z v w) (c p) u =
      B (c p) (connectionChristoffelBilinear (E := E) (riemannianConnection g) b c hc p.1 u v) w +
      B (c p) v (connectionChristoffelBilinear (E := E) (riemannianConnection g) b c hc p.1 u w) := by
  classical
  let ψ : E → M := fun z ↦ (c.symm z : M)
  let B := fun (z a d : E) ↦ g.inner (ψ z)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z a) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z d)
  let d := fun q : ConnectionWhole M ↦
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : ConnectionWhole M ↦ (r : M)) q
  obtain ⟨X, hX⟩ := exists_coordinate_frame_germ c hc p hp u
  obtain ⟨Y, hY⟩ := exists_coordinate_frame_germ c hc p hp v
  obtain ⟨Z, hZ⟩ := exists_coordinate_frame_germ c hc p hp w
  have hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ψ c.target :=
    contMDiff_subtype_val.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hc)
  have hB := gauss_smooth_metric_pullback_entry g c.open_target ψ hψ v w
  have hpair := gauss_metric_coordinate_pairing_germ g ⊤ c hc p hp Y Z v w hY hZ
  have hder : mvfderiv 𝓘(ℝ, E)
      (fun q : ConnectionWhole M ↦ g.inner q.1 (d q (Y q)) (d q (Z q))) p (X p) =
      fderiv ℝ (fun z ↦ B z v w) (c p) u := by
    rw [gauss_scalar_coordinate_germ_derivative c hc p hp _ _
      ((hB.contDiffAt (c.open_target.mem_nhds (c.map_source hp))).differentiableAt
        (by simp)) hpair, hX.self_of_nhds]
  have hcompat := (Classical.choose_spec
    (andrews_smooth_levi_civita_connection E M g)).2.1 ⊤ X Y Z p
  change mvfderiv 𝓘(ℝ, E)
    (fun q : ConnectionWhole M ↦ g.inner q.1 (d q (Y q)) (d q (Z q))) p (X p) =
      g.inner p.1 (d p ((riemannianConnection g).cov ⊤ X Y p)) (d p (Z p)) +
      g.inner p.1 (d p (Y p)) (d p ((riemannianConnection g).cov ⊤ X Z p)) at hcompat
  rw [hder, connection_covariant_constant_coordinate_germs (riemannianConnection g) b c hc p hp X Y u v hX.self_of_nhds hY, connection_covariant_constant_coordinate_germs (riemannianConnection g) b c hc p hp X Z u w hX.self_of_nhds hZ,
    gauss_coordinate_frame_inclusion ⊤ c hc p hp (Y p) v hY.self_of_nhds,
    gauss_coordinate_frame_inclusion ⊤ c hc p hp (Z p) w hZ.self_of_nhds] at hcompat
  change fderiv ℝ (fun z ↦ B z v w) (c p) u = _
  dsimp only [B, ψ]
  erw [c.left_inv hp]
  exact hcompat

end HolomorphicAnosov
