import HolomorphicAnosov.Geometry.ConnectionChristoffelRepresentation
import HolomorphicAnosov.Geometry.SmoothAffineConnection.Basic
import HolomorphicAnosov.Geometry.SmoothAffineConnection
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic
import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateFrameInclusion

/-!
Covariant derivatives of fields with constant coordinate germs are given by the Christoffel
bilinear expression. (Andrews, Prop. 8.3.1, p.74)
-/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- If the second field has constant chart coordinates near a point, its covariant derivative is the
inverse-chart derivative applied to the Christoffel bilinear expression. (Andrews, Prop. 8.3.1,
p.74) -/
theorem connection_covariant_constant_coordinate_germs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (nabla : SmoothAffineConnection E M) {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : ConnectionWhole M) (hp : p ∈ c.source)
    (X Y : LocalSmoothVectorField E M ⊤) (u a : E)
    (hX : mvfderiv 𝓘(ℝ, E) c p (X p) = u)
    (hY : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (Y q) = a) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : ConnectionWhole M ↦ (r : M)) p
        (nabla.cov ⊤ X Y p) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ (c.symm z : M)) (c p)
        (connectionChristoffelBilinear (E := E) nabla b c hc p.1 u a) := by
  classical
  have hchosen := connectionChristoffel_representation nabla b c hc
  apply gauss_coordinate_frame_inclusion ⊤ c hc p hp
  apply b.repr.injective
  ext k
  have hYc : Y.coordinateCoefficient b c k =ᶠ[𝓝 (c p)] fun _ ↦ b.repr a k := by
    have hy := (c.continuousAt_symm (c.map_source hp)).eventually
      (by simpa only [c.left_inv hp] using hY)
    filter_upwards [hy] with z hz
    exact congrArg (fun v ↦ b.repr v k) hz
  change (nabla.cov ⊤ X Y).tangentCoefficient b c p k = _
  rw [hchosen X Y p hp k, hYc.fderiv_eq, fderiv_const_apply]
  simp only [LocalSmoothVectorField.tangentCoefficient, hX, hY.self_of_nhds,
    zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
  change _ = b.repr (connectionChristoffelBilinear (E := E)
    nabla b c hc p.1 u a) k
  have hrepr := congrArg (fun z : E ↦ b.repr z k)
    (b.sum_repr (connectionChristoffelBilinear (E := E)
      nabla b c hc p.1 u a))
  convert hrepr.symm using 1 <;> simp [connectionChristoffelBilinear, Finset.sum_apply, map_sum,
    map_smul, Finsupp.single_apply]

end HolomorphicAnosov
