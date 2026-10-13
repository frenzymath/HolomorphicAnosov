import HolomorphicAnosov.Geometry.ConnectionChristoffelRepresentation
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray
import HolomorphicAnosov.Geometry.Riemannian.Gauss.ChristoffelFrameGerm
import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateFrameGerm

/-! The Christoffel coefficients of the Levi-Civita connection satisfy the inverse-metric formula.
(Gallier–Quaintance, Props. 16.7–16.8, pp.451–454; Andrews, Lecture 8, Prop. 8.3.1, pp.74–75;
Lecture 10, Prop. 10.3.1, pp.95–98) -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- On the chart source, the Christoffel coefficients of the Riemannian connection satisfy the
Levi-Civita formula in terms of the inverse metric and derivatives of metric entries. (Andrews,
Lecture 10, Prop. 10.3.1, p.98; Gallier–Quaintance, Prop. 16.7) -/
theorem gauss_connectionChristoffel_metric_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : ConnectionWhole M) (hp : p ∈ c.source) (i j k : Fin n) :
    let ψ : E → M := fun z ↦ (c.symm z : M)
    let G : E → Matrix (Fin n) (Fin n) ℝ := fun z r s ↦ g.inner (ψ z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b r))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z (b s))
    connectionChristoffel (riemannianConnection g) b c hc i j k p =
      (1 / 2 : ℝ) * ∑ l, ((G (c p))⁻¹) k l *
        (fderiv ℝ (fun z ↦ G z j l) (c p) (b i) +
          fderiv ℝ (fun z ↦ G z i l) (c p) (b j) -
          fderiv ℝ (fun z ↦ G z i j) (c p) (b l)) := by
  obtain ⟨Γ, _, _, hformula, hΓ⟩ :=
    (Classical.choose_spec (andrews_smooth_levi_civita_connection E M g)).2.2.2.2
      ⊤ n b c hc
  have hchosen := connectionChristoffel_representation (riemannianConnection g) b c hc
  obtain ⟨X, hX⟩ := exists_coordinate_frame_germ c hc p hp (b i)
  obtain ⟨Y, hY⟩ := exists_coordinate_frame_germ c hc p hp (b j)
  have h1 := gauss_christoffel_frame_germ (riemannianConnection g) ⊤ b c
    (connectionChristoffel (riemannianConnection g) b c hc) hchosen p hp i j k X Y hX hY
  have h2 := gauss_christoffel_frame_germ (riemannianConnection g) ⊤ b c
    Γ hΓ p hp i j k X Y hX hY
  rw [← h1, h2]
  exact hformula p hp i j k

end HolomorphicAnosov

