import HolomorphicAnosov.Geometry.SmoothAffineConnection.Basic
import HolomorphicAnosov.Geometry.SmoothAffineConnection

/-! Christoffel coefficients are recovered by evaluating covariant derivatives on coordinate
basis-vector germs. (Gallier–Quaintance, Props. 16.7–16.8, pp.451–454; Andrews, Lecture 8, Prop.
8.3.1, pp.74–75; Lecture 10, Prop. 10.3.1, pp.95–98) -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- For vector fields with coordinate basis-vector germs, the corresponding coordinate of their
covariant derivative equals the Christoffel coefficient in a connection reconstruction formula.
(Gallier–Quaintance, Props. 16.7–16.8, pp.451–454; Andrews, Lecture 8, Prop. 8.3.1, pp.74–75;
Lecture 10, Prop. 10.3.1, pp.95–98) -/
lemma gauss_christoffel_frame_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (nabla : SmoothAffineConnection E M) (U : Opens M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (Γ : Fin n → Fin n → Fin n → U → ℝ)
    (hΓ : ∀ (X Y : LocalSmoothVectorField E M U) (p : U), p ∈ c.source → ∀ k,
      (nabla.cov U X Y).tangentCoefficient b c p k =
        (∑ i, X.tangentCoefficient b c p i *
          fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i)) +
        ∑ i, ∑ j, X.tangentCoefficient b c p i * Y.tangentCoefficient b c p j * Γ i j k p)
    (p : U) (hp : p ∈ c.source) (i j k : Fin n)
    (X Y : LocalSmoothVectorField E M U)
    (hX : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (X q) = b i)
    (hY : ∀ᶠ q in 𝓝 p, mvfderiv 𝓘(ℝ, E) c q (Y q) = b j) :
    (nabla.cov U X Y).tangentCoefficient b c p k = Γ i j k p := by
  exact christoffel_coefficient_of_coordinate_germs nabla.cov U b c Γ hΓ p hp i j k X Y hX hY

end HolomorphicAnosov
