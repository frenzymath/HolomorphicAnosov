import HolomorphicAnosov.Geometry.SmoothAffineConnection
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ExtendedCoefficients
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.WholeChartAtlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.WholeChart

/-!
Coordinate definitions for covariant differentiation along curves, geodesics, tangent lifts, and
geodesic sprays of smooth affine connections. (Andrews, pp.74–75, 83–85)
-/

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The whole manifold as an open subtype. (Andrews, Prop. 8.3.1, p.74) -/
abbrev ConnectionWhole (M : Type*) [TopologicalSpace M] := (⊤ : Opens M)

/-- The chart map on the original manifold, identified with the whole open subtype. (Andrews, Prop.
8.3.1, p.74) -/
def connectionChartMap (c : OpenPartialHomeomorph (ConnectionWhole M) E) (p : M) : E :=
  c ⟨p, mem_univ p⟩

/-- The inverse chart map with values in the original manifold. (Andrews, Prop. 8.3.1, p.74) -/
def connectionChartInverse (c : OpenPartialHomeomorph (ConnectionWhole M) E) (x : E) : M :=
  (c.symm x).1

/-- The Christoffel coefficients of the connection in a chosen basis and chart, extended by zero
outside the chart source. (Andrews, Prop. 8.3.1, p.74) -/
def connectionChristoffel (nabla : SmoothAffineConnection E M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M)) :
    Fin n → Fin n → Fin n → ConnectionWhole M → ℝ :=
  fun i j k p ↦ ConnectionChristoffelLocal.extendedLocalChristoffel nabla b
    (ConnectionChristoffelLocal.wholeChart c)
    (ConnectionChristoffelLocal.wholeChart_mem_maximalAtlas c hc) i j k p.1

/-- The bilinear Christoffel expression in the real model space. (Andrews, Prop. 8.3.1, p.74) -/
def connectionChristoffelBilinear (nabla : SmoothAffineConnection E M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : M) (u v : E) : E :=
  ∑ k, (∑ i, ∑ j,
    b.repr u i * b.repr v j * connectionChristoffel nabla b c hc i j k
      ⟨p, mem_univ p⟩) • b k

/-- The chart coordinates of a tangent field along a curve. (Andrews, Prop. 8.4.1, pp.74–75) -/
def alongCurveCoordinate (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (γ : ℝ → M) (Z : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (γ t)) (t : ℝ) : E :=
  tangentSpaceCastModel 𝓘(ℝ, E) (connectionChartMap c (γ t))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c) (γ t) (Z t))

/-- The coordinate covariant derivative `z′ + Γ(x′, z)` of a field along a curve. (Andrews, Prop.
8.4.1, pp.74–75) -/
def covariantDerivativeCoordinate (nabla : SmoothAffineConnection E M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (γ : ℝ → M) (Z : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (γ t)) (t : ℝ) : E :=
  deriv (alongCurveCoordinate c γ Z) t +
    connectionChristoffelBilinear nabla b c hc (γ t)
      (deriv (connectionChartMap c ∘ γ) t) (alongCurveCoordinate c γ Z t)

/-- The covariant derivative of a tangent field along a curve, computed in the canonical chart and
transported to the tangent fibre. (Andrews, Prop. 8.4.1, pp.74–75) -/
def covariantDerivativeAlongCurve (nabla : SmoothAffineConnection E M)
    (γ : ℝ → M) (Z : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (γ t)) (t : ℝ) :
    TangentSpace 𝓘(ℝ, E) (γ t) :=
  let c := chartAt E (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M)
  let hc := chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M)
  let a := covariantDerivativeCoordinate nabla (Module.finBasis ℝ E) c hc γ Z t
  let x := connectionChartMap c (γ t)
  let w := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartInverse c) x
    ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm a)
  (tangentSpaceCastModel 𝓘(ℝ, E) (γ t)).symm
    (tangentSpaceCastModel 𝓘(ℝ, E) (connectionChartInverse c x) w)

/-- The velocity of a parametrized curve as a vector in its tangent fibre. (Andrews, Def. 8.11.1,
p.83) -/
def curveVelocity (γ : ℝ → M) (t : ℝ) : TangentSpace 𝓘(ℝ, E) (γ t) :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1)

/-- The predicate that a curve is smooth on a domain and has vanishing covariant acceleration there.
(Andrews, Def. 8.11.1, p.83) -/
def IsConnectionGeodesicOn (nabla : SmoothAffineConnection E M) (γ : ℝ → M)
    (J : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ J ∧
    ∀ t ∈ J, covariantDerivativeAlongCurve nabla γ (curveVelocity γ) t = 0

/-- The tangent lift `t ↦ (γ(t), γ′(t))` of a curve. (Andrews, Prop. 8.11.2, p.84) -/
def curveTangentLift (γ : ℝ → M) (t : ℝ) : TangentBundle 𝓘(ℝ, E) M :=
  ⟨γ t, curveVelocity γ t⟩

/-- The induced tangent coordinates `(φ(p), dφ_p(v))`. (Andrews, Prop. 8.11.2 and Ex. 8.11.3, p.84) -/
def connectionTangentChart (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (z : TangentBundle 𝓘(ℝ, E) M) : E × E :=
  (connectionChartMap c z.proj,
    tangentSpaceCastModel 𝓘(ℝ, E) (connectionChartMap c z.proj)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c) z.proj z.snd))

/-- The predicate that a vector field has coordinate expression `(v, -Γ(v, v))` in every admissible
induced tangent chart. (Andrews, Prop. 8.11.2 and Ex. 8.11.3, p.84) -/
def HasConnectionSprayCoordinates (nabla : SmoothAffineConnection E M)
    (G : (z : TangentBundle 𝓘(ℝ, E) M) →
      TangentSpace (𝓘(ℝ, E)).tangent z) : Prop :=
  ∀ (n : ℕ) (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (z : TangentBundle 𝓘(ℝ, E) M),
    (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M) ∈ c.source →
      let v := (connectionTangentChart c z).2
      tangentSpaceCastModel 𝓘(ℝ, E × E) (connectionTangentChart c z)
        (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart c) z (G z)) =
          (v, -connectionChristoffelBilinear nabla b c hc z.proj v v)


end
end HolomorphicAnosov
