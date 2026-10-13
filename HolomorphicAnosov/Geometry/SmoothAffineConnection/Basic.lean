import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Smooth affine connections on the real tangent bundle


-/ 

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Smooth local sections of the genuine tangent bundle over an open set. Source: Andrews, Lecture 8, Definition 8.2.1, p.72, in its local-field formulation. -/
abbrev LocalSmoothVectorField (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (U : Opens M) :=
  ContMDiffSection 𝓘(ℝ, E) E ∞ (TangentSpace 𝓘(ℝ, E) : U → Type _)

variable {E M}

/-- Multiply a local smooth vector field by a smooth real function. Source: Andrews, Lecture 8, Definition 8.2.1(3), p.72. -/
def LocalSmoothVectorField.mulFunction {U : Opens M} (X : LocalSmoothVectorField E M U)
    (f : U → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) :
    LocalSmoothVectorField E M U :=
  ⟨fun p ↦ f p • X p, hf.smul_section X.contMDiff⟩

/-- A section over `V` restricts a section over `U` if inclusion pushes it to that section. Source: the local-field restriction formulation of Andrews, Lecture 8, Definition 8.2.1, p.72. -/
def LocalSmoothVectorField.IsRestriction {U V : Opens M} (hVU : V ≤ U)
    (XU : LocalSmoothVectorField E M U) (XV : LocalSmoothVectorField E M V) : Prop :=
  ∀ p : V, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Opens.inclusion hVU) p (XV p) =
    XU (Opens.inclusion hVU p)

variable (E M)

/-- The genuine real-bilinear local operator data of an affine connection. Source: Andrews, Lecture 8, Definition 8.2.1(1–2), p.72, on all open subsets. -/
abbrev LocalBilinearCovariantDerivative :=
  ∀ U : Opens M, LocalSmoothVectorField E M U →ₗ[ℝ]
    LocalSmoothVectorField E M U →ₗ[ℝ] LocalSmoothVectorField E M U

variable {E M}

/-- Compatibility of local covariant derivative data with genuine open restriction. Source: the local-field formulation of Andrews, Lecture 8, Definition 8.2.1, p.72. -/
def LocalBilinearCovariantDerivative.RespectsRestriction
    (cov : LocalBilinearCovariantDerivative E M) : Prop :=
  ∀ {U V : Opens M} (hVU : V ≤ U)
    (XU YU : LocalSmoothVectorField E M U) (XV YV : LocalSmoothVectorField E M V),
    LocalSmoothVectorField.IsRestriction hVU XU XV →
    LocalSmoothVectorField.IsRestriction hVU YU YV →
    LocalSmoothVectorField.IsRestriction hVU (cov U XU YU) (cov V XV YV)

/-- The restriction, tensoriality and derivative Leibniz laws for supplied local operator data. Source: Andrews, Lecture 8, Definition 8.2.1, p.72, expressed on all open subsets. -/
structure IsSmoothAffineConnectionOperator (cov : LocalBilinearCovariantDerivative E M) : Prop where
  /-- Covariant differentiation commutes with restriction to an open subset. -/
  restriction : cov.RespectsRestriction
  /-- The first argument is linear over smooth functions. -/
  function_linear {U : Opens M} (X Y : LocalSmoothVectorField E M U)
    (f : U → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) :
    cov U (X.mulFunction f hf) Y = (cov U X Y).mulFunction f hf
  /-- `∇_X(fY) = f∇_X Y + df(X)Y`, pointwise on the common domain. -/
  leibniz {U : Opens M} (X Y : LocalSmoothVectorField E M U)
    (f : U → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (p : U) :
    cov U X (Y.mulFunction f hf) p = f p • cov U X Y p +
      (mvfderiv 𝓘(ℝ, E) f p (X p)) • Y p

variable (E M)

/-- A smooth affine connection consists of genuine local operator data and the affine connection laws. Source: Andrews, Lecture 8, Definition 8.2.1, p.72. -/
structure SmoothAffineConnection where
  /-- The real-bilinear smooth local covariant derivative. -/
  cov : LocalBilinearCovariantDerivative E M
  /-- Restriction compatibility, smooth-function tensoriality and the genuine Leibniz rule. -/
  laws : IsSmoothAffineConnectionOperator cov

variable {E M}

/-- The coefficient of a local tangent field in a chart and a basis of its real coordinate model. Source: Andrews, Lecture 8, §8.3, p.74. -/
def LocalSmoothVectorField.tangentCoefficient {U : Opens M} {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (Y : LocalSmoothVectorField E M U) (p : U) (k : Fin n) : ℝ :=
  b.repr (mvfderiv 𝓘(ℝ, E) c p (Y p)) k

/-- The coordinate coefficient of a local field, as a function on the chart target. Source: Andrews, Lecture 8, §8.3, p.74. -/
def LocalSmoothVectorField.coordinateCoefficient {U : Opens M} {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (Y : LocalSmoothVectorField E M U) (k : Fin n) (z : E) : ℝ :=
  Y.tangentCoefficient b c (c.symm z) k

/-- Smooth Christoffel coordinate representation of supplied local operator data. Source: Andrews, Lecture 8, §8.3 and Proposition 8.3.1, p.74. -/
def LocalBilinearCovariantDerivative.HasSmoothChristoffelSymbols
    (cov : LocalBilinearCovariantDerivative E M) : Prop :=
  ∀ (U : Opens M) (n : ℕ) (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph U E), c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U →
    ∃ Γ : Fin n → Fin n → Fin n → U → ℝ,
      (∀ i j k, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (Γ i j k) c.source) ∧
      ∀ (X Y : LocalSmoothVectorField E M U) (p : U), p ∈ c.source →
        ∀ k : Fin n,
          (cov U X Y).tangentCoefficient b c p k =
            (∑ i, X.tangentCoefficient b c p i *
              fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i)) +
            ∑ i, ∑ j, X.tangentCoefficient b c p i *
              Y.tangentCoefficient b c p j * Γ i j k p


/-- Torsion vanishes exactly when the antisymmetric covariant derivative is the intrinsic commutator of tangent derivations. Source: Andrews, Lecture 10, Proposition 10.3.1, p.97. -/
def SmoothAffineConnection.IsTorsionFree (nabla : SmoothAffineConnection E M) : Prop :=
  ∀ (U : Opens M) (X Y : LocalSmoothVectorField E M U) (p : U),
    nabla.cov U X Y p - nabla.cov U Y X p =
      VectorField.mlieBracket 𝓘(ℝ, E) (fun q ↦ X q) (fun q ↦ Y q) p

/-- Compatibility with a supplied genuine smooth Riemannian metric on `TM`. Source: Andrews, Lecture 10, §10.1, p.95. -/
def SmoothAffineConnection.IsMetricCompatible (nabla : SmoothAffineConnection E M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    Prop :=
  ∀ (U : Opens M) (X Y Z : LocalSmoothVectorField E M U) (p : U),
    let ι := fun q : U ↦ (q : M)
    let dι := fun q : U ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ι q
    mvfderiv 𝓘(ℝ, E) (fun q : U ↦ g.inner q.1 (dι q (Y q)) (dι q (Z q)))
        p (X p) =
      g.inner p.1 (dι p (nabla.cov U X Y p)) (dι p (Z p)) +
        g.inner p.1 (dι p (Y p)) (dι p (nabla.cov U X Z p))

end

end HolomorphicAnosov
