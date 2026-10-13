import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant

/-!
Real top forms are alternating maps on tangent fibers with smooth chart coefficients.
Orientations are given by covering atlases with positive transition determinants. (Demailly, I
§1.B.5 and §1.C, pp. 10–11)
-/

open scoped Manifold ContDiff
open Set

noncomputable section
namespace HolomorphicAnosov.VolumePrototype

universe u
/-- The real Euclidean coordinate space of dimension `n`. (Demailly, I §1.C, p. 11) -/
abbrev CoordinateSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]

/-- A real top-degree form assigns a continuous alternating `n`-linear map to each tangent fiber.
(Demailly, I §1.B, p. 10) -/
abbrev TopForm (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (CoordinateSpace n) M] :=
  (x : M) → ContinuousAlternatingMap ℝ (TangentSpace 𝓘(ℝ, CoordinateSpace n) x) ℝ (Fin n)

/-- The coefficient of a top form in a chart, evaluated on the inverse-chart coordinate frame.
(Demailly, I (1.13), p. 10) -/
def chartDensity (ν : TopForm n M) (e : OpenPartialHomeomorph M (CoordinateSpace n))
    (z : CoordinateSpace n) : ℝ :=
  ν (e.symm z) (fun i ↦ mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e.symm z
    ((NormedSpace.fromTangentSpace z).symm (EuclideanSpace.basisFun (Fin n) ℝ i)))

/-- The derivative determinant of the chart transition `ψ ∘ φ⁻¹`. (Demailly, I §1.C, p. 11) -/
def transitionDet (φ ψ : OpenPartialHomeomorph M (CoordinateSpace n))
    (z : CoordinateSpace n) : ℝ :=
  LinearMap.det (fderiv ℝ (fun w ↦ ψ (φ.symm w)) z).toLinearMap

/-- An orientation given by a covering compatible atlas with positive transition determinants.
(Demailly, I §1.C, p. 11) -/
structure OrientedAtlas [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] where
  charts : Set (OpenPartialHomeomorph M (CoordinateSpace n))
  compatible : ∀ e ∈ charts, e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M
  covers : ∀ x : M, ∃ e ∈ charts, x ∈ e.source
  positive_transition : ∀ φ ∈ charts, ∀ ψ ∈ charts, ∀ z ∈ φ.target,
    φ.symm z ∈ ψ.source → 0 < transitionDet φ ψ z

/-- A top form is smooth if its coefficient is smooth in every compatible chart. (Demailly, I §1.B,
p. 10) -/
def IsSmoothTopForm [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] (ν : TopForm n M) : Prop :=
  ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M,
    ContDiffOn ℝ ∞ (chartDensity ν e) e.target

/-- A smooth real top form together with an oriented compatible atlas. (Demailly, I §1.B.5 and §1.C,
pp. 10–11) -/
structure OrientedRealTopForm [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] where
  orientation : OrientedAtlas (n := n) (M := M)
  form : TopForm n M
  smooth : IsSmoothTopForm form

end HolomorphicAnosov.VolumePrototype
