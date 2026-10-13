import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! This file defines Hermitian metrics on native complex tangent fibres. (Demailly, VI §4.) -/



open scoped ContDiff

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- The inverse-chart differential sends the standard coordinate vector to the native tangent fibre. On a compatible chart's target this is its coordinate frame. (Demailly, VI §4.) -/
noncomputable def hermitianTangentChartFrame
    (e : OpenPartialHomeomorph X (ComplexModel d)) (z : ComplexModel d) (i : Fin d) :
    TangentSpace (complexModel d) (e.symm z) :=
  mfderiv (complexModel d) (complexModel d) e.symm z
    ((NormedSpace.fromTangentSpace z).symm (Pi.single i 1))

/-- Positive definite complex Hermitian forms on the native tangent fibres. (Demailly, VI §4.) -/
abbrev HermitianTangentMetricCore (d : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] :=
  ∀ x : X, InnerProductSpace.Core ℂ (TangentSpace (complexModel d) x)

/-- The first-linear Hermitian pairing, with Demailly's convention. (Demailly, VI §4.) -/
def hermitianTangentPairing (h : HermitianTangentMetricCore d X) (x : X)
    (v w : TangentSpace (complexModel d) x) : ℂ :=
  (h x).inner w v

/-- The metric's actual complex coordinate coefficients in the inverse-chart frame. (Demailly, VI §4.) -/
noncomputable def hermitianTangentChartCoefficient (h : HermitianTangentMetricCore d X)
    (e : OpenPartialHomeomorph X (ComplexModel d)) (i j : Fin d) (z : ComplexModel d) : ℂ :=
  hermitianTangentPairing h (e.symm z)
    (hermitianTangentChartFrame e z i) (hermitianTangentChartFrame e z j)

/-- Real smoothness of all coefficients in every compatible holomorphic chart. (Demailly, VI §4.) -/
def IsSmoothHermitianTangentMetric [IsManifold (complexModel d) ∞ X]
    (h : HermitianTangentMetricCore d X) : Prop :=
  ∀ e : OpenPartialHomeomorph X (ComplexModel d),
    e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
    ∀ i j : Fin d, ContDiffOn ℝ ∞ (hermitianTangentChartCoefficient h e i j) e.target

/-- The real metric pairing on the original real tangent fibre, through the canonical real identification. (Demailly, VI §4.) -/
noncomputable def hermitianTangentRealPairing (h : HermitianTangentMetricCore d X) (x : X)
    (v w : TangentSpace (realModel d) x) : ℝ :=
  (hermitianTangentPairing h x
    ((complexTangentToReal d x).symm v) ((complexTangentToReal d x).symm w)).re

end HolomorphicAnosov
