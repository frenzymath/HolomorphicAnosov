import HolomorphicAnosov.Geometry.Manifold.OrientedRealTopForm
import HolomorphicAnosov.Geometry.Manifold.SmoothPositiveRealVolumeForm
import Mathlib.Geometry.Manifold.Diffeomorph

/-! This file defines coordinate covariance of top-form densities and orientation preservation in a
positively oriented smooth atlas. (Demailly, I §1.B.5, (1.13), p. 10; §1.C, (1.16)–(1.17), p.
11) -/

open scoped Manifold ContDiff

namespace HolomorphicAnosov.VolumePrototype

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (CoordinateSpace n) M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- The top-form density in the first positive chart equals its density in the second chart times
the determinant of the transition `ψ ∘ φ⁻¹` on their overlap. (Demailly, I (1.13), p. 10; §1.C,
p. 11) -/
def DensityOverlapLaw
    (o : OrientedAtlas (n := n) (M := M)) (ν : PositiveVolumeForm o) : Prop :=
  ∀ φ ∈ o.charts, ∀ ψ ∈ o.charts, ∀ z ∈ φ.target, φ.symm z ∈ ψ.source →
    chartDensity ν.form φ z = chartDensity ν.form ψ (ψ (φ.symm z)) * transitionDet φ ψ z

/-- The coordinate representative `ψ ∘ F ∘ φ⁻¹` has strictly positive derivative determinant in
every pair of charts in the oriented atlas. (Demailly, I §1.C, (1.17), p. 11) -/
def PreservesOrientation (o : OrientedAtlas (n := n) (M := M))
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞) : Prop :=
  ∀ φ ∈ o.charts, ∀ ψ ∈ o.charts, ∀ z ∈ φ.target, F (φ.symm z) ∈ ψ.source →
    0 < LinearMap.det (fderiv ℝ (fun w ↦ ψ (F (φ.symm w))) z).toLinearMap

end HolomorphicAnosov.VolumePrototype
