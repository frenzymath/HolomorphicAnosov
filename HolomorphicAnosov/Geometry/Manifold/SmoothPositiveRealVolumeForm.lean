import HolomorphicAnosov.Geometry.Manifold.OrientedRealTopForm

/-! # Smooth positive real volume forms on an oriented manifold Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, Chapter I §1.B.5 (1.13), printed p.10, and §1.C (1.16)–(1.17), printed p.11. The orientation, native tangent fibres, top-degree alternating form and smooth chart coefficients are the actual data of `OrientedRealTopForm`. This module adds only strict positivity in the supplied positively oriented atlas. -/

open scoped Manifold ContDiff

namespace HolomorphicAnosov.VolumePrototype

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (CoordinateSpace n) M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- A smooth positive real volume form for the given oriented compatible atlas (Demailly, I §1.B.5 and §1.C, pp.10–11). -/
structure PositiveVolumeForm (o : OrientedAtlas (n := n) (M := M)) where
  form : TopForm n M
  smooth : IsSmoothTopForm form
  positive : ∀ e ∈ o.charts, ∀ z ∈ e.target, 0 < chartDensity form e z

end HolomorphicAnosov.VolumePrototype
