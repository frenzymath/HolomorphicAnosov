import HolomorphicAnosov.Geometry.Manifold.SmoothPositiveRealVolumeForm
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # The real volume-form pullback and scalar Jacobian candidate Source: Jean-Pierre Demailly, *Complex Analytic and Differential Geometry*, June21,2012, Chapter I §1.B.5, printed p.10, equation (1.13), and §1.C, printed p.11, equations (1.16)–(1.17). The given volume form contains actual continuous alternating maps on the native real tangent fibres. Its pullback below uses the actual manifold differential. -/

open scoped Manifold ContDiff

noncomputable section

namespace HolomorphicAnosov.VolumePrototype

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (CoordinateSpace n) M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- Pullback of a native real tangent top form by the actual real manifold derivative (Demailly, I §1.B.5, p.10). -/
def pullback (ν : TopForm n M)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞) :
    TopForm n M :=
  fun x ↦ (ν (F x)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) F x)

/-- A positive chart containing the specified point, selected from the given orientation atlas (Demailly, I §1.C, p.11). -/
def chosenChart (o : OrientedAtlas (n := n) (M := M)) (x : M) :
    OpenPartialHomeomorph M (CoordinateSpace n) :=
  Classical.choose (o.covers x)

/-- The scalar coefficient ratio for the actual pullback of the given positive volume form (Demailly, I §1.B.5 and §1.C, pp.10–11). -/
def jacobian {o : OrientedAtlas (n := n) (M := M)} (ν : PositiveVolumeForm o)
    (F : Diffeomorph 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) M M ∞)
    (x : M) : ℝ :=
  chartDensity (pullback ν.form F) (chosenChart o x) (chosenChart o x x) /
    chartDensity ν.form (chosenChart o x) (chosenChart o x x)

end HolomorphicAnosov.VolumePrototype
