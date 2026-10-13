import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- For a map differentiable in both the complex and real manifold structures, its real derivative
is the scalar restriction of its complex derivative. -/
theorem derivative_scalar_restriction {d e : ℕ} {X : Type*} {Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y]
    [IsManifold (complexModel e) ∞ Y]
    (f : X → Y) (x : X)
    (hc : MDifferentiableAt (complexModel d) (complexModel e) f x)
    (hr : MDifferentiableAt (realModel d) (realModel e) f x) :
    mfderiv (realModel d) (realModel e) f x =
      (mfderiv (complexModel d) (complexModel e) f x).restrictScalars ℝ := by
  ext v
  apply (tangentSpaceCastModel (realModel e) (f x)).injective
  change (tangentSpaceCastModel (realModel e) (f x))
    ((mfderiv (realModel d) (realModel e) f x) v) =
    (tangentSpaceCastModel (realModel e) (f x))
      ((mfderiv (complexModel d) (complexModel e) f x) v)
  rw [hc.mfderiv_abuse, hr.mfderiv_abuse]
  have hd := hc.differentiableWithinAt_writtenInExtChartAt
  change (fderivWithin ℝ (writtenInExtChartAt (complexModel d) (complexModel e) x f)
    (Set.range (complexModel d)) ((extChartAt (complexModel d) x) x)) v =
    (fderivWithin ℂ (writtenInExtChartAt (complexModel d) (complexModel e) x f)
      (Set.range (complexModel d)) ((extChartAt (complexModel d) x) x)) v
  exact congrArg (fun L ↦ L v) (hd.restrictScalars_fderivWithin ℝ (by simp)).symm

end StableFoliationsSupport
end HolomorphicAnosov
