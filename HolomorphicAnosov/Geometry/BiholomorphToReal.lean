import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexToRealMap
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! This file constructs the underlying real diffeomorphism of a biholomorphism and relates their derivatives (Demailly, I §3.C; Ghys, §2). -/

open scoped ContDiff

universe u v

namespace HolomorphicAnosov

/-- The same equivalence as `f`, with real smoothness in both directions (Demailly, I §3.C, p.23; Ghys, §2, p.588). -/
def Biholomorph.toReal {d e : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y]
    (f : Biholomorph d e X Y) :
    Diffeomorph (realModel d) (realModel e) X Y ∞ :=
  { toEquiv := f.toEquiv
    contMDiff_toFun := contMDiff_complex_to_real f.contMDiff
    contMDiff_invFun := contMDiff_complex_to_real f.symm.contMDiff }

attribute [local instance] complex_isManifold_real

/-- The actual derivative is obtained by scalar restriction in the preferred charts (Demailly, I §3.C, p.23). -/
theorem Biholomorph.real_mfderiv_eq_complex {d e : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y]
    [IsManifold (complexModel e) ∞ Y]
    (f : Biholomorph d e X Y) (x : X) :
    mfderiv (realModel d) (realModel e) f x =
      (mfderiv (complexModel d) (complexModel e) f x).restrictScalars ℝ := by
  have hc := f.contMDiff.mdifferentiable (by simp) x
  have hr : MDifferentiableAt (realModel d) (realModel e) f x :=
    f.toReal.contMDiff.mdifferentiable (by simp) x
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

/-- The actual derivative commutes with the canonical tangent realifications (Demailly, I §3.C, p.23). -/
theorem Biholomorph.real_mfderiv_realification {d e : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y]
    [IsManifold (complexModel e) ∞ Y]
    (f : Biholomorph d e X Y) (x : X)
    (v : TangentSpace (complexModel d) x) :
    mfderiv (realModel d) (realModel e) f.toReal x (complexTangentToReal d x v) =
      complexTangentToReal e (f x) (mfderiv (complexModel d) (complexModel e) f x v) := by
  change mfderiv (realModel d) (realModel e) f x (complexTangentToReal d x v) = _
  rw [Biholomorph.real_mfderiv_eq_complex]
  rfl

end HolomorphicAnosov
