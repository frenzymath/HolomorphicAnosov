import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace




/-! This file compares complex manifold derivatives with their realifications. (Demailly, I §3.C, p. 23).
-/
open scoped ContDiff
namespace HolomorphicAnosov
universe u v

/-- A complex derivative intertwines the native tangent realifications with the corresponding real and complex derivatives. (Demailly, I §3.C, p. 23). -/
theorem mfderiv_complex_to_real {d e : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y]
    {f : X → Y} {x : X}
    (hf : MDifferentiableAt (complexModel d) (complexModel e) f x)
    (v : TangentSpace (complexModel d) x) :
    mfderiv (realModel d) (realModel e) f x (complexTangentToReal d x v) =
      complexTangentToReal e (f x) (mfderiv (complexModel d) (complexModel e) f x v) := by
  have hc := hf.differentiableWithinAt_writtenInExtChartAt
  have hd : DifferentiableAt ℂ
      (writtenInExtChartAt (complexModel d) (complexModel e) x f)
      ((extChartAt (complexModel d) x) x) := by
    simpa only [complexModel, modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ] using hc
  have hr : MDifferentiableAt (realModel d) (realModel e) f x := by
    apply (mdifferentiableAt_iff f x).mpr
    exact ⟨hf.continuousAt, (hd.restrictScalars ℝ).differentiableWithinAt⟩
  rw [hr.mfderiv, hf.mfderiv]
  simp only [realModel, complexModel, modelWithCornersSelf_coe, Set.range_id,
    fderivWithin_univ]
  change (fderiv ℝ (writtenInExtChartAt (complexModel d) (complexModel e) x f)
      ((extChartAt (complexModel d) x) x)) v =
    (fderiv ℂ (writtenInExtChartAt (complexModel d) (complexModel e) x f)
      ((extChartAt (complexModel d) x) x)) v
  exact congrArg (fun L ↦ L v) (hd.fderiv_restrictScalars (𝕜 := ℝ))

end HolomorphicAnosov

