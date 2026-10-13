import HolomorphicAnosov.Geometry.HermitianMetricVolumeDefinitions
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! This file computes the preferred Hermitian top form in preferred chart coordinates. (Demailly, VI §4.) -/


open scoped ContDiff
namespace HolomorphicAnosov
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
variable [IsManifold (complexModel d) ∞ X]
attribute [local instance] complex_isManifold_real
set_option backward.isDefEq.respectTransparency false in
/-- In the tangent coordinates defined by the preferred chart, the preferred Hermitian top form is the Gram determinant times the paired coordinate form. (Demailly, VI §4.) -/
theorem hermitian_preferred_topForm_coordinates (h : HermitianTangentMetricCore d X) (x : X)
    (v : ComplexPairedIndex d → TangentSpace (realModel d) x) :
    hermitianMetricPreferredTopForm h x v =
      (Matrix.det fun i j : Fin d ↦ (h x).inner (Pi.single j 1) (Pi.single i 1)).re *
        complexCoordinateTopForm d v := by
  have hd : mfderiv (realModel d) (realModel d)
      (chartAt (ComplexModel d) x) x = ContinuousLinearMap.id ℝ (ComplexModel d) :=
    mfderiv_extChartAt_self (I := realModel d)
  have hdi : mfderiv (complexModel d) (complexModel d)
      (chartAt (ComplexModel d) x).symm ((chartAt (ComplexModel d) x) x) =
        ContinuousLinearMap.id ℂ (TangentSpace (complexModel d) ((chartAt (ComplexModel d) x) x)) := by
    simpa only [complexModel, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ,
      extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id]
      using (mfderivWithin_range_extChartAt_symm (I := complexModel d) (x := x))
  unfold hermitianMetricPreferredTopForm hermitianMetricChartVolumeDensity
    hermitianTangentChartCoefficient hermitianTangentChartFrame
    hermitianTangentPairing realTangentCoordinateTopFormAt
  dsimp only
  rw [hdi, hd]
  change (Matrix.det fun i j : Fin d ↦
    (h ((chartAt (ComplexModel d) x).symm ((chartAt (ComplexModel d) x) x))).inner
      (Pi.single j 1) (Pi.single i 1)).re * complexCoordinateTopForm d v = _
  rw [(chartAt (ComplexModel d) x).left_inv (mem_chart_source _ x)]
end HolomorphicAnosov
