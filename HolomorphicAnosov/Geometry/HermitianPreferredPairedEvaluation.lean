import HolomorphicAnosov.Geometry.HermitianMetricVolumeDefinitions
import HolomorphicAnosov.Geometry.HermitianPreferredTopFormCoordinates
import HolomorphicAnosov.Geometry.HermitianCoreGramDeterminantChange
import HolomorphicAnosov.Geometry.ComplexPairedTopFormDeterminant

/-! This file evaluates the preferred Hermitian top form on paired vector families. (Demailly, VI §4.) -/


open scoped ContDiff
namespace HolomorphicAnosov
universe u
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the preferred Hermitian top form on any complex vector family, paired with its imaginary multiples, equals its Hermitian Gram determinant. (Demailly, VI §4.) -/
theorem hermitian_preferred_paired_evaluation {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (h : HermitianTangentMetricCore d X) (x : X)
    (v : Fin d → TangentSpace (complexModel d) x) :
    hermitianMetricPreferredTopForm h x (fun i : ComplexPairedIndex d ↦
      complexTangentToReal d x (if i.2 = 0 then v i.1 else Complex.I • v i.1)) =
      (Matrix.det fun i j ↦ (h x).inner (v j) (v i)).re := by
  rw [hermitian_preferred_topForm_coordinates]
  let A : ComplexModel d →ₗ[ℂ] ComplexModel d :=
    (Pi.basisFun ℂ (Fin d)).constr ℂ (show Fin d → ComplexModel d from v)
  have hA (i : Fin d) : A (Pi.single i 1) = v i := by
    simpa only [Pi.basisFun_apply] using
      (Pi.basisFun ℂ (Fin d)).constr_basis ℂ (show Fin d → ComplexModel d from v) i
  have hp : (fun i : ComplexPairedIndex d ↦
      complexTangentToReal d x (if i.2 = 0 then v i.1 else Complex.I • v i.1)) =
      (fun i ↦ A (Pi.single i.1 (if i.2 = 0 then (1 : ℂ) else Complex.I))) := by
    funext i
    change (if i.2 = 0 then v i.1 else Complex.I • v i.1) = _
    split_ifs with hi
    · exact (hA i.1).symm
    · have he : Pi.single i.1 Complex.I = Complex.I • Pi.single i.1 (1 : ℂ) := by
        ext j
        by_cases hj : j = i.1 <;> simp [hj]
      rw [he, map_smul, hA]
  rw [hp, complexCoordinateTopForm_paired_map]
  have hg := hermitian_core_gram_det_change (V := ComplexModel d) (h x)
    (Pi.basisFun ℂ (Fin d)) (show Fin d → ComplexModel d from v)
  have hdet : (Matrix.of fun i j ↦ (Pi.basisFun ℂ (Fin d)).repr (v j) i).det = A.det := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin d))]
    congr 1
    ext i j
    simp only [Matrix.of_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, hA]

  rw [hdet] at hg
  have hr := congrArg Complex.re hg
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Pi.basisFun_apply] using hr.symm
end HolomorphicAnosov
