import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

/-! Complex linearity of tangent-field pullback through holomorphic charts. -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Pullback through a holomorphic atlas chart commutes with multiplication of tangent fields by
`Complex.I`. (Zhang, Lemma 2.4, eq. (13), p. 7, eq. (2), p. 4) -/
theorem imaginary_field_chart_transport
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ atlas (ComplexModel d) X)
    (Y : (x : X) → TangentSpace (complexModel d) x)
    {z : ComplexModel d} (hz : z ∈ c.target) :
    VectorField.mpullback (realModel d) (realModel d) c.symm
        (fun x ↦ complexTangentToReal d x (Complex.I • Y x)) z =
      Complex.I • (show ComplexModel d from
        VectorField.mpullback (realModel d) (realModel d) c.symm
          (fun x ↦ complexTangentToReal d x (Y x)) z) := by
  have hf : MDifferentiableAt (complexModel d) (complexModel d) c.symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := complexModel d) (n := ∞) hc) hz).mdifferentiableAt
      (by simp)
  have hr : MDifferentiableAt (realModel d) (realModel d) c.symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := realModel d) (n := ∞) hc) hz).mdifferentiableAt
      (by simp)
  have hder : mfderiv (realModel d) (realModel d) c.symm z =
      (mfderiv (complexModel d) (complexModel d) c.symm z).restrictScalars ℝ := by
    ext v
    apply (tangentSpaceCastModel (realModel d) (c.symm z)).injective
    rw [hf.mfderiv_abuse, hr.mfderiv_abuse]
    have hd := hf.differentiableWithinAt_writtenInExtChartAt
    change (fderivWithin ℝ (writtenInExtChartAt (complexModel d) (complexModel d) z c.symm)
        (Set.range (complexModel d)) ((extChartAt (complexModel d) z) z)) v =
      (fderivWithin ℂ (writtenInExtChartAt (complexModel d) (complexModel d) z c.symm)
        (Set.range (complexModel d)) ((extChartAt (complexModel d) z) z)) v
    exact congrArg (fun L ↦ L v) (hd.restrictScalars_fderivWithin ℝ (by simp)).symm
  have hi : (mfderiv (realModel d) (realModel d) c.symm z).IsInvertible := by
    have h := isInvertible_mfderivWithin_extend_symm (I := realModel d)
      (IsManifold.subset_maximalAtlas (n := 1) hc) (y := z) (by simpa using hz)
    simpa using h
  simp only [VectorField.mpullback_apply]
  apply hi.inverse_apply_eq.mpr
  rw [hder]
  change Complex.I • Y (c.symm z) =
    (mfderiv (complexModel d) (complexModel d) c.symm z)
      (Complex.I • ((mfderiv (complexModel d) (complexModel d) c.symm z).restrictScalars ℝ).inverse
        (complexTangentToReal d (c.symm z) (Y (c.symm z))))
  rw [map_smul]
  congr 1
  apply (complexTangentToReal d (c.symm z)).injective
  have hcancel := (hi.self_apply_inverse
    (complexTangentToReal d (c.symm z) (Y (c.symm z)))).symm
  rw [hder] at hcancel
  exact hcancel

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
