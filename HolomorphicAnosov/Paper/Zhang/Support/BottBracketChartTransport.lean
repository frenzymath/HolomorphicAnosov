import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

/-! Chart transport of the real Bott bracket. (Zhang, Lemma 2.4, eq. (13)) -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The Bott bracket pulled back through a smooth inverse chart is half the difference of the real
brackets of the pulled-back fields and their imaginary multiples. (Zhang, Lemma 2.4, eq. (13),
p. 7) -/
theorem bott_bracket_chart_transport
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (c : OpenPartialHomeomorph X (ComplexModel d)) {z : ComplexModel d}
    (hc : ContMDiffAt (realModel d) (realModel d) ∞ c.symm z)
    (Y Z : (x : X) → TangentSpace (complexModel d) x)
    (hY : MDifferentiableAt (realModel d) (realModel d).tangent
      (fun x ↦ (⟨x, complexTangentToReal d x (Y x)⟩ : TangentBundle (realModel d) X))
      (c.symm z))
    (hZ : MDifferentiableAt (realModel d) (realModel d).tangent
      (fun x ↦ (⟨x, complexTangentToReal d x (Z x)⟩ : TangentBundle (realModel d) X))
      (c.symm z))
    (hIY : MDifferentiableAt (realModel d) (realModel d).tangent
      (fun x ↦ (⟨x, complexTangentToReal d x (Complex.I • Y x)⟩ :
        TangentBundle (realModel d) X)) (c.symm z))
    (hIZ : MDifferentiableAt (realModel d) (realModel d).tangent
      (fun x ↦ (⟨x, complexTangentToReal d x (Complex.I • Z x)⟩ :
        TangentBundle (realModel d) X)) (c.symm z)) :
    (mfderiv (realModel d) (realModel d) c.symm z).inverse
        (complexTangentToReal d (c.symm z)
          (QuotientLineConnection.bottBracket Y Z (c.symm z))) =
      (1 / 2 : ℝ) •
        (VectorField.lieBracket ℝ
            (VectorField.mpullback (realModel d) (realModel d) c.symm
              (fun x ↦ complexTangentToReal d x (Y x)))
            (VectorField.mpullback (realModel d) (realModel d) c.symm
              (fun x ↦ complexTangentToReal d x (Z x))) z -
          VectorField.lieBracket ℝ
            (VectorField.mpullback (realModel d) (realModel d) c.symm
              (fun x ↦ complexTangentToReal d x (Complex.I • Y x)))
            (VectorField.mpullback (realModel d) (realModel d) c.symm
              (fun x ↦ complexTangentToReal d x (Complex.I • Z x))) z) := by
  have : IsManifold (realModel d) (minSmoothness ℝ 2) X :=
    IsManifold.of_le (n := ∞) (by simp)
  have hYZ := VectorField.mpullback_mlieBracket hY hZ hc (by simp)
  have hIYZ := VectorField.mpullback_mlieBracket hIY hIZ hc (by simp)
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [QuotientLineConnection.bottBracket, hhalf, Complex.coe_smul,
    map_smul, ContinuousLinearEquiv.apply_symm_apply, map_smul, map_sub]
  change (1 / 2 : ℝ) •
    (VectorField.mpullback (realModel d) (realModel d) c.symm _ z -
      VectorField.mpullback (realModel d) (realModel d) c.symm _ z) = _
  rw [hYZ, hIYZ]
  simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ]

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport

