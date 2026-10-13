import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicFrameRestrict
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CovariantDerivativeSectionCongr
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov
namespace ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

variable [T2Space X] [SecondCountableTopology X] [CompactSpace X]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The distribution of a compatible quotient-line connection is involutive for smooth tangent fields (Zhang, Definition 2.1 and (2), p.4). -/
theorem bott_involutive_of_compatible
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V))
    (D : QuotientLineConnection.Connection P)
    (hD : QuotientLineConnection.IsCompatible D)
    (U : Opens X) (Y Z : (x : X) → TangentSpace (complexModel d) x)
    (hY : QuotientLineConnection.IsSmoothTangentField U Y)
    (hZ : QuotientLineConnection.IsSmoothTangentField U Z)
    (hYP : ∀ x ∈ U, Y x ∈ P x) (hZP : ∀ x ∈ U, Z x ∈ P x)
    (x : X) (hx : x ∈ U) :
    QuotientLineConnection.bottBracket Y Z x ∈ P x := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hcover x
  let W : Opens X := U ⊓ V
  let eW : QuotientLineConnection.HolomorphicFrame P W :=
    holomorphicFrameRestrict e inf_le_right
  have hz : ∀ y ∈ W, QuotientLineConnection.projection P y (Z y) = 0 := by
    intro y hy
    exact (Submodule.Quotient.mk_eq_zero (P y)).mpr (hZP y hy.1)
  have hzero : ∀ v : TangentSpace (realModel d) x,
      QuotientLineConnection.covariantDerivative D eW
        (fun y ↦ QuotientLineConnection.projection P y (Z y)) x ⟨hx, hxV⟩ v = 0 := by
    intro v
    rw [covariantDerivative_section_congr D W eW _ (fun _ ↦ 0) hz x ⟨hx, hxV⟩ v]
    have hc : eW.coefficient (fun _ ↦ 0) = fun _ ↦ 0 := by
      funext y
      simp [QuotientLineConnection.HolomorphicFrame.coefficient]
    unfold QuotientLineConnection.covariantDerivative
    rw [hc]
    simp [QuotientLineConnection.realDifferential, mfderiv_const]
  have hb := hD.2 W eW Y Z (hY.mono inter_subset_left) (hZ.mono inter_subset_left)
    (fun y hy ↦ hYP y hy.1) x ⟨hx, hxV⟩
  rw [hzero, hzero, smul_zero, sub_self, smul_zero] at hb
  exact (Submodule.Quotient.mk_eq_zero (P x)).mp hb.symm


end ConnectionCalculus
end HolomorphicAnosov
