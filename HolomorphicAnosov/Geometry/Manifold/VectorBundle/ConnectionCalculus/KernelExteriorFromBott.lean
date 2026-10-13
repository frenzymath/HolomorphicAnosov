import HolomorphicAnosov.Paper.Zhang.Support.BottBracketChartTransport
import HolomorphicAnosov.Paper.Zhang.Support.ImaginaryFieldChartTransport
import HolomorphicAnosov.Paper.Zhang.Support.RealCovariantExteriorCoordinateEvaluation

open Set TopologicalSpace HolomorphicAnosov
open HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open scoped ContDiff Manifold Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace HolomorphicAnosov.ConnectionCalculus

/-- The exterior derivative of a holomorphic quotient coordinate vanishes on pairs of kernel fields
whose Bott bracket lies in the kernel. (Zhang, §2.1, (2), p.4 and Lemma 2.4, (12)–(13), p.7) -/
theorem kernel_exterior_from_bott {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d)) (hc : c ∈ atlas (ComplexModel d) X)
    (θ : ComplexModel d → ComplexModel d →L[ℂ] ℂ)
    (hθ : ∀ w (hw : w ∈ c.target ∩ c.symm ⁻¹' (V : Set X)), ∀ v : ComplexModel d,
      θ w v = e.coordinate (c.symm w) hw.2
        (QuotientLineConnection.projection U (c.symm w)
          (mfderiv (complexModel d) (complexModel d) c.symm w
            ((NormedSpace.fromTangentSpace w).symm v))))
    {z : ComplexModel d} (hz : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X))
    (hθd : DifferentiableAt ℂ θ z)
    (Y Z : (x : X) → TangentSpace (complexModel d) x)
    (hY : QuotientLineConnection.IsSmoothTangentField V Y)
    (hZ : QuotientLineConnection.IsSmoothTangentField V Z)
    (hIY : QuotientLineConnection.IsSmoothTangentField V (fun x ↦ Complex.I • Y x))
    (hIZ : QuotientLineConnection.IsSmoothTangentField V (fun x ↦ Complex.I • Z x))
    (hYU : ∀ x ∈ V, Y x ∈ U x) (hZU : ∀ x ∈ V, Z x ∈ U x)
    (hbrzero : QuotientLineConnection.bottBracket Y Z (c.symm z) ∈ U (c.symm z)) :
    let Yc : ComplexModel d → ComplexModel d := VectorField.mpullback (realModel d)
      (realModel d) c.symm (fun x ↦ complexTangentToReal d x (Y x))
    let Zc : ComplexModel d → ComplexModel d := VectorField.mpullback (realModel d)
      (realModel d) c.symm (fun x ↦ complexTangentToReal d x (Z x))
    fderiv ℝ θ z (Yc z) (Zc z) - fderiv ℝ θ z (Zc z) (Yc z) = 0 := by
  let Tc (T : (x : X) → TangentSpace (complexModel d) x) :
      ComplexModel d → ComplexModel d := VectorField.mpullback (realModel d)
        (realModel d) c.symm (fun x ↦ complexTangentToReal d x (T x))
  let g (T : (x : X) → TangentSpace (complexModel d) x) :=
    e.coefficient (fun x ↦ QuotientLineConnection.projection U x (T x))
  have hcm : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
    IsManifold.subset_maximalAtlas hc
  have hrm : c ∈ IsManifold.maximalAtlas (realModel d) ∞ X :=
    IsManifold.subset_maximalAtlas hc
  have hrm1 : c ∈ IsManifold.maximalAtlas (realModel d) 1 X :=
    IsManifold.subset_maximalAtlas hc
  have hci := contMDiffAt_symm_of_mem_maximalAtlas hrm hz.1
  have hi (w : ComplexModel d) (hw : w ∈ c.target) :
      (mfderiv (realModel d) (realModel d) c.symm w).IsInvertible := by
    have h := isInvertible_mfderivWithin_extend_symm (I := realModel d) hrm1
      (y := w) (by simpa using hw)
    simpa using h
  have hder (w : ComplexModel d) (hw : w ∈ c.target) :
      mfderiv (realModel d) (realModel d) c.symm w =
        (mfderiv (complexModel d) (complexModel d) c.symm w).restrictScalars ℝ := by
    have hf := (contMDiffAt_symm_of_mem_maximalAtlas hcm hw).mdifferentiableAt (by simp)
    have hr := (contMDiffAt_symm_of_mem_maximalAtlas hrm hw).mdifferentiableAt (by simp)
    ext v
    apply (tangentSpaceCastModel (realModel d) (c.symm w)).injective
    rw [hf.mfderiv_abuse, hr.mfderiv_abuse]
    have hd := hf.differentiableWithinAt_writtenInExtChartAt
    change (fderivWithin ℝ (writtenInExtChartAt (complexModel d) (complexModel d) w c.symm)
      (range (complexModel d)) (extChartAt (complexModel d) w w)) v =
      (fderivWithin ℂ (writtenInExtChartAt (complexModel d) (complexModel d) w c.symm)
      (range (complexModel d)) (extChartAt (complexModel d) w w)) v
    exact congrArg (fun L ↦ L v) (hd.restrictScalars_fderivWithin ℝ (by simp)).symm
  have hcoef (T : (x : X) → TangentSpace (complexModel d) x)
      (w : ComplexModel d) (hw : w ∈ c.target ∩ c.symm ⁻¹' (V : Set X)) :
      θ w (Tc T w) = g T (c.symm w) := by
    rw [hθ w hw]
    have h := (hi w hw.1).self_apply_inverse
      (complexTangentToReal d (c.symm w) (T (c.symm w)))
    change mfderiv (realModel d) (realModel d) c.symm w (Tc T w) =
      complexTangentToReal d (c.symm w) (T (c.symm w)) at h
    rw [hder w hw.1] at h
    change mfderiv (complexModel d) (complexModel d) c.symm w
      ((NormedSpace.fromTangentSpace w).symm (Tc T w)) = T (c.symm w) at h
    rw [h]
    simp only [g, QuotientLineConnection.HolomorphicFrame.coefficient,
      dite_eq_left (show c.symm w ∈ V from hw.2)]
  have hTp (T : (x : X) → TangentSpace (complexModel d) x)
      (hT : QuotientLineConnection.IsSmoothTangentField V T) :
      ContMDiffAt (realModel d) (realModel d).tangent ∞
        (fun x ↦ (⟨x, complexTangentToReal d x (T x)⟩ : TangentBundle (realModel d) X))
        (c.symm z) := (hT _ hz.2).contMDiffAt (V.isOpen.mem_nhds hz.2)
  have hTcd (T : (x : X) → TangentSpace (complexModel d) x)
      (hT : QuotientLineConnection.IsSmoothTangentField V T) :
      DifferentiableAt ℝ (Tc T) z := by
    have h := (hTp T hT).mpullback_vectorField_preimage hci (hi z hz.1) (by simp)
    exact (contMDiffAt_vectorSpace_iff_contDiffAt.mp h).differentiableAt (by simp)
  have hbr := bott_bracket_chart_transport c hci Y Z
    ((hTp Y hY).mdifferentiableAt (by simp))
    ((hTp Z hZ).mdifferentiableAt (by simp))
    ((hTp _ hIY).mdifferentiableAt (by simp))
    ((hTp _ hIZ).mdifferentiableAt (by simp))
  have hIT (T : (x : X) → TangentSpace (complexModel d) x) :
      Tc (fun x ↦ Complex.I • T x) =ᶠ[nhds z] (fun w ↦ Complex.I • Tc T w) := by
    filter_upwards [c.open_target.mem_nhds hz.1] with w hw
    exact imaginary_field_chart_transport c hc T hw
  have hbr' := (hIT Y).lieBracket_vectorField_eq (𝕜 := ℝ) (hIT Z)
  change Tc (QuotientLineConnection.bottBracket Y Z) z =
    (1 / 2 : ℝ) • (VectorField.lieBracket ℝ (Tc Y) (Tc Z) z -
      VectorField.lieBracket ℝ (Tc (fun x ↦ Complex.I • Y x))
        (Tc (fun x ↦ Complex.I • Z x)) z) at hbr
  rw [hbr'] at hbr
  have hbcoef := hcoef (QuotientLineConnection.bottBracket Y Z) z hz
  rw [hbr] at hbcoef
  have hzero (T : (x : X) → TangentSpace (complexModel d) x)
      (hTU : ∀ x ∈ V, T x ∈ U x) :
      (fun w ↦ θ w (Tc T w)) =ᶠ[nhds z] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [(c.isOpen_inter_preimage_symm V.isOpen).mem_nhds hz] with w hw
    rw [hcoef T w hw]
    have hp : QuotientLineConnection.projection U (c.symm w) (T (c.symm w)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (hTU _ hw.2)
    simp only [g, QuotientLineConnection.HolomorphicFrame.coefficient,
      hp, map_zero, dite_eq_ite, ite_self]
  have hbzero : g (QuotientLineConnection.bottBracket Y Z) (c.symm z) = 0 := by
    have hp : QuotientLineConnection.projection U (c.symm z)
        (QuotientLineConnection.bottBracket Y Z (c.symm z)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hbrzero
    simp only [g, QuotientLineConnection.HolomorphicFrame.coefficient,
      hp, map_zero, dite_eq_ite, ite_self]
  have hid := real_covariant_exterior_coordinate_evaluation θ
    (0 : ComplexModel d →L[ℝ] ℂ) (Tc Y) (Tc Z)
    (fderiv ℂ θ z) hθd.hasFDerivAt (by simp) (hTcd Y hY) (hTcd Z hZ)
  rw [(hzero Y hYU).fderiv_eq, (hzero Z hZU).fderiv_eq, hbcoef, hbzero] at hid
  simpa only [zero_apply, zero_mul, add_zero, sub_zero,
    fderiv_const_apply, mul_zero, zero_sub, neg_zero] using hid.symm

end HolomorphicAnosov.ConnectionCalculus

