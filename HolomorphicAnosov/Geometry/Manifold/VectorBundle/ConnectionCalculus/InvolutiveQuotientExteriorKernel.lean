import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.KernelExteriorFromBott
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicSectionRestrict
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.SmoothTangentFieldOfHolomorphic
import HolomorphicAnosov.Paper.Zhang.Support.HolomorphicTangentFieldExtension
import HolomorphicAnosov.Paper.Zhang.Support.QuotientCoordinateFormRegularity

open Set TopologicalSpace HolomorphicAnosov HolomorphicAnosov.ConnectionCalculus
open HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open scoped ContDiff Manifold Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace HolomorphicAnosov.ConnectionCalculus

/-- The coordinate exterior derivative of the quotient form of a holomorphic involutive tangent
subbundle vanishes on pairs of kernel vectors. (Zhang, §2.1, (2), p.4 and Lemma 2.4, (12)–(13),
p.7; Demailly, V §11, p.267) -/
theorem involutive_quotient_exterior_kernel {d r : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU : IsHolomorphicTangentSubbundle r U) (hline : IsQuotientTangentLine U)
    (hInv : ∀ (W : Opens X) (Y Z : (x : X) → TangentSpace (complexModel d) x),
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun x ↦ (⟨x, Y x⟩ : TangentBundle (complexModel d) X)) W →
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun x ↦ (⟨x, Z x⟩ : TangentBundle (complexModel d) X)) W →
      (∀ x ∈ W, Y x ∈ U x) → (∀ x ∈ W, Z x ∈ U x) →
      ∀ x ∈ W, QuotientLineConnection.bottBracket Y Z x ∈ U x)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d)) (hc : c ∈ atlas (ComplexModel d) X)
    (θ : ComplexModel d → ComplexModel d →L[ℂ] ℂ)
    (hθ : ∀ w (hw : w ∈ c.target ∩ c.symm ⁻¹' (V : Set X)), ∀ v : ComplexModel d,
      θ w v = e.coordinate (c.symm w) hw.2
        (QuotientLineConnection.projection U (c.symm w)
          (mfderiv (complexModel d) (complexModel d) c.symm w
            ((NormedSpace.fromTangentSpace w).symm v))))
    {z : ComplexModel d} (hz : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X))
    (v w : ComplexModel d) (hv : θ z v = 0) (hw : θ z w = 0) :
    fderiv ℝ θ z v w - fderiv ℝ θ z w v = 0 := by
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
  have hreg := quotient_coordinate_form_regularity U hU hline V e c hcm θ hθ
  have hθd := (hreg.1.differentiableOn (by simp) z hz).differentiableAt
    ((c.isOpen_inter_preimage_symm V.isOpen).mem_nhds hz)
  let D : ComplexModel d →L[ℂ] TangentSpace (complexModel d) (c.symm z) :=
    (mfderiv (complexModel d) (complexModel d) c.symm z).comp
      (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap
  have hmem (a : ComplexModel d) (ha : θ z a = 0) : D a ∈ U (c.symm z) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply (e.coordinate (c.symm z) hz.2).injective
    rw [map_zero]
    exact (hθ z hz a).symm.trans ha
  obtain ⟨VY, Y, _, hxY, hYV, hYx, _, hYhol, _, hYU⟩ :=
    holomorphic_tangent_field_extension U hU V (c.symm z) hz.2 (D v) 0 (hmem v hv)
  obtain ⟨VZ, Z, _, hxZ, hZV, hZx, _, hZhol, _, hZU⟩ :=
    holomorphic_tangent_field_extension U hU V (c.symm z) hz.2 (D w) 0 (hmem w hw)
  let W : Opens X := VY ⊓ VZ
  have hxW : c.symm z ∈ W := ⟨hxY, hxZ⟩
  have hWV : W ≤ V := fun _ ha ↦ hYV ha.1
  have hYholW := hYhol.mono (show (W : Set X) ⊆ VY from fun _ ha ↦ ha.1)
  have hZholW := hZhol.mono (show (W : Set X) ⊆ VZ from fun _ ha ↦ ha.2)
  have hYUW : ∀ x ∈ W, Y x ∈ U x := fun x hx ↦ hYU x hx.1
  have hZUW : ∀ x ∈ W, Z x ∈ U x := fun x hx ↦ hZU x hx.2
  let eW : QuotientLineConnection.HolomorphicFrame U W :=
    { sectionValue := e.sectionValue
      holomorphic := holomorphic_section_restrict hWV e.holomorphic
      coordinate := fun y hy ↦ e.coordinate y (hWV hy)
      normalized := fun y hy ↦ e.normalized y (hWV hy) }
  have hθW : ∀ b (hb : b ∈ c.target ∩ c.symm ⁻¹' (W : Set X)),
      ∀ t : ComplexModel d, θ b t = eW.coordinate (c.symm b) hb.2
        (QuotientLineConnection.projection U (c.symm b)
          (mfderiv (complexModel d) (complexModel d) c.symm b
            ((NormedSpace.fromTangentSpace b).symm t))) :=
    fun b hb t ↦ hθ b ⟨hb.1, hWV hb.2⟩ t
  have hY := smoothTangentField_of_holomorphic W.isOpen hYholW
  have hZ := smoothTangentField_of_holomorphic W.isOpen hZholW
  have hIY := smoothTangentField_of_holomorphic W.isOpen
    (hYholW.const_smul_section (a := Complex.I))
  have hIZ := smoothTangentField_of_holomorphic W.isOpen
    (hZholW.const_smul_section (a := Complex.I))
  have hcancel := kernel_exterior_from_bott U W eW c hc θ hθW ⟨hz.1, hxW⟩
    hθd Y Z hY hZ hIY hIZ hYUW hZUW
    (hInv W Y Z hYholW hZholW hYUW hZUW (c.symm z) hxW)
  have hpull (T : (x : X) → TangentSpace (complexModel d) x)
      (a : ComplexModel d) (hTa : T (c.symm z) = D a) :
      VectorField.mpullback (realModel d) (realModel d) c.symm
        (fun y ↦ complexTangentToReal d y (T y)) z = a := by
    apply (hi z hz.1).inverse_apply_eq.mpr
    change complexTangentToReal d (c.symm z) (T (c.symm z)) =
      mfderiv (realModel d) (realModel d) c.symm z
        ((NormedSpace.fromTangentSpace z).symm a)
    rw [hTa, hder z hz.1]
    rfl
  dsimp only at hcancel
  rw [hpull Y v hYx, hpull Z w hZx] at hcancel
  exact hcancel

end HolomorphicAnosov.ConnectionCalculus

