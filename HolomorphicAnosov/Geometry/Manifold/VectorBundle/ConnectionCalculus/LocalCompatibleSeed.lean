import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ScalarDifferentialChartTransportG12
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.NormalizedCovectorConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.InvolutiveQuotientExteriorKernel
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.LocalFrameConnectionForm
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicFrameCover

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
open HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
set_option backward.isDefEq.respectTransparency false
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

/-- A local smooth quotient-line connection form compatible with the Dolbeault and Bott identities.
(Zhang, §2.1, (2)–(4), pp.4–5) -/
structure LocalCompatibleSeed
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) where
  O : Opens X
  e₀ : QuotientLineConnection.HolomorphicFrame P O
  A : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ
  smooth : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (c : OpenPartialHomeomorph X (ComplexModel d)),
    c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
    ContDiffOn ℝ ∞ (fun z ↦ (localFrameConnectionForm e₀ A V e (c.symm z)).comp
      ((mfderiv (realModel d) (realModel d) c.symm z).comp
        (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap))
      (c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ (O : Set X)))
  typeOne : ∀ (x : X), x ∈ O → ∀ v : TangentSpace (complexModel d) x,
    A x (complexTangentToReal d x (Complex.I • v)) =
      Complex.I * A x (complexTangentToReal d x v)
  bott : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (Y Z : (x : X) → TangentSpace (complexModel d) x),
    QuotientLineConnection.IsSmoothTangentField V Y →
    QuotientLineConnection.IsSmoothTangentField V Z →
    (∀ x ∈ V, Y x ∈ P x) → ∀ x (hx : x ∈ V), x ∈ O →
    let s := fun y ↦ QuotientLineConnection.projection P y (Z y)
    let D := fun v ↦ (e.coordinate x hx).symm
      (QuotientLineConnection.realDifferential (e.coefficient s) x v +
        e.coefficient s x * localFrameConnectionForm e₀ A V e x v)
    (1 / 2 : ℂ) • (D (complexTangentToReal d x (Y x)) -
      Complex.I • D (complexTangentToReal d x (Complex.I • Y x))) =
      QuotientLineConnection.projection P x
        (QuotientLineConnection.bottBracket Y Z x)

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Every point of a holomorphic involutive subbundle with quotient rank one has a neighborhood
carrying a smooth Dolbeault- and Bott-compatible connection seed. (Zhang, §2.1, (2)–(4), pp.4–5) -/
theorem exists_local_compatible_seed
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (hInv : ∀ (U : Opens X)
      (Y Z : (x : X) → TangentSpace (complexModel d) x),
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun x ↦ (⟨x, Y x⟩ : TangentBundle (complexModel d) X)) U →
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun x ↦ (⟨x, Z x⟩ : TangentBundle (complexModel d) X)) U →
      (∀ x ∈ U, Y x ∈ P x) → (∀ x ∈ U, Z x ∈ P x) →
      ∀ x ∈ U, QuotientLineConnection.bottBracket Y Z x ∈ P x)
    (x : X) : ∃ s : LocalCompatibleSeed P, x ∈ s.O := by
  classical
  obtain ⟨V, hxV, ⟨e⟩⟩ := holomorphic_frame_cover P hP hline x
  obtain ⟨W, T, hW, hxW, hWV, hT, hTe⟩ := e.holomorphic x hxV
  let c := chartAt (ComplexModel d) x
  let O : Opens X := ⟨W ∩ c.source, hW.inter c.open_source⟩
  let e₀ : QuotientLineConnection.HolomorphicFrame P O :=
    { sectionValue := e.sectionValue
      holomorphic := holomorphic_section_restrict (show (O : Set X) ⊆ V from fun _ hy ↦ hWV hy.1) e.holomorphic
      coordinate := fun y hy ↦ e.coordinate y (hWV hy.1)
      normalized := fun y hy ↦ e.normalized y (hWV hy.1) }
  let α : (y : X) → TangentSpace (complexModel d) y →L[ℂ] ℂ := fun y ↦
    if hy : y ∈ O then
      ((e₀.coordinate y hy).toLinearMap.comp (P y).mkQ).toContinuousLinearMap
    else 0
  have hα (y : X) (hy : y ∈ O) (v : TangentSpace (complexModel d) y) :
      α y v = e₀.coordinate y hy (QuotientLineConnection.projection P y v) := by
    simp only [α, dite_eq_left hy]
    rfl
  have hc : c ∈ atlas (ComplexModel d) X := chart_mem_atlas _ _
  have hcm : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
    IsManifold.subset_maximalAtlas hc
  let U : Set (ComplexModel d) := c.target ∩ c.symm ⁻¹' (O : Set X)
  have hU : IsOpen U := c.isOpen_inter_preimage_symm O.isOpen
  let θ : ComplexModel d → ComplexModel d →L[ℂ] ℂ := fun z ↦
    (α (c.symm z)).comp ((mfderiv (complexModel d) (complexModel d) c.symm z).comp
      (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap)
  have hθ : ∀ z (hz : z ∈ U), ∀ v : ComplexModel d,
      θ z v = e₀.coordinate (c.symm z) hz.2
        (QuotientLineConnection.projection P (c.symm z)
          (mfderiv (complexModel d) (complexModel d) c.symm z
            ((NormedSpace.fromTangentSpace z).symm v))) := by
    intro z hz v
    exact hα (c.symm z) hz.2 _
  have hreg := quotient_coordinate_form_regularity P hP hline O e₀ c hcm θ hθ
  let Tc := VectorField.mpullback (complexModel d) (complexModel d) c.symm T
  have hi (w : ComplexModel d) (hw : w ∈ c.target) :
      (mfderiv (complexModel d) (complexModel d) c.symm w).IsInvertible := by
    have h := isInvertible_mfderivWithin_extend_symm (I := complexModel d)
      (IsManifold.subset_maximalAtlas hc) (y := w) (by simpa using hw)
    simpa using h
  have hTc : ContDiffOn ℂ ∞ Tc U := by
    intro w hw
    have hp := (hT.contMDiffAt (hW.mem_nhds hw.2.1)).mpullback_vectorField_preimage
      (contMDiffAt_symm_of_mem_maximalAtlas hcm hw.1) (hi w hw.1) (by simp)
    exact (contMDiffAt_vectorSpace_iff_contDiffAt.mp hp).contDiffWithinAt
  have hnormal : ∀ w ∈ U, θ w (Tc w) = 1 := by
    intro w hw
    rw [hθ w hw]
    change e₀.coordinate (c.symm w) hw.2
      (QuotientLineConnection.projection P (c.symm w)
        ((mfderiv (complexModel d) (complexModel d) c.symm w)
          ((mfderiv (complexModel d) (complexModel d) c.symm w).inverse (T (c.symm w))))) = 1
    rw [(hi w hw.1).self_apply_inverse, hTe (c.symm w) hw.2.1]
    exact e₀.normalized (c.symm w) hw.2
  have hkernel : ∀ z ∈ U, ∀ v w, θ z v = 0 → θ z w = 0 →
      fderiv ℂ θ z v w - fderiv ℂ θ z w v = 0 := by
    intro z hz v w hv hw
    have hk := involutive_quotient_exterior_kernel P hP hline hInv O e₀ c hc θ hθ
      hz v w hv hw
    have hd := (hreg.1.differentiableOn (by simp) z hz).differentiableAt
      (hU.mem_nhds hz)
    have heq := hd.hasFDerivAt.restrictScalars ℝ
    rw [heq.fderiv] at hk
    exact hk
  obtain ⟨Ac, hAc, hAcT, hclosed⟩ :=
    normalized_covector_connection θ Tc hU hreg.1 hTc hnormal hkernel
  let Aℂ : (y : X) → TangentSpace (complexModel d) y →L[ℂ] ℂ := fun y ↦
    (Ac (c y)).comp ((NormedSpace.fromTangentSpace (c y)).toContinuousLinearMap.comp
      (mfderiv (complexModel d) (complexModel d) c y))
  let A : (y : X) → TangentSpace (realModel d) y →L[ℝ] ℂ := fun y ↦
    (Aℂ y).restrictScalars ℝ
  have hA_typeOne (y : X) (v : TangentSpace (complexModel d) y) :
      A y (complexTangentToReal d y (Complex.I • v)) =
        Complex.I * A y (complexTangentToReal d y v) := by
    change Aℂ y (Complex.I • v) = Complex.I * Aℂ y v
    simp only [map_smul, smul_eq_mul]
  have hAcR : ContDiffOn ℝ ∞ (fun z ↦ (Ac z).restrictScalars ℝ) U := by
    exact (ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel d) ℂ ℝ ℝ).contDiff.comp_contDiffOn
      (hAc.restrict_scalars ℝ)
  have hder (f : X → ComplexModel d) (y : X)
      (hf : MDifferentiableAt (complexModel d) (complexModel d) f y)
      (hr : MDifferentiableAt (realModel d) (realModel d) f y) :
      mfderiv (realModel d) (realModel d) f y =
        (mfderiv (complexModel d) (complexModel d) f y).restrictScalars ℝ := by
    ext v
    rw [hf.mfderiv_abuse, hr.mfderiv_abuse]
    have hd := hf.differentiableWithinAt_writtenInExtChartAt
    change (fderivWithin ℝ (writtenInExtChartAt (complexModel d) (complexModel d) y f)
      (range (complexModel d)) (extChartAt (complexModel d) y y)) v =
      (fderivWithin ℂ (writtenInExtChartAt (complexModel d) (complexModel d) y f)
      (range (complexModel d)) (extChartAt (complexModel d) y y)) v
    exact congrArg (fun L ↦ L v) (hd.restrictScalars_fderivWithin ℝ (by simp)).symm
  have hAreal (y : X) (hy : y ∈ c.source) :
      A y = ((Ac (c y)).restrictScalars ℝ).comp
        (mfderiv (realModel d) (realModel d) c y) := by
    have hcc := (contMDiffAt_of_mem_maximalAtlas hcm hy).mdifferentiableAt (by simp)
    have hcr := (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := realModel d) (n := ∞) hc) hy).mdifferentiableAt (by simp)
    rw [hder c y hcc hcr]
    rfl
  have hbase (b : OpenPartialHomeomorph X (ComplexModel d))
      (hb : b ∈ IsManifold.maximalAtlas (complexModel d) ∞ X) :
      ContDiffOn ℝ ∞ (fun z ↦ (A (b.symm z)).comp
        ((mfderiv (realModel d) (realModel d) b.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap))
        (b.target ∩ b.symm ⁻¹' (O : Set X)) := by
    intro z hz
    have hbc := contMDiffAt_symm_of_mem_maximalAtlas hb hz.1
    have hbr : ContMDiffAt (realModel d) (realModel d) ∞ b.symm z := by
      obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp hbc
      exact contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩
    have hcr := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := realModel d) (n := ∞) hc) hz.2.2
    have htrans : ContDiffAt ℝ ∞ (fun w ↦ c (b.symm w)) z :=
      (hcr.comp z hbr).contDiffAt
    have hzin : c (b.symm z) ∈ U :=
      ⟨c.map_source hz.2.2, by change c.symm (c (b.symm z)) ∈ O; rw [c.left_inv hz.2.2]; exact hz.2⟩
    have hform := (hAcR.contDiffAt (hU.mem_nhds hzin)).comp z htrans
    have hreg := hform.clm_comp (htrans.fderiv_right (by simp))
    apply (hreg.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [(b.isOpen_inter_preimage_symm O.isOpen).mem_nhds hz] with w hw
    rw [hAreal (b.symm w) hw.2.2]
    have hbwc := contMDiffAt_symm_of_mem_maximalAtlas hb hw.1
    have hbwr : ContMDiffAt (realModel d) (realModel d) ∞ b.symm w := by
      obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp hbwc
      exact contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩
    have hcwr := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := realModel d) (n := ∞) hc) hw.2.2
    have hcomp := mfderiv_comp w (hcwr.mdifferentiableAt (by simp))
      (hbwr.mdifferentiableAt (by simp))
    ext v
    change (Ac (c (b.symm w)))
      ((mfderiv (realModel d) (realModel d) c (b.symm w))
        ((mfderiv (realModel d) (realModel d) b.symm w) v)) =
      (Ac (c (b.symm w))) (fderiv ℝ (fun w ↦ c (b.symm w)) w v)
    rw [← ContinuousLinearMap.comp_apply, ← hcomp]
    congr 1
    exact congrArg (fun L ↦ L v) (mfderiv_eq_fderiv (𝕜 := ℝ) (f := c ∘ b.symm) (x := w))
  have hsmooth (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (b : OpenPartialHomeomorph X (ComplexModel d))
      (hb : b ∈ IsManifold.maximalAtlas (complexModel d) ∞ X) :
      ContDiffOn ℝ ∞ (fun z ↦ (localFrameConnectionForm e₀ A V e (b.symm z)).comp
        ((mfderiv (realModel d) (realModel d) b.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap))
        (b.target ∩ b.symm ⁻¹' ((V : Set X) ∩ (O : Set X))) := by
    intro z hz
    let g := e₀.coefficient e.sectionValue
    have hg := (frame_coefficient_holomorphic hP hline O V e₀ e.sectionValue
      e.holomorphic).contMDiffAt ((O.isOpen.inter V.isOpen).mem_nhds ⟨hz.2.2, hz.2.1⟩)
    have hgc : ContDiffAt ℝ ∞ (fun w ↦ g (b.symm w)) z :=
      ((hg.comp z (contMDiffAt_symm_of_mem_maximalAtlas hb hz.1)).contDiffAt).restrict_scalars ℝ
    have hg0 : g (b.symm z) ≠ 0 := frame_transition_nonzero O V e₀ e _ hz.2.2 hz.2.1
    have hbaseAt := (hbase b hb).contDiffAt
      ((b.isOpen_inter_preimage_symm O.isOpen).mem_nhds ⟨hz.1, hz.2.2⟩)
    have hreg := hbaseAt.add ((hgc.inv hg0).smul (hgc.fderiv_right (by simp)))
    apply (hreg.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [(b.isOpen_inter_preimage_symm (V.isOpen.inter O.isOpen)).mem_nhds hz]
      with w hw
    rw [localFrameConnectionForm, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp]
    rw [scalar_differential_chart_transport g b hb w hw.1
      (frame_coefficient_real_differentiableAt hP hline O V e₀ e.sectionValue
        e.holomorphic _ hw.2.2 hw.2.1)]
    rfl
  have hImaginary (V : Opens X) (T : (y : X) → TangentSpace (complexModel d) y)
      (hT : QuotientLineConnection.IsSmoothTangentField V T) :
      QuotientLineConnection.IsSmoothTangentField V (fun y ↦ Complex.I • T y) := by
    intro y hy
    let ec := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) y
    let er := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) y
    have htr := hT.contMDiffAt (V.isOpen.mem_nhds hy)
    have htc := (er.contMDiffAt_section_iff
      (FiberBundle.mem_baseSet_trivializationAt' y)).mp htr
    apply ContMDiffAt.contMDiffWithinAt
    apply (er.contMDiffAt_section_iff
      (FiberBundle.mem_baseSet_trivializationAt' y)).mpr
    have hm : ContDiff ℝ ∞ (fun v : ComplexModel d ↦ Complex.I • v) :=
      contDiff_const_smul Complex.I
    apply (hm.comp_contMDiffAt htc).congr_of_eventuallyEq
    filter_upwards [(chartAt (ComplexModel d) y).open_source.mem_nhds
      (mem_chart_source (ComplexModel d) y)] with w hw
    dsimp only [Function.comp_def, er]
    rw [complexTangentToReal_coordinates y ⟨w, Complex.I • T w⟩ hw,
      complexTangentToReal_coordinates y ⟨w, T w⟩ hw]
    exact (ec.linear ℂ hw).2 _ _
  refine ⟨{ O := O
            e₀ := e₀
            A := A
            smooth := hsmooth
            typeOne := fun y _ v ↦ hA_typeOne y v
            bott := ?_ }, ⟨hxW, mem_chart_source _ x⟩⟩
  intro V e Y Z hY hZ hYP y hyV hyO
  let z := c y
  have hcy : c.symm z = y := c.left_inv hyO.2
  have hz : z ∈ U := ⟨c.map_source hyO.2, by change c.symm z ∈ O; rwa [hcy]⟩
  have hzV : c.symm z ∈ V := hcy ▸ hyV
  let Fc (T : (x : X) → TangentSpace (complexModel d) x) :
      ComplexModel d → ComplexModel d := VectorField.mpullback (realModel d)
        (realModel d) c.symm (fun x ↦ complexTangentToReal d x (T x))
  let g₀ (T : (x : X) → TangentSpace (complexModel d) x) :=
    e₀.coefficient (fun x ↦ QuotientLineConnection.projection P x (T x))
  have hrm : c ∈ IsManifold.maximalAtlas (realModel d) ∞ X :=
    IsManifold.subset_maximalAtlas hc
  have hrm1 : c ∈ IsManifold.maximalAtlas (realModel d) 1 X :=
    IsManifold.subset_maximalAtlas hc
  have hci := contMDiffAt_symm_of_mem_maximalAtlas hrm hz.1
  have hiR (w : ComplexModel d) (hw : w ∈ c.target) :
      (mfderiv (realModel d) (realModel d) c.symm w).IsInvertible := by
    have h := isInvertible_mfderivWithin_extend_symm (I := realModel d) hrm1
      (y := w) (by simpa using hw)
    simpa using h
  have hderR (w : ComplexModel d) (hw : w ∈ c.target) :
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
      (w : ComplexModel d) (hw : w ∈ U) :
      θ w (Fc T w) = g₀ T (c.symm w) := by
    rw [hθ w hw]
    have h := (hiR w hw.1).self_apply_inverse
      (complexTangentToReal d (c.symm w) (T (c.symm w)))
    change mfderiv (realModel d) (realModel d) c.symm w (Fc T w) =
      complexTangentToReal d (c.symm w) (T (c.symm w)) at h
    rw [hderR w hw.1] at h
    change mfderiv (complexModel d) (complexModel d) c.symm w
      ((NormedSpace.fromTangentSpace w).symm (Fc T w)) = T (c.symm w) at h
    rw [h]
    simp only [g₀, QuotientLineConnection.HolomorphicFrame.coefficient,
      dite_eq_left (show c.symm w ∈ O from hw.2)]
  have hTp (T : (x : X) → TangentSpace (complexModel d) x)
      (hT : QuotientLineConnection.IsSmoothTangentField V T) :
      ContMDiffAt (realModel d) (realModel d).tangent ∞
        (fun x ↦ (⟨x, complexTangentToReal d x (T x)⟩ : TangentBundle (realModel d) X))
        (c.symm z) := hT.contMDiffAt (V.isOpen.mem_nhds hzV)
  have hTcd (T : (x : X) → TangentSpace (complexModel d) x)
      (hT : QuotientLineConnection.IsSmoothTangentField V T) :
      ContDiffAt ℝ ∞ (Fc T) z := by
    have h := (hTp T hT).mpullback_vectorField_preimage hci (hiR z hz.1) (by simp)
    exact contMDiffAt_vectorSpace_iff_contDiffAt.mp h
  have hbr := bott_bracket_chart_transport c hci Y Z
    ((hTp Y hY).mdifferentiableAt (by simp))
    ((hTp Z hZ).mdifferentiableAt (by simp))
    ((hTp _ (hImaginary V Y hY)).mdifferentiableAt (by simp))
    ((hTp _ (hImaginary V Z hZ)).mdifferentiableAt (by simp))
  have hIT (T : (x : X) → TangentSpace (complexModel d) x) :
      Fc (fun x ↦ Complex.I • T x) =ᶠ[nhds z] (fun w ↦ Complex.I • Fc T w) := by
    filter_upwards [c.open_target.mem_nhds hz.1] with w hw
    exact imaginary_field_chart_transport c hc T hw
  have hbr' := (hIT Y).lieBracket_vectorField_eq (𝕜 := ℝ) (hIT Z)
  change Fc (QuotientLineConnection.bottBracket Y Z) z =
    (1 / 2 : ℝ) • (VectorField.lieBracket ℝ (Fc Y) (Fc Z) z -
      VectorField.lieBracket ℝ (Fc (fun x ↦ Complex.I • Y x))
        (Fc (fun x ↦ Complex.I • Z x)) z) at hbr
  rw [hbr'] at hbr
  have hbcoef := hcoef (QuotientLineConnection.bottBracket Y Z) z hz
  rw [hbr] at hbcoef
  have hzero : (fun w ↦ θ w (Fc Y w)) =ᶠ[nhds z] (fun _ ↦ (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hz,
      hci.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds hzV)] with w hw hwV
    rw [hcoef Y w hw]
    have hp : QuotientLineConnection.projection P (c.symm w) (Y (c.symm w)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (hYP _ hwV)
    simp only [g₀, QuotientLineConnection.HolomorphicFrame.coefficient,
      hp, map_zero, dite_eq_ite, ite_self]
  have hθd := (hreg.1.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hid := real_covariant_exterior_coordinate_evaluation θ
    ((Ac z).restrictScalars ℝ) (Fc Y) (Fc Z)
    (fderiv ℂ θ z) hθd.hasFDerivAt (by intro v; exact (Ac z).map_smul _ v)
    ((hTcd Y hY).differentiableAt (by simp)) ((hTcd Z hZ).differentiableAt (by simp))
  rw [hzero.fderiv_eq, hzero.eq_of_nhds, hbcoef, (hθd.hasFDerivAt.restrictScalars ℝ).fderiv] at hid
  have hclosedz := hclosed z hz (Fc Y z) (Fc Z z)
  rw [hzero.eq_of_nhds] at hclosedz
  simp only [ContinuousLinearMap.coe_restrictScalars', fderiv_const_apply, zero_apply,
    mul_zero, add_zero, sub_zero] at hid hclosedz
  rw [hclosedz] at hid
  let t : X → ℂ := e₀.coefficient e.sectionValue
  let u : X → ℂ := e.coefficient (fun w ↦ QuotientLineConnection.projection P w (Z w))
  let f₀ : ComplexModel d → ℂ := fun w ↦ g₀ Z (c.symm w)
  let f : ComplexModel d → ℂ := fun w ↦ u (c.symm w)
  let t₁ : ComplexModel d → ℂ := fun w ↦ t (c.symm w)
  have hfeq : (fun w ↦ θ w (Fc Z w)) =ᶠ[nhds z] f₀ := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hcoef Z w hw
  have hf₀ : ContDiffAt ℝ ∞ f₀ z := by
    have hθR : ContDiffAt ℝ ∞ (fun w ↦ (θ w).restrictScalars ℝ) z :=
      (ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel d) ℂ ℝ ℝ).contDiff.contDiffAt.comp z
        ((hreg.1.contDiffAt (hU.mem_nhds hz)).restrict_scalars ℝ)
    exact (hθR.clm_apply (hTcd Z hZ)).congr_of_eventuallyEq hfeq.symm
  have ht : ContMDiffAt (complexModel d) 𝓘(ℂ, ℂ) ∞ t (c.symm z) :=
    (frame_coefficient_holomorphic hP hline O V e₀ e.sectionValue e.holomorphic).contMDiffAt
      ((O.isOpen.inter V.isOpen).mem_nhds ⟨hz.2, hzV⟩)
  have ht₁ : ContDiffAt ℝ ∞ t₁ z :=
    ((ht.comp z (contMDiffAt_symm_of_mem_maximalAtlas hcm hz.1)).contDiffAt).restrict_scalars ℝ
  have ht0 : t₁ z ≠ 0 := frame_transition_nonzero O V e₀ e _ hz.2 hzV
  have hmul : f₀ =ᶠ[nhds z] (fun w ↦ t₁ w * f w) := by
    filter_upwards [hU.mem_nhds hz,
      hci.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds hzV)] with w hw hwV
    exact frame_coefficient_change O V e₀ e
      (fun w ↦ QuotientLineConnection.projection P w (Z w)) _ hw.2 hwV
  have hf : ContDiffAt ℝ ∞ f z := by
    have hquot : ContDiffAt ℝ ∞ (fun w ↦ f₀ w / t₁ w) z := by
      simpa only [div_eq_mul_inv, Pi.inv_apply] using! hf₀.mul (ht₁.inv ht0)
    apply hquot.congr_of_eventuallyEq
    filter_upwards [hmul, ht₁.continuousAt.eventually_ne ht0] with w hw htw
    exact (eq_div_iff htw).mpr (by rw [hw]; ring)
  have hdf : fderiv ℝ f₀ z = t₁ z • fderiv ℝ f z + f z • fderiv ℝ t₁ z := by
    rw [hmul.fderiv_eq]
    exact ((ht₁.differentiableAt (by simp)).hasFDerivAt.mul
      (hf.differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [hfeq.fderiv_eq, hfeq.eq_of_nhds, hdf, hmul.eq_of_nhds] at hid
  have hchartleft : (mfderiv (realModel d) (realModel d) c (c.symm z)).comp
      (mfderiv (realModel d) (realModel d) c.symm z) =
      ContinuousLinearMap.id ℝ (ComplexModel d) := by
    have hh := mfderiv_extend_comp_mfderivWithin_extend_symm (I := realModel d)
      hrm1 (y := z) (by simpa using hz.1)
    simpa using! hh
  have hAval (T : (w : X) → TangentSpace (complexModel d) w) :
      A (c.symm z) (complexTangentToReal d (c.symm z) (T (c.symm z))) = Ac z (Fc T z) := by
    rw [hAreal _ hz.2.2, ContinuousLinearMap.comp_apply, c.right_inv hz.1]
    have hh := (hiR z hz.1).self_apply_inverse
      (complexTangentToReal d (c.symm z) (T (c.symm z)))
    change mfderiv (realModel d) (realModel d) c.symm z (Fc T z) = _ at hh
    rw [← hh]
    exact congrArg (fun v ↦ Ac z v) (congrArg (fun L ↦ L (Fc T z)) hchartleft)
  have hscalar (a : X → ℂ) (ha : ContDiffAt ℝ ∞ (fun w ↦ a (c.symm w)) z) :
      MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) a (c.symm z) := by
    have hca := contMDiffAt_of_mem_maximalAtlas hrm (c.map_target hz.1)
    have ha' : ContMDiffAt (realModel d) 𝓘(ℝ, ℂ) ∞ (fun w ↦ a (c.symm w))
        (c (c.symm z)) := by
      rw [c.right_inv hz.1]
      exact ha.contMDiffAt
    have hh := ha'.comp (c.symm z) hca
    apply (hh.congr_of_eventuallyEq ?_).mdifferentiableAt (by simp)
    filter_upwards [c.open_source.mem_nhds (c.map_target hz.1)] with w hw
    exact congrArg a (c.left_inv hw).symm
  have hdiff (a : X → ℂ) (ha : ContDiffAt ℝ ∞ (fun w ↦ a (c.symm w)) z)
      (T : (w : X) → TangentSpace (complexModel d) w) :
      QuotientLineConnection.realDifferential a (c.symm z)
        (complexTangentToReal d (c.symm z) (T (c.symm z))) =
        fderiv ℝ (fun w ↦ a (c.symm w)) z (Fc T z) := by
    have hh := congrArg (fun L ↦ L (Fc T z))
      (scalar_differential_chart_transport a c hcm z hz.1 (hscalar a ha))
    have hiT := (hiR z hz.1).self_apply_inverse
      (complexTangentToReal d (c.symm z) (T (c.symm z)))
    change mfderiv (realModel d) (realModel d) c.symm z (Fc T z) = _ at hiT
    change QuotientLineConnection.realDifferential a (c.symm z)
      (mfderiv (realModel d) (realModel d) c.symm z (Fc T z)) = _ at hh
    rwa [hiT] at hh
  have hscalarbott :
      (1 / 2 : ℂ) *
        (QuotientLineConnection.realDifferential u (c.symm z)
            (complexTangentToReal d (c.symm z) (Y (c.symm z))) +
          u (c.symm z) * localFrameConnectionForm e₀ A V e (c.symm z)
            (complexTangentToReal d (c.symm z) (Y (c.symm z))) -
          Complex.I * (QuotientLineConnection.realDifferential u (c.symm z)
            (complexTangentToReal d (c.symm z) (Complex.I • Y (c.symm z))) +
          u (c.symm z) * localFrameConnectionForm e₀ A V e (c.symm z)
            (complexTangentToReal d (c.symm z) (Complex.I • Y (c.symm z))))) =
        e.coordinate (c.symm z) hzV (QuotientLineConnection.projection P (c.symm z)
          (QuotientLineConnection.bottBracket Y Z (c.symm z))) := by
    simp only [localFrameConnectionForm, add_apply,
      smul_apply, smul_eq_mul]
    rw [hdiff u hf Y, hdiff u hf (fun w ↦ Complex.I • Y w),
      hdiff t ht₁ Y, hdiff t ht₁ (fun w ↦ Complex.I • Y w),
      hAval Y, hAval (fun w ↦ Complex.I • Y w), (hIT Y).eq_of_nhds]
    have hchange := frame_coefficient_change O V e₀ e
      (fun w ↦ QuotientLineConnection.projection P w
        (QuotientLineConnection.bottBracket Y Z w)) (c.symm z) hz.2 hzV
    change g₀ (QuotientLineConnection.bottBracket Y Z) (c.symm z) =
      t₁ z * e.coefficient (fun w ↦ QuotientLineConnection.projection P w
        (QuotientLineConnection.bottBracket Y Z w)) (c.symm z) at hchange
    rw [QuotientLineConnection.HolomorphicFrame.coefficient, dite_eq_left hzV] at hchange
    rw [hchange] at hid
    change (1 / 2 : ℂ) *
      (fderiv ℝ f z (Fc Y z) + f z * (Ac z (Fc Y z) + (t₁ z)⁻¹ * fderiv ℝ t₁ z (Fc Y z)) -
        Complex.I * (fderiv ℝ f z (Complex.I • Fc Y z) +
          f z * (Ac z (Complex.I • Fc Y z) + (t₁ z)⁻¹ * fderiv ℝ t₁ z (Complex.I • Fc Y z)))) = _
    apply mul_left_cancel₀ ht0
    simp only [add_apply, smul_apply, smul_eq_mul] at hid
    calc
      _ = (1 / 2 : ℂ) *
        (t₁ z * fderiv ℝ f z (Fc Y z) + f z * fderiv ℝ t₁ z (Fc Y z) +
          Ac z (Fc Y z) * (t₁ z * f z) -
          Complex.I * (t₁ z * fderiv ℝ f z (Complex.I • Fc Y z) +
            f z * fderiv ℝ t₁ z (Complex.I • Fc Y z) +
            Ac z (Complex.I • Fc Y z) * (t₁ z * f z))) := by field_simp; ring
      _ = _ := sub_eq_zero.mp hid
  apply (e.coordinate y hyV).injective
  simp only [map_smul, map_sub, LinearEquiv.apply_symm_apply, smul_eq_mul]
  let F : X → ℂ := fun w ↦ (1 / 2 : ℂ) *
    (QuotientLineConnection.realDifferential u w (complexTangentToReal d w (Y w)) +
      u w * localFrameConnectionForm e₀ A V e w (complexTangentToReal d w (Y w)) -
      Complex.I * (QuotientLineConnection.realDifferential u w
        (complexTangentToReal d w (Complex.I • Y w)) +
      u w * localFrameConnectionForm e₀ A V e w
        (complexTangentToReal d w (Complex.I • Y w))))
  let R : X → ℂ := e.coefficient (fun w ↦ QuotientLineConnection.projection P w
    (QuotientLineConnection.bottBracket Y Z w))
  have hh : F (c.symm z) = R (c.symm z) := by
    simpa only [F, R, QuotientLineConnection.HolomorphicFrame.coefficient,
      dite_eq_left hzV] using hscalarbott
  have hh' : F y = R y := by simpa only [hcy] using hh
  simpa only [F, R, u, QuotientLineConnection.HolomorphicFrame.coefficient,
    dite_eq_left hyV] using hh'

end HolomorphicAnosov.ConnectionCalculus

