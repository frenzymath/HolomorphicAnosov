import HolomorphicAnosov.Analysis.Complex.QCPositiveDiskBoundary
import HolomorphicAnosov.Analysis.Complex.QCPositiveBoundaryBoundedComponent
import HolomorphicAnosov.Analysis.Complex.QCLimitWinding
import HolomorphicAnosov.Analysis.Complex.QCCompactBoundaryTransport
import HolomorphicAnosov.Analysis.Complex.QCScaledRectangleModel

namespace HolomorphicAnosov
open Set Filter _root_.Topology Analysis.MarkedRectangle

/-- The four corners of a marked conformal rectangle model are positive on
its Jordan boundary. Extend the given closed rectangle homeomorphism to an
ambient representative. It is holomorphic in the interior and injective on
the entire closed rectangle. The inverse identity makes its derivative
nonzero, so the disk argument principle gives positive winding on each
contained circle. Transport the explicit positive rectangle marks by the
confined Jordan-boundary homotopy and the literal frontier homeomorphism.
Source: Lehto--Virtanen I.§§2.3,3.1 pp.14–17, with the boundary extension
and orientation convention in the definition of the marked rectangle model. -/
theorem qc_marked_model_positive {Q : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hmod : HasMarkedConformalModulus Q p m) (hcompact : IsCompact (closure Q)) :
    PositiveBoundaryFour Q p := by
  classical
  have hQopen := (qc_marked_model_geometry hmod hcompact).1
  obtain ⟨a, b, ha, hb, hm, F, Fi, hF, hFi, hbij, hmaps, hFiF, hFFi,
    e, he, hcorner⟩ := hmod
  let R := OpenRectangle a b
  let K := ClosedRectangle a b
  have hRopen : IsOpen R := RectangleModelPreparation.isOpen_openRectangle a b
  have hcl : closure R = K := RectangleModelPreparation.closure_openRectangle ha hb
  have hRsub : R ⊆ K := hcl ▸ subset_closure
  let f : ℂ → ℂ := Function.extend Subtype.val (fun z : K ↦ (e z : ℂ)) (fun _ ↦ 0)
  have hfe (z : K) : f z = (e z : ℂ) := Subtype.val_injective.extend_apply _ _ z
  have hfF : EqOn f F R := fun z hz ↦ (hfe ⟨z, hRsub hz⟩).trans (he _ hz)
  have hfc : ContinuousOn f K := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp e.continuous).congr (fun z ↦ (hfe z).symm)
  have hfi : InjOn f K := by
    intro z hz w hw heq
    rw [hfe ⟨z, hz⟩, hfe ⟨w, hw⟩] at heq
    exact congrArg Subtype.val (e.injective (Subtype.ext heq))
  have hfh : DifferentiableOn ℂ f R := hF.congr hfF
  have hfbij : BijOn f R Q := hbij.congr hfF.symm
  have himage : f '' R = Q := hfbij.image_eq
  obtain ⟨β, hβpos, u, hu, hup⟩ := qc_positive_rectangle_marks ha hb
  have hRconv : Convex ℝ R := by
    change Convex ℝ (Complex.equivRealProdLm.toLinearMap ⁻¹' (Ioo 0 a ×ˢ Ioo 0 b))
    exact ((convex_Ioo (0 : ℝ) a).prod (convex_Ioo (0 : ℝ) b)).linear_preimage
      Complex.equivRealProdLm.toLinearMap
  have hRne : R.Nonempty := by
    refine ⟨(a / 2 : ℝ) + (b / 2 : ℝ) * Complex.I, ?_⟩
    simp only [R, OpenRectangle, Complex.mem_reProdIm, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, mul_one, zero_add, mem_Ioo]
    exact ⟨⟨half_pos ha, half_lt_self ha⟩, ⟨half_pos hb, half_lt_self hb⟩⟩
  have hRcompact : IsCompact (closure R) := by
    rw [hcl]
    exact isCompact_Icc.reProdIm isCompact_Icc
  have hRconn : IsConnected R := (hRconv.isPathConnected hRne).isConnected
  let γ : Circle → ℂ := fun z ↦ (β z : ℂ)
  have hγ : _root_.Topology.IsEmbedding γ := _root_.Topology.IsEmbedding.subtypeVal.comp β.isEmbedding
  have hfront : frontier R = range γ := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw⟩ := β.surjective ⟨z, hz⟩
      exact ⟨w, congrArg Subtype.val hw⟩
    · rintro ⟨w, rfl⟩
      exact (β w).property
  obtain ⟨E, hE, hEcl⟩ := qc_positive_boundary_bounded_component R hRne hRopen hRconn
    (hRcompact.isBounded.subset subset_closure) γ hγ hfront β hβpos
  obtain ⟨ef, hef⟩ := qc_compact_boundary_transport hRopen hRcompact
    (hcl.symm ▸ hfc) (hcl.symm ▸ hfi) (himage.symm ▸ hQopen)
  let β' := β.trans ef
  have hβ' (z : Circle) : (β' z : ℂ) = f (β z) := hef (β z)
  have hpositive := qc_positive_jordan_boundary f R hRopen
    (hcl.symm ▸ hfc) (hcl.symm ▸ hfi) β hβpos E hE hEcl β' hβ'
  have hpos : PositiveBoundaryParametrization (f '' R) β' := by
    apply hpositive
    intro c r hr hball
    have hfa : AnalyticOnNhd ℂ f (Metric.closedBall c r) :=
      (hfh.analyticOnNhd hRopen).mono hball
    have hderiv : deriv f c ≠ 0 := by
      have hcR : c ∈ R := hball (Metric.mem_closedBall_self hr.le)
      have hd := (hfh.differentiableAt (hRopen.mem_nhds hcR)).hasDerivAt
      have hid := (hFi.differentiableAt (hQopen.mem_nhds (hfbij.mapsTo hcR))).hasDerivAt.comp c hd
      have heq : (Fi ∘ f) =ᶠ[𝓝 c] id := (hRopen.eventually_mem hcR).mono fun z hz ↦ by
        change Fi (f z) = z
        rw [hfF hz]
        exact hFiF z hz
      have hp := hid.deriv
      rw [heq.deriv_eq] at hp
      intro hzero
      simp [hzero] at hp
    exact normalized_phase_of_holomorphic_disk hr hfa (hfi.mono (hball.trans hRsub)) hderiv
  have hmarks : PositiveBoundaryFour (f '' R) (fun i ↦ f (RectangleCorner a b i)) :=
    ⟨β', hpos, u, hu, fun i ↦ (hβ' (u i)).trans (congrArg f (hup i))⟩
  rw [himage] at hmarks
  have hcorners : (fun i ↦ f (RectangleCorner a b i)) = p := by
    funext i
    exact (hfe ⟨RectangleCorner a b i, RectangleModelPreparation.corner_mem ha hb i⟩).trans
      (hcorner i _ rfl)
  rwa [hcorners] at hmarks

end HolomorphicAnosov
