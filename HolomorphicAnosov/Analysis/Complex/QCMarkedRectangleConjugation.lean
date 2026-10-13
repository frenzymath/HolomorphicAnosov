import HolomorphicAnosov.Analysis.Complex.MarkedConformalModulus
import HolomorphicAnosov.Analysis.Complex.QCHolomorphicCompositionDistortion
import HolomorphicAnosov.Analysis.MarkedRectangleVerticalSides
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import HolomorphicAnosov.Analysis.Complex.QCRealLinearDeterminant

/-! # Regular conjugation by marked conformal rectangle models

Source: Lehto–Virtanen, *Quasiconformal Mappings in the Plane* (1973),
I.§3.3 and the first paragraph of the proof of Theorem 3.1, pp.17–18.
-/

namespace HolomorphicAnosov.Analysis

open Set MarkedRectangle

/-- A regular map between marked quadrilaterals has a regular rectangle conjugate
with the same directional distortion and the prescribed horizontal endpoint separation.
The interior conjugation identity uses actual biholomorphic rectangle coordinates.

Source: Lehto–Virtanen I.§3.3 and Theorem 3.1, pp.17–18, the canonical rectangle
reduction preceding (3.3). Choose the two rectangle witnesses in the marked-modulus
relations, retaining their positive dimensions, holomorphic inverses, and same-map
closure homeomorphisms. Let F be the first interior map and G the inverse of the
second. On the source rectangle define W=G∘f∘F. Restrict the original partial
homeomorphism to closure Q: compactness and closure Q⊆U show that its image is
closure(f(Q)), by continuity, density of Q, and compactness of its image. This
restriction is a homeomorphism onto that closure. Compose it with the two closure
homeomorphisms to extend W continuously to the closed source rectangle, and extend
arbitrarily outside that closed rectangle. The interior expression is unchanged.

The inverse identities show that F and G have nonzero complex derivatives. Their
real derivatives are invertible similarities with positive determinant. The chain
rule therefore gives an invertible positive derivative of W; analytic regularity
of F,G and the real C¹ regularity of f give C¹ regularity of W on the open rectangle.
The holomorphic-composition distortion theorem transfers the bound K. Interior
bijections give the exact target rectangle. The composite closure homeomorphism
carries all four corners to the corresponding corners. The open-vertical-side
theorem sends each horizontal endpoint to its corresponding target vertical side;
their real parts differ by A, so their distance is at least A. No boundary
derivative, extra smoothness of Q, or finite-energy premise is used.
-/
theorem qc_marked_rectangle_conjugation
    (U V : Set ℂ) (f : OpenPartialHomeomorph ℂ ℂ)
    (hf_source : f.source = U) (_hf_target : f.target = V)
    (hC1 : ContDiffOn ℝ 1 (f : ℂ → ℂ) U)
    (hderiv : ∀ z ∈ U, ∃ L : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (f : ℂ → ℂ) (L : ℂ →L[ℝ] ℂ) z ∧ 0 < (L : ℂ →L[ℝ] ℂ).det)
    (K : ℝ)
    (hDistortion : ∀ z ∈ U, ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (f : ℂ → ℂ) z v‖ ≤ K * ‖fderiv ℝ (f : ℂ → ℂ) z w‖)
    (Q : Set ℂ) (p : Fin 4 → ℂ) (m m' : ℝ)
    (hQcompact : IsCompact (closure Q)) (hQinside : closure Q ⊆ U)
    (hQmod : HasMarkedConformalModulus Q p m)
    (hImageMod : HasMarkedConformalModulus (f '' Q) (fun i ↦ f (p i)) m') :
    ∃ a b A B : ℝ, 0 < a ∧ 0 < b ∧ 0 < A ∧ 0 < B ∧ m = a / b ∧ m' = A / B ∧
      ∃ F G W : ℂ → ℂ,
        DifferentiableOn ℂ F (OpenRectangle a b) ∧ BijOn F (OpenRectangle a b) Q ∧
        DifferentiableOn ℂ G (f '' Q) ∧ BijOn G (f '' Q) (OpenRectangle A B) ∧
        EqOn W (G ∘ f ∘ F) (OpenRectangle a b) ∧
        ContinuousOn W (ClosedRectangle a b) ∧
        ContDiffOn ℝ 1 W (OpenRectangle a b) ∧
        BijOn W (OpenRectangle a b) (OpenRectangle A B) ∧
        (∀ z ∈ OpenRectangle a b, ∃ L : ℂ ≃L[ℝ] ℂ,
          HasFDerivAt W (L : ℂ →L[ℝ] ℂ) z ∧ 0 < (L : ℂ →L[ℝ] ℂ).det) ∧
        (∀ z ∈ OpenRectangle a b, ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
          ‖fderiv ℝ W z v‖ ≤ K * ‖fderiv ℝ W z w‖) ∧
        (∀ y ∈ Ioo 0 b,
          A ≤ dist (W (y * Complex.I)) (W ((a : ℂ) + y * Complex.I))) := by
  classical
  obtain ⟨a, b, ha, hb, hm, F, Fi, hF, hFi, hFbij, hFim, hFiF, hFFi,
    eF, heF, hpF⟩ := hQmod
  obtain ⟨A, B, hA, hB, hm', H, G, hH, hG, hHbij, hGm, hGH, hHG,
    eH, heH, hpH⟩ := hImageMod
  have hR := RectangleModelPreparation.isOpen_openRectangle a b
  have hR' := RectangleModelPreparation.isOpen_openRectangle A B
  have hQsrc : Q ⊆ f.source := fun z hz ↦ hf_source.symm ▸ hQinside (subset_closure hz)
  have hQopen : IsOpen Q := by
    rw [← hFbij.image_eq]
    exact lebl_scalar_open_image hR hF hFbij.injOn hR subset_rfl
  have hQ'open := f.isOpen_image_of_subset_source hQopen hQsrc
  have hcsrc : closure Q ⊆ f.source := hf_source.symm ▸ hQinside
  have hfc : ContinuousOn f (closure Q) := f.continuousOn.mono hcsrc
  have hclosure : f '' closure Q = closure (f '' Q) := by
    apply Subset.antisymm hfc.image_closure
    exact closure_minimal (image_mono subset_closure)
      (hQcompact.image_of_continuousOn hfc).isClosed
  let ef := f.homeomorphOfImageSubsetSource hcsrc hclosure
  let e : ClosedRectangle a b ≃ₜ ClosedRectangle A B := (eF.trans ef).trans eH.symm
  have hRc : OpenRectangle a b ⊆ ClosedRectangle a b := by
    rw [← RectangleModelPreparation.closure_openRectangle ha hb]
    exact subset_closure
  have hR'c : OpenRectangle A B ⊆ ClosedRectangle A B := by
    rw [← RectangleModelPreparation.closure_openRectangle hA hB]
    exact subset_closure
  have hGbij : BijOn G (f '' Q) (OpenRectangle A B) := hHbij.symm ⟨hHG, hGH⟩
  have hfbij : BijOn f Q (f '' Q) := ⟨mapsTo_image f Q, f.injOn.mono hQsrc, surjOn_image _ _⟩
  have hcompbij : BijOn (G ∘ f ∘ F) (OpenRectangle a b) (OpenRectangle A B) :=
    hGbij.comp (hfbij.comp hFbij)
  have he : ∀ z : ClosedRectangle a b, (z : ℂ) ∈ OpenRectangle a b →
      (e z : ℂ) = (G ∘ f ∘ F) z := by
    intro z hz
    have hfz : f (F z) ∈ f '' Q := ⟨F z, hFbij.mapsTo hz, rfl⟩
    have hmid : ef (eF z) = ⟨f (F z), subset_closure hfz⟩ := by
      apply Subtype.ext
      change f (eF z) = f (F z)
      rw [heF z hz]
    change (eH.symm (ef (eF z)) : ℂ) = G (f (F z))
    rw [hmid]
    exact RectangleModelPreparation.closure_inverse_agrees hR'c H G eH heH
      hGm hHG _ hfz
  let W : ℂ → ℂ := Function.extend Subtype.val
    (fun z : ClosedRectangle a b ↦ (e z : ℂ)) (fun _ ↦ 0)
  have hW (z : ℂ) (hz : z ∈ ClosedRectangle a b) : W z = e ⟨z, hz⟩ :=
    Subtype.val_injective.extend_apply _ _ ⟨z, hz⟩
  have hWeq : EqOn W (G ∘ f ∘ F) (OpenRectangle a b) := by
    intro z hz
    exact (hW z (hRc hz)).trans (he ⟨z, hRc hz⟩ hz)
  have hWc : ContinuousOn W (ClosedRectangle a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun z : ClosedRectangle a b ↦ W z)
    have heq : (fun z : ClosedRectangle a b ↦ W z) = (fun z ↦ (e z : ℂ)) :=
      funext fun z ↦ hW z z.property
    rw [heq]
    exact continuous_subtype_val.comp e.continuous
  have hWbij : BijOn W (OpenRectangle a b) (OpenRectangle A B) :=
    hcompbij.congr hWeq.symm
  have hW1 : ContDiffOn ℝ 1 W (OpenRectangle a b) := by
    apply ContDiffOn.congr _ hWeq
    exact ((hG.contDiffOn hQ'open).restrict_scalars ℝ).comp
      (hC1.comp ((hF.contDiffOn hR).restrict_scalars ℝ)
        (fun z hz ↦ hQinside (subset_closure (hFbij.mapsTo hz))))
      (fun z hz ↦ ⟨F z, hFbij.mapsTo hz, rfl⟩)
  have hWd : ∀ z ∈ OpenRectangle a b, ∃ L : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt W (L : ℂ →L[ℝ] ℂ) z ∧ 0 < (L : ℂ →L[ℝ] ℂ).det := by
    intro z hz
    have hfz := hFbij.mapsTo hz
    have hffz : f (F z) ∈ f '' Q := ⟨F z, hfz, rfl⟩
    have hFd := (hF.differentiableAt (hR.mem_nhds hz)).hasDerivAt
    have hGd := (hG.differentiableAt (hQ'open.mem_nhds hffz)).hasDerivAt
    have hFn : deriv F z ≠ 0 := by
      have hi := (hFi.differentiableAt (hQopen.mem_nhds hfz)).hasDerivAt.comp z hFd
      have heq : (Fi ∘ F) =ᶠ[nhds z] id := (hR.eventually_mem hz).mono fun x hx ↦ hFiF x hx
      have he := hi.deriv
      rw [heq.deriv_eq] at he
      intro hn
      simp [hn] at he
    have hGn : deriv G (f (F z)) ≠ 0 := by
      have hi := (hH.differentiableAt (hR'.mem_nhds (hGm hffz))).hasDerivAt.comp
        (f (F z)) hGd
      have heq : (H ∘ G) =ᶠ[nhds (f (F z))] id :=
        (hQ'open.eventually_mem hffz).mono fun x hx ↦ hHG x hx
      have he := hi.deriv
      rw [heq.deriv_eq] at he
      intro hn
      simp [hn] at he
    obtain ⟨L, hL, hLp⟩ := hderiv (F z) (hQinside (subset_closure hfz))
    let P := (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ
    let T := (ContinuousLinearMap.toSpanSingleton ℂ (deriv G (f (F z)))).restrictScalars ℝ
    let D : ℂ →L[ℝ] ℂ := T.comp ((L : ℂ →L[ℝ] ℂ).comp P)
    have hsim (c : ℂ) (hc : c ≠ 0) :
        0 < ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det := by
      rw [qc_real_linear_determinant]
      simpa [Complex.normSq_apply, pow_two] using Complex.normSq_pos.mpr hc
    have hDp : 0 < D.det := by
      change 0 < (T.toLinearMap.comp (L.toLinearMap.comp P.toLinearMap)).det
      rw [LinearMap.det_comp, LinearMap.det_comp]
      exact mul_pos (hsim _ hGn) (mul_pos hLp (hsim _ hFn))
    have hcomp : HasFDerivAt (G ∘ f ∘ F) D z :=
      (hGd.hasFDerivAt.restrictScalars ℝ).comp z
        (hL.comp z (hFd.hasFDerivAt.restrictScalars ℝ))
    have heq : W =ᶠ[nhds z] (G ∘ f ∘ F) :=
      (hR.eventually_mem hz).mono fun x hx ↦ hWeq hx
    refine ⟨D.toContinuousLinearEquivOfDetNeZero hDp.ne', ?_, ?_⟩
    · rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
      exact hcomp.congr_of_eventuallyEq heq
    · simpa only [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hDp
  have hWdist : ∀ z ∈ OpenRectangle a b, ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ W z v‖ ≤ K * ‖fderiv ℝ W z w‖ := by
    intro z hz
    have hfz := hFbij.mapsTo hz
    obtain ⟨L, hL, _⟩ := hderiv (F z) (hQinside (subset_closure hfz))
    have hdist := hDistortion (F z) (hQinside (subset_closure hfz))
    rw [hL.fderiv] at hdist
    have hnear := hR.eventually_mem hz
    have hevent : W =ᶠ[nhds z] (G ∘ f ∘ F) := hnear.mono fun x hx ↦ hWeq hx
    rw [hevent.fderiv_eq]
    exact qc_holomorphic_composition_distortion
      (hF.differentiableAt (hR.mem_nhds hz)).hasDerivAt hL
      (hG.differentiableAt (hQ'open.mem_nhds ⟨F z, hfz, rfl⟩)).hasDerivAt hdist
  refine ⟨a, b, A, B, ha, hb, hA, hB, hm, hm', F, G, W, hF, hFbij,
    hG, hGbij, hWeq, hWc, hW1, hWbij, hWd, hWdist, ?_⟩
  have hcorn : ∀ i : Fin 4,
      (e ⟨RectangleCorner a b i, RectangleModelPreparation.corner_mem ha hb i⟩ : ℂ) =
        RectangleCorner A B i := by
    intro i
    let z : ClosedRectangle a b :=
      ⟨RectangleCorner a b i, RectangleModelPreparation.corner_mem ha hb i⟩
    let w : ClosedRectangle A B :=
      ⟨RectangleCorner A B i, RectangleModelPreparation.corner_mem hA hB i⟩
    have hmid : ef (eF z) = eH w := by
      apply Subtype.ext
      change f (eF z) = eH w
      rw [hpF i z rfl, hpH i w rfl]
    change (eH.symm (ef (eF z)) : ℂ) = RectangleCorner A B i
    rw [hmid, eH.symm_apply_apply]
  have heW : ∀ z : ClosedRectangle a b, (z : ℂ) ∈ OpenRectangle a b →
      (e z : ℂ) = W z := fun z _ ↦ (hW z z.property).symm
  intro y hy
  have hyl : (y : ℂ) * Complex.I ∈ ClosedRectangle a b := by
    simpa [ClosedRectangle, Complex.reProdIm, ha.le] using Ioo_subset_Icc_self hy
  have hyr : (a : ℂ) + (y : ℂ) * Complex.I ∈ ClosedRectangle a b := by
    simpa [ClosedRectangle, Complex.reProdIm, ha.le] using Ioo_subset_Icc_self hy
  have hl := marked_rectangle_open_vertical_side ha hb hA hB W hWbij e heW
    (hcorn 0) (hcorn 1) (hcorn 2) (hcorn 3) 0 0 (Or.inl ⟨rfl, rfl⟩)
    ⟨_, hyl⟩ (by simp) (by simpa using hy)
  have hr := marked_rectangle_open_vertical_side ha hb hA hB W hWbij e heW
    (hcorn 0) (hcorn 1) (hcorn 2) (hcorn 3) a A (Or.inr ⟨rfl, rfl⟩)
    ⟨_, hyr⟩ (by simp) (by simpa using hy)
  have hlW : (W ((y : ℂ) * Complex.I)).re = 0 := by rw [hW _ hyl]; exact hl.1
  have hrW : (W ((a : ℂ) + (y : ℂ) * Complex.I)).re = A := by
    rw [hW _ hyr]; exact hr.1
  calc
    A = |(W ((y : ℂ) * Complex.I) - W ((a : ℂ) + (y : ℂ) * Complex.I)).re| := by
      rw [Complex.sub_re, hlW, hrW]
      simp [abs_of_pos hA]
    _ ≤ ‖W ((y : ℂ) * Complex.I) - W ((a : ℂ) + (y : ℂ) * Complex.I)‖ :=
      Complex.abs_re_le_norm _
    _ = _ := (dist_eq_norm _ _).symm

end HolomorphicAnosov.Analysis

