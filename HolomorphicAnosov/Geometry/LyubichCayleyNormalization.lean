import HolomorphicAnosov.Geometry.LyubichMarkedTriangleTopology
import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import HolomorphicAnosov.Geometry.LyubichCayleyPositiveOrder
import Mathlib.Analysis.Complex.Norm
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse

namespace HolomorphicAnosov

open Analysis.MarkedRectangle
open scoped ComplexConjugate

/-! The file constructs the normalized Möbius map from a marked ideal triangle to the upper half-plane. (Lyubich, §2.4.13) -/

/-- A Carathéodory extension of a marked ideal-triangle map can be normalized by the Cayley transform at the third marked point and a positive real affine map at the first two points. (Lyubich, §2.4.13, Exercise 2.49(i)) -/
theorem markedIdealDiskTriangle_cayley_normalization
    (T : MarkedIdealDiskTriangle)
    (φ : ℂ → ℂ)
    (Φ : closedUnitDisk ≃ₜ closure T.interiorSet)
    (hφholomorphic : DifferentiableOn ℂ φ Analysis.MarkedRectangle.unitDisk)
    (hφbijective : Set.BijOn φ Analysis.MarkedRectangle.unitDisk T.interiorSet)
    (hΦ : ExtendsDiskMap T.interiorSet φ Φ)
    (hβ : ∃ β : Circle ≃ₜ frontier T.interiorSet,
      (∀ ζ : Circle, (β ζ : ℂ) = (Φ (circleInClosedDisk ζ) : ℂ)) ∧
      PositiveBoundaryParametrization T.interiorSet β) :
    ∃ F : OpenPartialHomeomorph ℂ ℂ,
      F.source = T.interiorSet ∧
      F.target = {w : ℂ | 0 < w.im} ∧
      DifferentiableOn ℂ F F.source ∧
      DifferentiableOn ℂ F.symm F.target ∧
      (∃ b : ℂ → OnePoint ℂ,
        ContinuousOn b T.closedSet ∧
        Set.EqOn b (fun z : ℂ ↦ (F z : OnePoint ℂ)) T.interiorSet ∧
        b (T.vertex 0) = (0 : ℂ) ∧
        b (T.vertex 1) = (1 : ℂ) ∧
        b (T.vertex 2) = OnePoint.infty) := by
  classical
  obtain ⟨β, hβΦ, hβpos⟩ := hβ
  have hclosed (i : Fin 3) : T.vertex i ∈ T.closedSet := by
    refine ⟨(T.norm_vertex i).le, ?_⟩
    have hk : idealDiskKlein (T.vertex i) = T.vertex i := by
      simp [idealDiskKlein, T.norm_vertex i]
      ring
    rw [hk]
    exact subset_convexHull ℝ (Set.range T.vertex) ⟨i, rfl⟩
  have hfront (i : Fin 3) : T.vertex i ∈ frontier T.interiorSet := by
    rw [(markedIdealDiskTriangle_interior_isOpen T).frontier_eq,
      markedIdealDiskTriangle_closure_interior_eq_closedSet T]
    refine ⟨hclosed i, ?_⟩
    intro hi
    have hnorm := hi.1
    rw [T.norm_vertex i] at hnorm
    exact (lt_irrefl 1) hnorm
  let q : Fin 3 → Circle := fun i ↦ β.symm ⟨T.vertex i, hfront i⟩
  have hq (i : Fin 3) : (Φ (circleInClosedDisk (q i)) : ℂ) = T.vertex i := by
    rw [← hβΦ]
    exact congrArg Subtype.val (β.apply_symm_apply ⟨T.vertex i, hfront i⟩)
  have hqinj : Function.Injective q := by
    intro i j hij
    apply T.distinct
    rw [← hq i, ← hq j, hij]
  let C : ℂ → ℂ := fun z ↦ Complex.I *
    (1 + conj (q 2 : ℂ) * z) / (1 - conj (q 2 : ℂ) * z)
  have hCden (z : ℂ) (hz : ‖z‖ < 1) :
      1 - conj (q 2 : ℂ) * z ≠ 0 := by
    intro hzero
    have hnorm : ‖conj (q 2 : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul]
      exact hz
    have hunit : (1 : ℂ) = conj (q 2 : ℂ) * z := sub_eq_zero.mp hzero
    have hunitnorm := congrArg norm hunit
    have hqn : ‖conj (q 2 : ℂ)‖ = 1 := by
      rw [Complex.norm_conj, Circle.norm_coe]
    rw [norm_one, norm_mul, hqn, one_mul] at hunitnorm
    have hz' : ‖z‖ < 1 := by
      simpa [norm_mul, hqn] using hnorm
    rw [← hunitnorm] at hz'
    exact (lt_irrefl 1) hz'
  have hCim (z : ℂ) :
      (C z).im = (1 - ‖z‖ ^ 2) / ‖1 - conj (q 2 : ℂ) * z‖ ^ 2 := by
    have hgeneric (w : ℂ) :
        (Complex.I * (1 + w) / (1 - w)).im =
          (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
      simp only [Complex.div_im, Complex.mul_im, Complex.mul_re,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [show C z = Complex.I * (1 + conj (q 2 : ℂ) * z) /
      (1 - conj (q 2 : ℂ) * z) by rfl, hgeneric]
    rw [norm_mul, Complex.norm_conj, Circle.norm_coe, one_mul]
  have hCim_pos (z : ℂ) (hz : ‖z‖ < 1) : 0 < (C z).im := by
    rw [hCim z]
    have hn : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    exact div_pos hn (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (hCden z hz)))
  let N : ℂ → ℂ := fun w ↦ (q 2 : ℂ) * (w - Complex.I) / (w + Complex.I)
  have hNden (w : ℂ) (hw : 0 < w.im) : w + Complex.I ≠ 0 := by
    intro hzero
    have hi := congrArg Complex.im hzero
    simp at hi
    linarith
  have hNC (z : ℂ) (hz : ‖z‖ < 1) : N (C z) = z := by
    have hw := hNden (C z) (hCim_pos z hz)
    have hqmul : (q 2 : ℂ) * conj (q 2 : ℂ) = 1 := by
      rw [Complex.mul_conj]
      rw [← Complex.sq_norm, Circle.norm_coe]
      norm_num
    dsimp [N, C]
    field_simp [hCden z hz, hw]
    ring_nf
    rw [hqmul]
    ring
  have hAffineIm (a b : ℝ) (hab : a < b) (w : ℂ) (hw : 0 < w.im) :
      0 < ((w - (a : ℂ)) / (b - a)).im := by
    rw [Complex.div_im]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero]
    have hba : 0 < b - a := sub_pos.mpr hab
    have hsq : 0 < (b - a) ^ 2 := sq_pos_of_pos hba
    have hnorm : Complex.normSq ((b : ℂ) - (a : ℂ)) = (b - a) ^ 2 := by
      rw [Complex.normSq_apply]
      norm_num
      ring
    rw [hnorm]
    simpa using (div_pos (mul_pos hw hba) hsq)
  obtain ⟨a, b, hab, hC0, hC1⟩ :=
    markedIdealDiskTriangle_cayley_positive_order T Φ β hβΦ hβpos q hq
  have hqmul : (q 2 : ℂ) * conj (q 2 : ℂ) = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, Circle.norm_coe]
    norm_num
  have hNmap (w : ℂ) (hw : 0 < w.im) : ‖N w‖ < 1 := by
    have hlt : ‖w - Complex.I‖ < ‖w + Complex.I‖ := by
      rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.I_re, Complex.I_im]
      nlinarith
    dsimp [N]
    rw [norm_div, norm_mul, Circle.norm_coe, one_mul]
    exact (div_lt_one (norm_pos_iff.mpr (hNden w hw))).mpr hlt
  have hCN (w : ℂ) (hw : 0 < w.im) : C (N w) = w := by
    have hrot : conj (q 2 : ℂ) * N w = (w - Complex.I) / (w + Complex.I) := by
      dsimp [N]
      rw [← mul_div_assoc, ← mul_assoc, mul_comm (conj (q 2 : ℂ)), hqmul, one_mul]
    change Complex.I * (1 + conj (q 2 : ℂ) * N w) / (1 - conj (q 2 : ℂ) * N w) = w
    rw [hrot]
    field_simp [hNden w hw]
    ring_nf
  have hCd : DifferentiableOn ℂ C unitDisk := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    dsimp [C]
    fun_prop (disch := exact hCden z hz)
  have hNd : DifferentiableOn ℂ N {w : ℂ | 0 < w.im} := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    dsimp [N]
    fun_prop (disch := exact hNden w hw)
  have hba : (b : ℂ) - a ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hab.ne'
  let G : ℂ → ℂ := fun z ↦ (C z - a) / ((b : ℂ) - a)
  let J : ℂ → ℂ := fun w ↦ N (((b : ℂ) - a) * w + a)
  have hA (w : ℂ) (hw : 0 < w.im) : 0 < (((b : ℂ) - a) * w + a).im := by
    simpa using mul_pos (sub_pos.mpr hab) hw
  have hGmap : Set.MapsTo G unitDisk {w : ℂ | 0 < w.im} := by
    intro z hz
    exact hAffineIm a b hab (C z) (hCim_pos z hz)
  have hJmap : Set.MapsTo J {w : ℂ | 0 < w.im} unitDisk := by
    intro w hw
    exact hNmap _ (hA w hw)
  have hJG (z : ℂ) (hz : z ∈ unitDisk) : J (G z) = z := by
    dsimp [G, J]
    rw [mul_div_cancel₀ _ hba, sub_add_cancel]
    exact hNC z hz
  have hGJ (w : ℂ) (hw : 0 < w.im) : G (J w) = w := by
    dsimp [G, J]
    rw [hCN _ (hA w hw)]
    field_simp
    ring
  have hGd : DifferentiableOn ℂ G unitDisk :=
    (hCd.sub_const _).div_const _
  have hJd : DifferentiableOn ℂ J {w : ℂ | 0 < w.im} :=
    hNd.comp ((differentiableOn_id.const_mul _).add_const _) hA
  let ψ : ℂ → ℂ := fun z ↦ if hz : z ∈ closure T.interiorSet then
    (Φ.symm ⟨z, hz⟩ : ℂ) else 0
  have hψ (z : ℂ) (hz : z ∈ closure T.interiorSet) :
      ψ z = (Φ.symm ⟨z, hz⟩ : ℂ) := dite_eq_left hz
  have hψcont : ContinuousOn ψ (closure T.interiorSet) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun z : closure T.interiorSet ↦ ψ z)
    have : (fun z : closure T.interiorSet ↦ ψ z) =
        fun z ↦ (Φ.symm z : ℂ) := by
      funext z
      exact hψ z z.property
    rw [this]
    exact continuous_subtype_val.comp Φ.symm.continuous
  have hψφ (z : ℂ) (hz : z ∈ unitDisk) : ψ (φ z) = z := by
    have hp := hφbijective.mapsTo hz
    rw [hψ _ (subset_closure hp)]
    have he : (⟨φ z, subset_closure hp⟩ : closure T.interiorSet) =
        Φ ⟨z, show ‖z‖ ≤ 1 from le_of_lt hz⟩ := Subtype.ext (hΦ z hz).symm
    rw [he, Φ.symm_apply_apply]
  have hψmap : Set.MapsTo ψ T.interiorSet unitDisk := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hφbijective.surjOn hz
    rw [hψφ _ hu]
    exact hu
  have hφψ (z : ℂ) (hz : z ∈ T.interiorSet) : φ (ψ z) = z := by
    obtain ⟨u, hu, rfl⟩ := hφbijective.surjOn hz
    rw [hψφ _ hu]
  let H : OpenPartialHomeomorph ℂ ℂ := {
    toFun := φ ∘ J
    invFun := G ∘ ψ
    source := {w : ℂ | 0 < w.im}
    target := T.interiorSet
    map_source' := fun w hw ↦ hφbijective.mapsTo (hJmap hw)
    map_target' := fun z hz ↦ hGmap (hψmap hz)
    left_inv' := by
      intro w hw
      change G (ψ (φ (J w))) = w
      rw [hψφ _ (hJmap hw), hGJ w hw]
    right_inv' := by
      intro z hz
      change φ (J (G (ψ z))) = z
      rw [hJG _ (hψmap hz), hφψ z hz]
    open_source := isOpen_lt continuous_const Complex.continuous_im
    open_target := markedIdealDiskTriangle_interior_isOpen T
    continuousOn_toFun := (hφholomorphic.comp hJd hJmap).continuousOn
    continuousOn_invFun := hGd.continuousOn.comp (hψcont.mono subset_closure) hψmap }
  have hHd : DifferentiableOn ℂ H H.source := hφholomorphic.comp hJd hJmap
  refine ⟨H.symm, rfl, rfl, ?_, hHd, ?_⟩
  · intro z hz
    exact (Analysis.Complex.coordinateInverseDeriv H hHd hz).2.differentiableAt.differentiableWithinAt
  · let d : ℂ → ℂ := fun z ↦ ((b : ℂ) - a) * (1 - conj (q 2 : ℂ) * z)
    let n : ℂ → ℂ := fun z ↦ Complex.I * (1 + conj (q 2 : ℂ) * z) -
      a * (1 - conj (q 2 : ℂ) * z)
    have hpair (z : ℂ) : (![n z, d z] : Fin 2 → ℂ) ≠ 0 := by
      intro he
      have hd : d z = 0 := congrFun he 1
      have hn : n z = 0 := congrFun he 0
      have hden : 1 - conj (q 2 : ℂ) * z = 0 := (mul_eq_zero.mp hd).resolve_left hba
      have hmul : conj (q 2 : ℂ) * z = 1 := (sub_eq_zero.mp hden).symm
      simp [n, hmul, Complex.I_ne_zero] at hn
    let e := NativeProjectiveTopology.nativeProjectiveLineHomeomorphOnePoint
    let B : ℂ → OnePoint ℂ := fun z ↦ e (Projectivization.mk ℂ ![n z, d z] (hpair z))
    have hBcont : Continuous B := by
      have hn : Continuous n := by dsimp [n]; fun_prop
      have hd : Continuous d := by dsimp [d]; fun_prop
      have hv : Continuous (fun z : ℂ ↦ (![n z, d z] : Fin 2 → ℂ)) := by
        apply continuous_pi
        intro i
        fin_cases i <;> simpa using (show Continuous _ from by first | exact hn | exact hd)
      exact e.continuous.comp (continuous_quotient_mk'.comp (hv.subtype_mk hpair))
    have hBfinite (z : ℂ) (hz : 1 - conj (q 2 : ℂ) * z ≠ 0) :
        B z = (G z : OnePoint ℂ) := by
      change (OnePoint.equivProjectivization ℂ).symm
        (Projectivization.mk ℂ ![n z, d z] (hpair z)) = _
      rw [OnePoint.equivProjectivization_symm_apply_mk]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, d,
        mul_ne_zero hba hz, ite_false]
      congr 1
      dsimp [G, C, n, d]
      field_simp
    have hBpole : B (q 2 : ℂ) = OnePoint.infty := by
      change (OnePoint.equivProjectivization ℂ).symm
        (Projectivization.mk ℂ _ _) = _
      rw [OnePoint.equivProjectivization_symm_apply_mk]
      simp [d, mul_comm (conj (q 2 : ℂ)), hqmul]
    have hqden (i : Fin 3) (hi : i ≠ 2) : 1 - conj (q 2 : ℂ) * (q i : ℂ) ≠ 0 := by
      intro hh
      have he : conj (q 2 : ℂ) * (q i : ℂ) = 1 := (sub_eq_zero.mp hh).symm
      have : (q i : ℂ) = (q 2 : ℂ) := by
        calc
          (q i : ℂ) = ((q 2 : ℂ) * conj (q 2 : ℂ)) * q i := by rw [hqmul, one_mul]
          _ = q 2 := by rw [mul_assoc, he, mul_one]
      exact hi (hqinj (Subtype.ext this))
    have hψvertex (i : Fin 3) : ψ (T.vertex i) = (q i : ℂ) := by
      have hv : T.vertex i ∈ closure T.interiorSet := by
        rw [markedIdealDiskTriangle_closure_interior_eq_closedSet T]
        exact hclosed i
      rw [hψ _ hv]
      have he : (⟨T.vertex i, hv⟩ : closure T.interiorSet) =
          Φ (circleInClosedDisk (q i)) := Subtype.ext (hq i).symm
      rw [he, Φ.symm_apply_apply]
      rfl
    refine ⟨B ∘ ψ, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← markedIdealDiskTriangle_closure_interior_eq_closedSet T]
      exact hBcont.comp_continuousOn hψcont
    · intro z hz
      exact hBfinite _ (hCden _ (hψmap hz))
    · change B (ψ (T.vertex 0)) = _
      rw [hψvertex, hBfinite _ (hqden 0 (by decide))]
      have hc : C (q 0 : ℂ) = (a : ℂ) := hC0
      simp [G, hc]
    · change B (ψ (T.vertex 1)) = _
      rw [hψvertex, hBfinite _ (hqden 1 (by decide))]
      have hc : C (q 1 : ℂ) = (b : ℂ) := hC1
      simp [G, hc, hba]
    · change B (ψ (T.vertex 2)) = _
      rw [hψvertex, hBpole]

end HolomorphicAnosov

