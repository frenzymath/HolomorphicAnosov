import HolomorphicAnosov.Geometry.LyubichReflectionLocalChartsG11
import HolomorphicAnosov.Geometry.LyubichMarkedTriangleTopologyProviders
import HolomorphicAnosov.Geometry.MobiusGroupContinuousG9
import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import Mathlib.Analysis.Complex.Norm

noncomputable section

/-! The normalized triangle sphere boundary map. (Lyubich, §2.4.4 and §2.4.13) -/

namespace HolomorphicAnosov
open scoped Matrix
open Complex

/-- An invertible complex matrix acts by a sphere homeomorphism. -/
def complexMatrixSphereHomeomorph (m : GL (Fin 2) ℂ) : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  let g : Ghys.MobiusGroup := ⟨MulAction.toPerm m, ⟨m, rfl⟩⟩
  { toEquiv := g.val
    continuous_toFun := mobiusGroup_continuous_apply g
    continuous_invFun := mobiusGroup_continuous_apply g⁻¹ }

/-- The disk-to-half-plane fractional-linear formula, totalized on ℂ. -/
def diskCayley (z : ℂ) : ℂ := I * (1 + z) / (1 - z)

/-- Its half-plane-to-disk inverse, totalized on ℂ. -/
def halfPlaneCayley (w : ℂ) : ℂ := (w - I) / (w + I)

/-- The Cayley transform including its sphere pole. -/
def diskCayleySphere : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  complexMatrixSphereHomeomorph (Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![I, I; -1, 1] (by norm_num [Matrix.det_fin_two]))

/-- Away from its pole the matrix action is the usual Cayley quotient. -/
theorem diskCayleySphere_coe {z : ℂ} (hz : z ≠ 1) :
    diskCayleySphere (z : OnePoint ℂ) = (diskCayley z : OnePoint ℂ) := by
  change (Matrix.GeneralLinearGroup.mkOfDetNeZero !![I, I; -1, 1] _) •
    (z : OnePoint ℂ) = _
  rw [OnePoint.smul_some_eq_ite]
  have hd : -z + 1 ≠ 0 := by intro h; apply hz; linear_combination -h
  simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  change (if -1 * z + 1 = 0 then OnePoint.infty else
    (((I * z + I) / (-1 * z + 1) : ℂ) : OnePoint ℂ)) = _
  simp only [neg_one_mul, ite_eq_right hd]
  congr 1
  dsimp [diskCayley]
  congr 1 <;> ring

/-- The ideal pole one is sent to sphere infinity. -/
theorem diskCayleySphere_one : diskCayleySphere ((1 : ℂ) : OnePoint ℂ) = OnePoint.infty := by
  change (Matrix.GeneralLinearGroup.mkOfDetNeZero !![I, I; -1, 1] _) •
    ((1 : ℂ) : OnePoint ℂ) = _
  rw [OnePoint.smul_some_eq_ite]
  norm_num

/-- The imaginary part of the Cayley transform determines the disk's image half-plane. -/
theorem diskCayley_im (z : ℂ) :
    (diskCayley z).im = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
  simp only [diskCayley, Complex.div_im, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- The disk Cayley denominator has no zero in the open unit disk. -/
theorem diskCayley_denominator_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have heq : z = 1 := (sub_eq_zero.mp h).symm
  simp [heq] at hz

/-- The Cayley transform maps the open disk to the open upper half-plane. -/
theorem diskCayley_im_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (diskCayley z).im := by
  rw [diskCayley_im]
  have hn : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  exact div_pos hn (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
    (diskCayley_denominator_ne_zero hz)))

/-- The inverse Cayley denominator has no zero on the closed upper half-plane. -/
theorem halfPlaneCayley_denominator_ne_zero {w : ℂ} (hw : 0 ≤ w.im) : w + I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
  linarith

/-- The inverse Cayley map sends the upper half-plane into the open disk, since the squared denominator norm exceeds the numerator norm by 4 Im w. -/
theorem halfPlaneCayley_norm_lt_one {w : ℂ} (hw : 0 < w.im) :
    ‖halfPlaneCayley w‖ < 1 := by
  have hden : 0 < ‖w + I‖ := norm_pos_iff.mpr (halfPlaneCayley_denominator_ne_zero hw.le)
  rw [halfPlaneCayley, norm_div, div_lt_one hden]
  have hsq : ‖w - I‖ ^ 2 < ‖w + I‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
    nlinarith
  nlinarith [norm_nonneg (w - I)]

/-- The inverse Cayley quotient cancels the disk Cayley quotient. -/
theorem halfPlaneCayley_diskCayley {z : ℂ} (hz : ‖z‖ < 1) :
    halfPlaneCayley (diskCayley z) = z := by
  have hd := diskCayley_denominator_ne_zero hz
  have he := halfPlaneCayley_denominator_ne_zero (diskCayley_im_pos hz).le
  dsimp [halfPlaneCayley, diskCayley] at *
  field_simp
  ring

/-- The disk Cayley quotient cancels its half-plane inverse. -/
theorem diskCayley_halfPlaneCayley {w : ℂ} (hw : 0 < w.im) :
    diskCayley (halfPlaneCayley w) = w := by
  have hd := halfPlaneCayley_denominator_ne_zero hw.le
  have he := diskCayley_denominator_ne_zero (halfPlaneCayley_norm_lt_one hw)
  dsimp [halfPlaneCayley, diskCayley] at *
  field_simp
  ring

/-- The Cayley quotient is holomorphic on the open disk by the quotient rule. -/
theorem diskCayley_differentiableOn :
    DifferentiableOn ℂ diskCayley {z : ℂ | ‖z‖ < 1} := by
  intro z hz
  exact (((differentiableAt_const I).mul
    ((differentiableAt_const 1).add differentiableAt_id)).div
    ((differentiableAt_const 1).sub differentiableAt_id)
    (diskCayley_denominator_ne_zero hz)).differentiableWithinAt

/-- The inverse Cayley quotient is holomorphic on the open upper half-plane. -/
theorem halfPlaneCayley_differentiableOn :
    DifferentiableOn ℂ halfPlaneCayley {w : ℂ | 0 < w.im} := by
  intro w hw
  exact ((differentiableAt_id.sub (differentiableAt_const I)).div
    (differentiableAt_id.add (differentiableAt_const I))
    (halfPlaneCayley_denominator_ne_zero hw.le)).differentiableWithinAt

/-- The explicit disk/upper-half-plane Cayley biholomorphism as a partial homeomorphism of ℂ. -/
def diskCayleyPartial : OpenPartialHomeomorph ℂ ℂ where
  toFun := diskCayley
  invFun := halfPlaneCayley
  source := {z : ℂ | ‖z‖ < 1}
  target := {w : ℂ | 0 < w.im}
  map_source' _ hz := diskCayley_im_pos hz
  map_target' _ hw := halfPlaneCayley_norm_lt_one hw
  left_inv' _ hz := halfPlaneCayley_diskCayley hz
  right_inv' _ hw := diskCayley_halfPlaneCayley hw
  open_source := isOpen_lt continuous_norm continuous_const
  open_target := isOpen_lt continuous_const Complex.continuous_im
  continuousOn_toFun := diskCayley_differentiableOn.continuousOn
  continuousOn_invFun := halfPlaneCayley_differentiableOn.continuousOn

/-- The inverse Cayley map takes the closed upper half-plane into the closed disk, by comparing numerator and denominator squared norms. -/
theorem halfPlaneCayley_norm_le_one {w : ℂ} (hw : 0 ≤ w.im) :
    ‖halfPlaneCayley w‖ ≤ 1 := by
  have hden : 0 < ‖w + I‖ := norm_pos_iff.mpr (halfPlaneCayley_denominator_ne_zero hw)
  rw [halfPlaneCayley, norm_div, div_le_one hden]
  have hsq : ‖w - I‖ ^ 2 ≤ ‖w + I‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
    nlinarith
  nlinarith [norm_nonneg (w - I)]

/-- No finite closed-half-plane value maps to the Cayley pole one. -/
theorem halfPlaneCayley_ne_one {w : ℂ} (hw : 0 ≤ w.im) :
    halfPlaneCayley w ≠ 1 := by
  intro he
  have hh : w - I = w + I := (div_eq_one_iff_eq
    (halfPlaneCayley_denominator_ne_zero hw)).mp he
  have hi := congrArg Complex.im hh
  simp only [Complex.sub_im, Complex.add_im, Complex.I_im] at hi
  linarith

/-- The sphere Cayley map recovers every finite point of the closed upper half-plane from its inverse Cayley image in the closed disk. -/
theorem diskCayleySphere_halfPlaneCayley {w : ℂ} (hw : 0 ≤ w.im) :
    diskCayleySphere (halfPlaneCayley w : OnePoint ℂ) = (w : OnePoint ℂ) := by
  rw [diskCayleySphere_coe (halfPlaneCayley_ne_one hw)]
  congr 1
  have hd := halfPlaneCayley_denominator_ne_zero hw
  have he : 1 - halfPlaneCayley w ≠ 0 := sub_ne_zero.mpr (halfPlaneCayley_ne_one hw).symm
  dsimp [diskCayley, halfPlaneCayley] at *
  field_simp
  ring

/-- Every continuous sphere extension of a biholomorphic half-plane chart on a bounded simply connected Jordan domain agrees with the sphere Cayley map after a closed-disk homeomorphic parametrization of the domain closure. -/
theorem halfPlaneChart_sphere_extension_model
    (F : OpenPartialHomeomorph ℂ ℂ)
    (hFtarget : F.target = {w : ℂ | 0 < w.im})
    (hFne : F.source.Nonempty) (hFbounded : Bornology.IsBounded F.source)
    (hFsimply : IsSimplyConnected F.source)
    (hFjordan : Analysis.MarkedRectangle.HasJordanBoundary F.source)
    (hFi : DifferentiableOn ℂ F.symm F.target)
    (b : ℂ → OnePoint ℂ) (hb : ContinuousOn b (closure F.source))
    (hbeq : Set.EqOn b (fun z ↦ (F z : OnePoint ℂ)) F.source) :
    ∃ Φ : Analysis.MarkedRectangle.closedUnitDisk ≃ₜ closure F.source,
      ∀ z, b (Φ z) = diskCayleySphere (z.val : OnePoint ℂ) := by
  let φ : ℂ → ℂ := F.symm ∘ diskCayley
  have hcmap : Set.MapsTo diskCayley Analysis.MarkedRectangle.unitDisk F.target := by
    intro z hz
    rw [hFtarget]
    exact diskCayley_im_pos hz
  have hφhol : DifferentiableOn ℂ φ Analysis.MarkedRectangle.unitDisk :=
    hFi.comp diskCayley_differentiableOn hcmap
  have hφbij : Set.BijOn φ Analysis.MarkedRectangle.unitDisk F.source := by
    have hFiBij : Set.BijOn F.symm {w : ℂ | 0 < w.im} F.source := by
      simpa only [hFtarget, OpenPartialHomeomorph.symm_source,
        OpenPartialHomeomorph.symm_target] using F.symm.bijOn
    exact hFiBij.comp diskCayleyPartial.bijOn
  obtain ⟨Φ, hΦ, _, _, _⟩ := Analysis.MarkedRectangle.caratheodory_same_map
    F.source hFne F.open_source hFbounded hFsimply hFjordan φ hφhol hφbij
  let G : Analysis.MarkedRectangle.closedUnitDisk → OnePoint ℂ := fun z ↦ b (Φ z)
  let H : Analysis.MarkedRectangle.closedUnitDisk → OnePoint ℂ :=
    fun z ↦ diskCayleySphere (z.val : OnePoint ℂ)
  have hG : Continuous G := by
    have hb' : Continuous (fun z : closure F.source ↦ b z.val) :=
      continuousOn_iff_continuous_domRestrict.mp hb
    exact hb'.comp Φ.continuous
  have hH : Continuous H := diskCayleySphere.continuous.comp
    (OnePoint.continuous_coe.comp continuous_subtype_val)
  have hdense : Dense {z : Analysis.MarkedRectangle.closedUnitDisk | ‖z.val‖ < 1} := by
    intro z
    rw [_root_.Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change z.val ∈ closure (Subtype.val ''
      {z : Analysis.MarkedRectangle.closedUnitDisk | ‖z.val‖ < 1})
    have himg : Subtype.val '' {z : Analysis.MarkedRectangle.closedUnitDisk | ‖z.val‖ < 1} =
        Metric.ball (0 : ℂ) 1 := by
      ext w
      simp only [Set.mem_image, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hw
        exact ⟨⟨w, hw.le⟩, hw, rfl⟩
    rw [himg, closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (show ‖z.val‖ ≤ 1 from z.property)
  have hGH : G = H := hG.ext_on hdense hH (by
    intro z hz
    have hz' : z.val ∈ Analysis.MarkedRectangle.unitDisk := hz
    have hφz : (Φ z : ℂ) = φ z.val := hΦ z.val hz'
    change b (Φ z) = diskCayleySphere (z.val : OnePoint ℂ)
    rw [hφz, hbeq (hφbij.mapsTo hz')]
    change (F (F.symm (diskCayley z.val)) : OnePoint ℂ) = _
    rw [F.right_inv (hcmap hz')]
    exact (diskCayleySphere_coe (by
      intro heq
      have hn : ‖z.val‖ < 1 := hz
      simp [heq] at hn)).symm)
  exact ⟨Φ, congrFun hGH⟩

/-- The sphere extension is injective because the closed-disk model identifies it with the restriction of a sphere homeomorphism. (Carathéodory; Lyubich, §2.4.13) -/
theorem halfPlaneChart_sphere_extension_injOn
    (F : OpenPartialHomeomorph ℂ ℂ)
    (hFtarget : F.target = {w : ℂ | 0 < w.im})
    (hFne : F.source.Nonempty) (hFbounded : Bornology.IsBounded F.source)
    (hFsimply : IsSimplyConnected F.source)
    (hFjordan : Analysis.MarkedRectangle.HasJordanBoundary F.source)
    (hFi : DifferentiableOn ℂ F.symm F.target)
    (b : ℂ → OnePoint ℂ) (hb : ContinuousOn b (closure F.source))
    (hbeq : Set.EqOn b (fun z ↦ (F z : OnePoint ℂ)) F.source) :
    Set.InjOn b (closure F.source) := by
  obtain ⟨Φ, hΦ⟩ := halfPlaneChart_sphere_extension_model F hFtarget hFne hFbounded
    hFsimply hFjordan hFi b hb hbeq
  intro x hx y hy hxy
  let zx := Φ.symm ⟨x, hx⟩
  let zy := Φ.symm ⟨y, hy⟩
  have hΦx : (Φ zx : ℂ) = x := congrArg Subtype.val (Φ.apply_symm_apply ⟨x, hx⟩)
  have hΦy : (Φ zy : ℂ) = y := congrArg Subtype.val (Φ.apply_symm_apply ⟨y, hy⟩)
  have hGHx := hΦ zx
  have hGHy := hΦ zy
  change b (Φ zx) = diskCayleySphere (zx.val : OnePoint ℂ) at hGHx
  change b (Φ zy) = diskCayleySphere (zy.val : OnePoint ℂ) at hGHy
  rw [hΦx] at hGHx
  rw [hΦy] at hGHy
  have hzxy : zx = zy := Subtype.ext (OnePoint.coe_injective
    (diskCayleySphere.injective (hGHx.symm.trans (hxy.trans hGHy))))
  exact hΦx.symm.trans ((congrArg (fun t ↦ (Φ t : ℂ)) hzxy).trans hΦy)

/-- The sphere extension embeds the complete domain closure. -/
theorem halfPlaneChart_sphere_extension_isEmbedding
    (F : OpenPartialHomeomorph ℂ ℂ)
    (hFtarget : F.target = {w : ℂ | 0 < w.im})
    (hFne : F.source.Nonempty) (hFbounded : Bornology.IsBounded F.source)
    (hFsimply : IsSimplyConnected F.source)
    (hFjordan : Analysis.MarkedRectangle.HasJordanBoundary F.source)
    (hFi : DifferentiableOn ℂ F.symm F.target)
    (b : ℂ → OnePoint ℂ) (hb : ContinuousOn b (closure F.source))
    (hbeq : Set.EqOn b (fun z ↦ (F z : OnePoint ℂ)) F.source) :
    _root_.Topology.IsEmbedding (fun z : closure F.source ↦ b z.val) := by
  obtain ⟨Φ, hΦ⟩ := halfPlaneChart_sphere_extension_model F hFtarget hFne hFbounded
    hFsimply hFjordan hFi b hb hbeq
  apply Φ.isEmbedding_comp_iff.mp
  have he : (fun z : closure F.source ↦ b z.val) ∘ Φ =
      diskCayleySphere ∘ (fun z : Analysis.MarkedRectangle.closedUnitDisk ↦
        (z.val : OnePoint ℂ)) := funext hΦ
  rw [he]
  exact diskCayleySphere.isEmbedding.comp
    (OnePoint.isOpenEmbedding_coe.isEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal)

/-- Every finite value in the closed upper half-plane is attained by the sphere extension on the domain closure. -/
theorem halfPlaneChart_sphere_extension_surjOn
    (F : OpenPartialHomeomorph ℂ ℂ)
    (hFtarget : F.target = {w : ℂ | 0 < w.im})
    (hFne : F.source.Nonempty) (hFbounded : Bornology.IsBounded F.source)
    (hFsimply : IsSimplyConnected F.source)
    (hFjordan : Analysis.MarkedRectangle.HasJordanBoundary F.source)
    (hFi : DifferentiableOn ℂ F.symm F.target)
    (b : ℂ → OnePoint ℂ) (hb : ContinuousOn b (closure F.source))
    (hbeq : Set.EqOn b (fun z ↦ (F z : OnePoint ℂ)) F.source)
    {w : ℂ} (hw : 0 ≤ w.im) :
    ∃ z ∈ closure F.source, b z = (w : OnePoint ℂ) := by
  obtain ⟨Φ, hΦ⟩ := halfPlaneChart_sphere_extension_model F hFtarget hFne hFbounded
    hFsimply hFjordan hFi b hb hbeq
  let q : Analysis.MarkedRectangle.closedUnitDisk :=
    ⟨halfPlaneCayley w, halfPlaneCayley_norm_le_one hw⟩
  exact ⟨Φ q, (Φ q).property, (hΦ q).trans (diskCayleySphere_halfPlaneCayley hw)⟩

end HolomorphicAnosov

namespace HolomorphicAnosov
/-- A real value different from the two punctures has its unique preimage on an open triangle side, provided the continuous sphere boundary map is injective and covers the closed upper half-plane. -/
theorem MarkedIdealDiskTriangle.real_value_preimage_on_side
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet) (hFt : F.target = {w : ℂ | 0 < w.im})
    (b : ℂ → OnePoint ℂ) (hbinj : Set.InjOn b T.closedSet)
    (hbeq : Set.EqOn b (fun z ↦ (F z : OnePoint ℂ)) T.interiorSet)
    (hb0 : b (T.vertex 0) = ((0 : ℂ) : OnePoint ℂ))
    (hb1 : b (T.vertex 1) = ((1 : ℂ) : OnePoint ℂ))
    (hb2 : b (T.vertex 2) = OnePoint.infty)
    (hsurj : ∀ w : ℂ, 0 ≤ w.im → ∃ z ∈ T.closedSet, b z = (w : OnePoint ℂ))
    {w : ℂ} (hw : w.im = 0) (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    ∃ z : ℂ, (∃ i j : Fin 3, i ≠ j ∧ z ∈ T.openSide i j) ∧
      b z = (w : OnePoint ℂ) ∧ ∀ y ∈ T.closedSet, b y = (w : OnePoint ℂ) → y = z := by
  obtain ⟨z, hzc, hzw⟩ := hsurj w hw.ge
  have hzn : ‖z‖ < 1 := by
    refine lt_of_le_of_ne hzc.1 ?_
    intro he
    obtain ⟨i, rfl⟩ := (T.closedSet_unit_norm_iff hzc).mp he
    fin_cases i
    · exact hw0 (OnePoint.coe_injective (hzw.symm.trans hb0))
    · exact hw1 (OnePoint.coe_injective (hzw.symm.trans hb1))
    · exact OnePoint.coe_ne_infty w (hzw.symm.trans hb2)
  have hznot : z ∉ T.interiorSet := by
    intro hzi
    have hfzw : F z = w := OnePoint.coe_injective ((hbeq hzi).symm.trans hzw)
    have hpos := F.map_source (hFs.symm ▸ hzi)
    rw [hFt] at hpos
    change 0 < (F z).im at hpos
    simp only [hfzw, hw, lt_self_iff_false] at hpos
  refine ⟨z, ?_, hzw, fun y hy he ↦ hbinj hy hzc (he.trans hzw.symm)⟩
  exact (T.closedSet_disk_partition hzc hzn).resolve_left hznot

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set

/-- The given sphere extension of the normalized triangle chart is injective and attains every finite closed-half-plane value. -/
theorem MarkedIdealDiskTriangle.boundary_chart_model
    (T : MarkedIdealDiskTriangle) (F : OpenPartialHomeomorph ℂ ℂ)
    (hFs : F.source = T.interiorSet) (hFt : F.target = {w : ℂ | 0 < w.im})
    (hFi : DifferentiableOn ℂ F.symm F.target)
    (b : ℂ → OnePoint ℂ) (hb : ContinuousOn b T.closedSet)
    (hbeq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) T.interiorSet) :
    InjOn b T.closedSet ∧
      ∀ w : ℂ, 0 ≤ w.im → ∃ z ∈ T.closedSet, b z = (w : OnePoint ℂ) := by
  have hcl : closure F.source = T.closedSet := by
    rw [hFs, markedIdealDiskTriangle_closure_interior_eq_closedSet]
  have hne : F.source.Nonempty := hFs.symm ▸ markedIdealDiskTriangle_interior_nonempty T
  have hbounded : Bornology.IsBounded F.source :=
    hFs.symm ▸ markedIdealDiskTriangle_interior_isBounded T
  have hsc : IsSimplyConnected F.source :=
    hFs.symm ▸ markedIdealDiskTriangle_interior_isSimplyConnected T
  have hj : Analysis.MarkedRectangle.HasJordanBoundary F.source :=
    hFs.symm ▸ markedIdealDiskTriangle_interior_hasJordanBoundary T
  have hbc : ContinuousOn b (closure F.source) := hcl.symm ▸ hb
  have heq : EqOn b (fun z ↦ (F z : OnePoint ℂ)) F.source := hFs.symm ▸ hbeq
  constructor
  · simpa only [hcl] using halfPlaneChart_sphere_extension_injOn F hFt hne hbounded hsc hj hFi b hbc heq
  · intro w hw
    simpa only [hcl] using halfPlaneChart_sphere_extension_surjOn F hFt hne hbounded hsc hj hFi b hbc heq hw

end HolomorphicAnosov
