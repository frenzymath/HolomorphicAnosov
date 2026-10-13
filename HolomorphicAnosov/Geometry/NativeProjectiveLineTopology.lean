import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-! The homogeneous complex projective line is connected, Hausdorff, and compact, and is
homeomorphic to `OnePoint ℂ`. (Ghys, Lemma 5.2 and Thm. A, pp. 599–600; Demailly, V §15.A, p. 277) -/
namespace HolomorphicAnosov.NativeProjectiveTopology
open Set Topology _root_.Topology
noncomputable section
abbrev NonzeroPair := {v : ComplexModel 2 // v ≠ 0}

/-- The space of nonzero homogeneous pairs is connected in its inherited topology. -/
theorem connected_nonzero_pair : ConnectedSpace NonzeroPair := by
  have hr : 1 < Module.rank ℝ (ComplexModel 2) := by
    norm_num [ComplexModel, rank_fun, Complex.rank_real_complex]
  have hc := isConnected_compl_singleton_of_one_lt_rank hr (0 : ComplexModel 2)
  exact isConnected_iff_connectedSpace.mp hc

/-- The homogeneous complex projective line is connected in its quotient topology. -/
theorem connected_native_projective_line : ConnectedSpace ComplexProjectiveLine := by
  let _ := connected_nonzero_pair
  exact Quotient.instConnectedSpace

/-- The homogeneous complex projective line contains at least two distinct points. -/
theorem nontrivial_native_projective_line : Nontrivial ComplexProjectiveLine := by
  exact Equiv.nontrivial (OnePoint.equivProjectivization ℂ).symm

/-- Nonzero homogeneous pairs represent the same projective point exactly when their wedge vanishes. -/
theorem mk_eq_iff_wedge (v w : NonzeroPair) :
    Projectivization.mk ℂ v.val v.property = Projectivization.mk ℂ w.val w.property ↔
      v.val 0 * w.val 1 = v.val 1 * w.val 0 := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    rw [← h0, ← h1]
    ring
  · intro h
    by_cases hw : w.val 1 = 0
    · have hw0 : w.val 0 ≠ 0 := by
        intro h0
        apply w.property
        ext i
        fin_cases i <;> simp_all
      have hv1 : v.val 1 = 0 := by
        have : v.val 1 * w.val 0 = 0 := by simpa [hw] using h.symm
        exact (mul_eq_zero.mp this).resolve_right hw0
      refine ⟨v.val 0 / w.val 0, ?_⟩
      ext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hw, hv1, hw0]
    · refine ⟨v.val 1 / w.val 1, ?_⟩
      ext i
      fin_cases i
      · change v.val 1 / w.val 1 * w.val 0 = v.val 0
        rw [div_mul_eq_mul_div]
        exact (div_eq_iff hw).mpr h.symm
      · simp [Pi.smul_apply, smul_eq_mul, hw]

/-- Scalar multiplication by a complex unit defines a homeomorphism of nonzero homogeneous pairs. -/
def scalePair (a : ℂˣ) : NonzeroPair ≃ₜ NonzeroPair where
  toFun v := ⟨a • v.val, smul_ne_zero a.ne_zero v.property⟩
  invFun v := ⟨a⁻¹ • v.val, smul_ne_zero (a⁻¹).ne_zero v.property⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp
  continuous_toFun := ((continuous_const_smul a).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_const_smul a⁻¹).comp continuous_subtype_val).subtype_mk _

/-- The homogeneous quotient map to the complex projective line is open. -/
theorem quotient_mk_open : IsOpenMap (Projectivization.mk' ℂ : NonzeroPair → ComplexProjectiveLine) := by
  intro U hU
  have hq : IsQuotientMap (Projectivization.mk' ℂ : NonzeroPair → ComplexProjectiveLine) :=
    isQuotientMap_quotient_mk'
  apply hq.isOpen_preimage.mp
  have heq : (Projectivization.mk' ℂ) ⁻¹' ((Projectivization.mk' ℂ) '' U) =
      ⋃ a : ℂˣ, (scalePair a) '' U := by
    ext v
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨w, hw, heq⟩
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ w.property v.property).mp heq
      refine ⟨a⁻¹, w, hw, ?_⟩
      apply Subtype.ext
      change a⁻¹ • w.val = v.val
      rw [← ha]
      simp
    · rintro ⟨a, w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      exact (Projectivization.mk_eq_mk_iff ℂ _ _ w.property (scalePair a w).property).mpr
        ⟨a⁻¹, by simp [scalePair]⟩
  rw [heq]
  exact isOpen_iUnion fun a ↦ (scalePair a).isOpenMap U hU

/-- The homogeneous complex projective line is Hausdorff in its quotient topology. -/
theorem t2_native_projective_line : T2Space ComplexProjectiveLine := by
  have hq : IsOpenQuotientMap (Projectivization.mk' ℂ : NonzeroPair → ComplexProjectiveLine) :=
    .of_isOpenMap_isQuotientMap quotient_mk_open isQuotientMap_quotient_mk'
  apply (t2Space_iff_of_isOpenQuotientMap hq).mpr
  have heq : {q : NonzeroPair × NonzeroPair | Projectivization.mk' ℂ q.1 =
      Projectivization.mk' ℂ q.2} =
      {q | q.1.val 0 * q.2.val 1 = q.1.val 1 * q.2.val 0} := by
    ext q
    exact mk_eq_iff_wedge q.1 q.2
  rw [heq]
  exact isClosed_eq
    (((continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply 1).comp (continuous_subtype_val.comp continuous_snd)))
    (((continuous_apply 1).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd)))

/-- The homogeneous complex projective line is compact in its quotient topology. -/
theorem compact_native_projective_line : CompactSpace ComplexProjectiveLine := by
  let q : ↥(Metric.sphere (0 : ComplexModel 2) 1) → ComplexProjectiveLine := fun v ↦
    Projectivization.mk ℂ v.val (by
      intro h
      have hn : ‖v.val‖ = 1 := by simp
      simp [h] at hn)
  have hq : Continuous q := continuous_quotient_mk'.comp
    (continuous_subtype_val.subtype_mk _)
  have hs : Function.Surjective q := by
    intro p
    let v := p.rep
    have hv : v ≠ 0 := p.rep_nonzero
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let a : ℂ := ((‖v‖ : ℝ) : ℂ)⁻¹
    have ha : a ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne')
    have hunit : a • v ∈ Metric.sphere (0 : ComplexModel 2) 1 := by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, a, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
      exact inv_mul_cancel₀ hn.ne'
    refine ⟨⟨a • v, hunit⟩, ?_⟩
    change Projectivization.mk ℂ (a • v) _ = p
    rw [← Projectivization.mk_rep p]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a, rfl⟩
  exact Function.Surjective.compactSpace hq hs

/-- The affine homogeneous point `[z:1]` associated with `z : ℂ`. -/
def affinePoint (z : ℂ) : ComplexProjectiveLine :=
  Projectivization.mk ℂ ![z, 1] (by simp)
def reciprocalPoint (z : ℂ) : ComplexProjectiveLine :=
  Projectivization.mk ℂ ![1, z] (by simp)

theorem continuous_affinePoint : Continuous affinePoint := by
  have hc : Continuous (fun z : ℂ ↦ (![z, 1] : ComplexModel 2)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  change Continuous ((Projectivization.mk' ℂ) ∘
    (fun z : ℂ ↦ (⟨![z, 1], by simp⟩ : NonzeroPair)))
  exact continuous_quotient_mk'.comp (hc.subtype_mk _)

theorem continuous_reciprocalPoint : Continuous reciprocalPoint := by
  have hc : Continuous (fun z : ℂ ↦ (![1, z] : ComplexModel 2)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  change Continuous ((Projectivization.mk' ℂ) ∘
    (fun z : ℂ ↦ (⟨![1, z], by simp⟩ : NonzeroPair)))
  exact continuous_quotient_mk'.comp (hc.subtype_mk _)

/-- For nonzero `z`, the affine point `[z:1]` equals the reciprocal point `[1:z⁻¹]`. -/
theorem affine_eq_reciprocal_inv {z : ℂ} (hz : z ≠ 0) :
    affinePoint z = reciprocalPoint z⁻¹ := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨z, ?_⟩
  ext i
  fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hz]

/-- The homogeneous equivalence from `OnePoint ℂ` to the complex projective line is continuous. -/
theorem continuous_onePoint_projectivization :
    Continuous (OnePoint.equivProjectivization ℂ : OnePoint ℂ → ComplexProjectiveLine) := by
  apply (OnePoint.continuous_iff _).mpr
  constructor
  · change Filter.Tendsto affinePoint (Filter.coclosedCompact ℂ) (𝓝 (reciprocalPoint 0))
    rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    apply ((continuous_reciprocalPoint.tendsto 0).comp
      (Filter.tendsto_inv₀_cobounded (α := ℂ))).congr'
    filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
    exact (affine_eq_reciprocal_inv hz).symm
  · exact continuous_affinePoint

/-- The homeomorphism from the homogeneous complex projective line to `OnePoint ℂ` whose underlying
equivalence is `(OnePoint.equivProjectivization ℂ).symm`. -/
def nativeProjectiveLineHomeomorphOnePoint : ComplexProjectiveLine ≃ₜ OnePoint ℂ := by
  let _ := t2_native_projective_line
  exact continuous_onePoint_projectivization.homeoOfEquivCompactToT2.symm

end
end HolomorphicAnosov.NativeProjectiveTopology
