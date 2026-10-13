import HolomorphicAnosov.Topology.GallierXuSurfacePresentation
import HolomorphicAnosov.Topology.DiskPrescribedBoundaryExtension
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Rectangle disk chart with six prescribed sides

Source: Gallier–Xu, Proposition 3.2, p.31 and Note F.4, p.167.
DAG: `topo.cairns_six_side_rectangle_chart_g1`.
The explicit affine loop parametrizes the rectangle frontier. The convex-body
disk chart is corrected by the prescribed-boundary extension theorem.
-/

noncomputable section
open Set Metric
namespace HolomorphicAnosov.Topology.GallierXu

def sixSideRectangleLoop (t : ℝ) : ℂ :=
  if t ≤ 1 then ((3 : ℂ) - t) / 2 * Complex.I
  else if t ≤ 2 then (t - 1 : ℂ) + Complex.I
  else if t ≤ 4 then (1 : ℂ) + (t : ℂ) / 2 * Complex.I
  else if t ≤ 5 then (5 - t : ℂ) + 2 * Complex.I
  else ((9 : ℂ) - t) / 2 * Complex.I

lemma sixSideRectangleLoop_continuous : Continuous sixSideRectangleLoop := by
  have h₀ : Continuous (fun t : ℝ => ((3 : ℂ) - t) / 2 * Complex.I) :=
    ((continuous_const.sub Complex.continuous_ofReal).div_const 2).mul continuous_const
  have h₁ : Continuous (fun t : ℝ => (t - 1 : ℂ) + Complex.I) :=
    Complex.continuous_ofReal.sub continuous_const |>.add continuous_const
  have h₂ : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) / 2 * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.div_const 2 |>.mul continuous_const)
  have h₃ : Continuous (fun t : ℝ => (5 - t : ℂ) + 2 * Complex.I) :=
    (continuous_const.sub Complex.continuous_ofReal).add continuous_const
  have h₄ : Continuous (fun t : ℝ => ((9 : ℂ) - t) / 2 * Complex.I) :=
    ((continuous_const.sub Complex.continuous_ofReal).div_const 2).mul continuous_const
  unfold sixSideRectangleLoop
  refine Continuous.if_le h₀ ?_ continuous_id continuous_const ?_
  · refine Continuous.if_le h₁ ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le h₂ ?_ continuous_id continuous_const ?_
      · exact Continuous.if_le h₃ h₄ continuous_id continuous_const (by intro x hx; subst x; norm_num)
      · intro x hx; subst x; norm_num
    · intro x hx; subst x; norm_num
  · intro x hx; subst x; norm_num

lemma sixSideRectangleLoop_end : sixSideRectangleLoop 0 = sixSideRectangleLoop 6 := by norm_num [sixSideRectangleLoop]

lemma sixSideRectangleLoop_injective : InjOn sixSideRectangleLoop (Ico 0 6) := by
  intro s hs t ht h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  unfold sixSideRectangleLoop at hr hi
  split_ifs at hr hi
  all_goals try norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.normSq] at hr
  all_goals try norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.normSq] at hi
  all_goals first | assumption | linarith [hs.1, hs.2, ht.1, ht.2]


def sixSideRectangle : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im ∧ z.im ≤ 2}

lemma sixSideRectangle_closed : IsClosed sixSideRectangle := by
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

lemma sixSideRectangle_convex : Convex ℝ sixSideRectangle := by
  intro x hx y hy a b ha hb hab
  simp only [sixSideRectangle, mem_ofPred_eq, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.1 ha, mul_le_mul_of_nonneg_left hy.2.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.mpr hx.2.2.1) ha,
      mul_le_mul_of_nonneg_left (sub_nonneg.mpr hy.2.2.1) hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2.2.2 ha, mul_le_mul_of_nonneg_left hy.2.2.2 hb]

lemma sixSideRectangle_bounded : Bornology.IsBounded sixSideRectangle := by
  apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
  refine ⟨3, fun z hz ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
       _ ≤ 3 := by rw [abs_of_nonneg hz.1, abs_of_nonneg (by linarith [hz.2.2.1] : 0 ≤ z.im)]; linarith [hz.2.1, hz.2.2.2]

lemma sixSideRectangle_interior : interior sixSideRectangle =
    {z | 0 < z.re ∧ z.re < 1 ∧ 1 < z.im ∧ z.im < 2} := by
  have hre : IsOpenMap Complex.re := Complex.reCLM.isOpenMap (fun r ↦ ⟨r, by simp⟩)
  have him : IsOpenMap Complex.im := Complex.imCLM.isOpenMap (fun r ↦ ⟨r * Complex.I, by simp⟩)
  change interior ((Complex.re ⁻¹' Ici 0) ∩ ((Complex.re ⁻¹' Iic 1) ∩
    ((Complex.im ⁻¹' Ici 1) ∩ (Complex.im ⁻¹' Iic 2)))) = _
  rw [interior_inter, interior_inter, interior_inter,
    ← hre.preimage_interior_eq_interior_preimage Complex.continuous_re,
    ← hre.preimage_interior_eq_interior_preimage Complex.continuous_re,
    ← him.preimage_interior_eq_interior_preimage Complex.continuous_im,
    ← him.preimage_interior_eq_interior_preimage Complex.continuous_im,
    interior_Ici, interior_Iic, interior_Ici, interior_Iic]
  rfl

lemma sixSideRectangle_frontier : frontier sixSideRectangle =
    {z | z ∈ sixSideRectangle ∧ (z.re = 0 ∨ z.re = 1 ∨ z.im = 1 ∨ z.im = 2)} := by
  rw [frontier, sixSideRectangle_closed.closure_eq, sixSideRectangle_interior]
  ext z
  change (z ∈ sixSideRectangle ∧ ¬(0 < z.re ∧ z.re < 1 ∧ 1 < z.im ∧ z.im < 2)) ↔ _
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, ?_⟩
    by_cases h0 : z.re = 0
    · exact Or.inl h0
    by_cases h1 : z.re = 1
    · exact Or.inr (Or.inl h1)
    by_cases hb : z.im = 1
    · exact Or.inr (Or.inr (Or.inl hb))
    right; right; right
    have hr0 : 0 < z.re := lt_of_le_of_ne hz.1 (Ne.symm h0)
    have hr1 : z.re < 1 := lt_of_le_of_ne hz.2.1 h1
    have hi0 : 1 < z.im := lt_of_le_of_ne hz.2.2.1 (Ne.symm hb)
    exact le_antisymm hz.2.2.2 (le_of_not_gt (fun hlt ↦ h ⟨hr0,hr1,hi0,hlt⟩))
  · rintro ⟨hz, h | h | h | h⟩ <;> refine ⟨hz, ?_⟩ <;> rintro ⟨hr0,hr1,hi0,hi1⟩ <;> linarith

lemma sixSideRectangleLoop_image : sixSideRectangleLoop '' Icc 0 6 = frontier sixSideRectangle := by
  rw [sixSideRectangle_frontier]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    unfold sixSideRectangleLoop
    split_ifs
    all_goals norm_num [sixSideRectangle, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.normSq]
    all_goals constructor <;> linarith [ht.1, ht.2]
  · rintro ⟨hz, h | h | h | h⟩
    · by_cases hb : z.im ≤ 3/2
      · refine ⟨3-2*z.im, ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.1]⟩, ?_⟩
        apply Complex.ext <;> unfold sixSideRectangleLoop <;> split_ifs
        all_goals norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
          Complex.normSq]
        all_goals linarith [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
      · refine ⟨9-2*z.im, ⟨by linarith [hz.2.2.2], by linarith⟩, ?_⟩
        apply Complex.ext <;> unfold sixSideRectangleLoop <;> split_ifs
        all_goals norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
          Complex.normSq]
        all_goals linarith [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
    · refine ⟨2*z.im, ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩, ?_⟩
      apply Complex.ext <;> unfold sixSideRectangleLoop <;> split_ifs
      all_goals norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
        Complex.normSq]
      all_goals linarith [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
    · refine ⟨z.re+1, ⟨by linarith [hz.1], by linarith [hz.2.1]⟩, ?_⟩
      apply Complex.ext <;> unfold sixSideRectangleLoop <;> split_ifs
      all_goals norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
        Complex.normSq]
      all_goals linarith [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
    · refine ⟨5-z.re, ⟨by linarith [hz.2.1], by linarith [hz.1]⟩, ?_⟩
      apply Complex.ext <;> unfold sixSideRectangleLoop <;> split_ifs
      all_goals norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
        Complex.normSq]
      all_goals linarith [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]

theorem sixSideRectangle_boundary_parameter :
    ∃ j : Circle ≃ₜ frontier sixSideRectangle,
      ∀ t ∈ Icc (0 : ℝ) 6,
        (j (Circle.exp (2*Real.pi*t/6))).val = sixSideRectangleLoop t := by
  have : Fact (0 < (6 : ℝ)) := ⟨by norm_num⟩
  let g : AddCircle (6 : ℝ) → ℂ := AddCircle.liftIco 6 0 sixSideRectangleLoop
  have hg : Continuous g := AddCircle.liftIco_zero_continuous
    sixSideRectangleLoop_end sixSideRectangleLoop_continuous.continuousOn
  have hginj : Function.Injective g := by
    intro a b hab
    apply (AddCircle.equivIco (6 : ℝ) 0).injective
    apply Subtype.ext
    exact sixSideRectangleLoop_injective (by simpa using (AddCircle.equivIco (6 : ℝ) 0 a).property)
      (by simpa using (AddCircle.equivIco (6 : ℝ) 0 b).property) hab
  let e : AddCircle (6 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
  let j : Circle → ℂ := g ∘ e.symm
  have hj : _root_.Topology.IsEmbedding j :=
    ((hg.comp e.symm.continuous).isClosedEmbedding (hginj.comp e.symm.injective)).isEmbedding
  have hformula (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 6) :
      j (Circle.exp (2*Real.pi*t/6)) = sixSideRectangleLoop t := by
    have he : Circle.exp (2*Real.pi*t/6) = e (t : AddCircle (6 : ℝ)) := by
      rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
      congr 1
      ring
    rw [he]
    change g (e.symm (e (t : AddCircle (6 : ℝ)))) = _
    rw [e.symm_apply_apply]
    by_cases h : t = 6
    · subst t
      change AddCircle.liftIco 6 0 sixSideRectangleLoop (6 : ℝ) = _
      rw [AddCircle.coe_period]
      rw [← sixSideRectangleLoop_end]
      exact AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 6)
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 h⟩
  have hrange : range j = frontier sixSideRectangle := by
    rw [← sixSideRectangleLoop_image]
    apply Set.Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      refine ⟨(AddCircle.equivIco (6 : ℝ) 0 (e.symm z)).val, ?_, rfl⟩
      simpa using Ico_subset_Icc_self (AddCircle.equivIco (6 : ℝ) 0 (e.symm z)).property
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨Circle.exp (2*Real.pi*t/6), hformula t ht⟩
  exact ⟨hj.toHomeomorph.trans (Homeomorph.setCongr hrange), hformula⟩

/-- The rectangle disk chart has the six side parameters of the canonical
annulus word. Source: Gallier–Xu Proposition 3.2, p.31; Note F.4, p.167.
The affine loop descends to a circle homeomorphism because it is continuous,
injective on [0,6), and covers the frontier. A convex-body disk chart exists;
correcting its boundary map with disk_prescribed_boundary_extension yields
exactly the displayed angle parametrization, including the repeated endpoint. -/
theorem sixSideRectangle_disk_parameter :
    ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ sixSideRectangle,
      ∀ t ∈ Icc (0 : ℝ) 6,
        (h ⟨Circle.exp (2*Real.pi*t/6), by exact sphere_subset_closedBall (Circle.exp _).property⟩).val = sixSideRectangleLoop t := by
  have hne : (interior sixSideRectangle).Nonempty := by
    rw [sixSideRectangle_interior]
    exact ⟨(1/2 : ℝ) + (3/2 : ℝ)*Complex.I, by norm_num⟩
  obtain ⟨H, _, hcl, hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    sixSideRectangle_convex hne sixSideRectangle_bounded
  rw [sixSideRectangle_closed.closure_eq] at hcl
  let H₀ : sixSideRectangle ≃ₜ Metric.closedBall (0 : ℂ) 1 :=
    (H.image sixSideRectangle).trans (Homeomorph.setCongr hcl)
  have hbd : ∀ z : sixSideRectangle, z.val ∈ frontier sixSideRectangle ↔ ‖(H₀ z : ℂ)‖ = 1 := by
    intro z
    change z.val ∈ frontier sixSideRectangle ↔ ‖H z.val‖ = 1
    have hm : H z.val ∈ sphere (0 : ℂ) 1 ↔ ‖H z.val‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
    rw [← hm, ← hfr]
    exact H.injective.mem_set_image.symm
  obtain ⟨j, hj⟩ := sixSideRectangle_boundary_parameter
  have hsubset : frontier sixSideRectangle ⊆ sixSideRectangle := by
    exact frontier_subset_closure.trans_eq sixSideRectangle_closed.closure_eq
  obtain ⟨F, hF⟩ := HolomorphicAnosov.disk_prescribed_boundary_extension
    (frontier sixSideRectangle) sixSideRectangle hsubset H₀ hbd j.symm
  refine ⟨F.symm, ?_⟩
  intro t ht
  let z : frontier sixSideRectangle := j (Circle.exp (2*Real.pi*t/6))
  have hz := hF z (hsubset z.property)
  have he : F ⟨z.val, hsubset z.property⟩ =
      ⟨Circle.exp (2*Real.pi*t/6), by exact sphere_subset_closedBall (Circle.exp _).property⟩ := by
    apply Subtype.ext
    exact hz.trans (congrArg Subtype.val (j.symm_apply_apply _))
  rw [← he, F.symm_apply_apply]
  exact hj t ht


end HolomorphicAnosov.Topology.GallierXu

