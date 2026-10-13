import HolomorphicAnosov.Geometry.IdealDiskTriangle
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import HolomorphicAnosov.Geometry.LyubichMarkedTriangleAffineIndependentG12

/-! The file supplies basic topological properties of the marked ideal-triangle carrier. (Lyubich, §2.4.4) -/

namespace HolomorphicAnosov
open Set Metric

/-- Explicit inverse of the radial Klein coordinate on the open unit disk. -/
noncomputable def idealDiskKleinInv (w : ℂ) : ℂ :=
  w / (1 + Real.sqrt (1 - ‖w‖ ^ 2))

theorem idealDiskKleinInv_left {z : ℂ} (hz : ‖z‖ < 1) :
    idealDiskKleinInv (idealDiskKlein z) = z := by
  unfold idealDiskKleinInv idealDiskKlein
  have hn : 0 ≤ ‖z‖ := norm_nonneg _
  have hsq : ‖z‖ ^ 2 < 1 := by simpa using ((sq_lt_sq₀ hn (by positivity)).mpr hz)
  have hd : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hnorm : ‖(2 * z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ))‖ =
      2 * ‖z‖ / (1 + ‖z‖ ^ 2) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    norm_num
  rw [hnorm]
  have harg : 0 ≤ 1 - (2 * ‖z‖ / (1 + ‖z‖ ^ 2)) ^ 2 := by
    field_simp
    nlinarith [hsq]
  have hsqrt : Real.sqrt (1 - (2 * ‖z‖ / (1 + ‖z‖ ^ 2)) ^ 2) =
      (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2) := by
    have hright : 0 ≤ (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2) := by positivity
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hright).mp
    rw [Real.sq_sqrt harg]
    field_simp
    ring
  rw [hsqrt]
  apply (div_eq_iff (by exact_mod_cast
    (ne_of_gt (by positivity : 0 < 1 + ((1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2) : ℝ))))).2
  have hzc : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hd)
  have hzc2 : (1 + (‖z‖ : ℂ) ^ 2) ≠ 0 := by
    intro h
    apply hzc
    norm_num at h ⊢
    exact h
  field_simp [hzc]
  push_cast
  field_simp [hzc2]
  ring

theorem idealDiskKlein_injective {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ < 1)
    (h₂ : ‖z₂‖ < 1) (he : idealDiskKlein z₁ = idealDiskKlein z₂) : z₁ = z₂ := by
  unfold idealDiskKlein at he
  have hd₁ : (1 + ‖z₁‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hd₂ : (1 + ‖z₂‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hc₁ : ((1 + ‖z₁‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd₁
  have hc₂ : ((1 + ‖z₂‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd₂
  field_simp [hc₁, hc₂] at he
  have hsq₁ : ‖z₁‖ ^ 2 < 1 := by nlinarith [norm_nonneg z₁, h₁]
  have hsq₂ : ‖z₂‖ ^ 2 < 1 := by nlinarith [norm_nonneg z₂, h₂]
  have hnorm := congrArg norm he
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 + ‖z₁‖ ^ 2),
    abs_of_pos (by positivity : 0 < 1 + ‖z₂‖ ^ 2)] at hnorm
  have hprod : (‖z₁‖ - ‖z₂‖) * (1 - ‖z₁‖ * ‖z₂‖) = 0 := by
    nlinarith [hnorm]
  have hab : ‖z₁‖ * ‖z₂‖ < 1 := by
    have h1 : ‖z₁‖ ≤ 1 := le_of_lt h₁
    have := mul_lt_mul_of_pos_left h₂ (by positivity : 0 < (1 : ℝ))
    nlinarith [sq_nonneg (‖z₁‖ - ‖z₂‖)]
  have hrad : ‖z₁‖ = ‖z₂‖ := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · nlinarith
  have hscalar : (1 + ‖z₂‖ ^ 2 : ℝ) = (1 + ‖z₁‖ ^ 2 : ℝ) := by rw [hrad]
  rw [hscalar] at he
  have hc : ((1 + ‖z₁‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity)
  apply (mul_right_cancel₀ hc)
  simpa [mul_comm] using he

/-- Right inverse of the radial Klein coordinate on the open disk. (Lyubich, §2.4.4) -/
theorem idealDiskKlein_right_inverse {w : ℂ} (hw : ‖w‖ < 1) :
    idealDiskKlein (idealDiskKleinInv w) = w := by
  let r : ℝ := ‖w‖
  let s : ℝ := Real.sqrt (1 - r ^ 2)
  have hr : 0 ≤ r := norm_nonneg _
  have hr2 : r ^ 2 < 1 := by
    simpa [r] using ((sq_lt_sq₀ hr (by positivity)).mpr hw)
  have hs : s ^ 2 = 1 - r ^ 2 := by
    simpa [s] using Real.sq_sqrt (show 0 ≤ 1 - r ^ 2 by linarith)
  have hs0 : 0 ≤ s := by simp [s]
  have hcR : (1 + s : ℝ) ≠ 0 := by positivity
  have hdR : 1 + (r / (1 + s)) ^ 2 ≠ 0 := by positivity
  have hnorm : ‖idealDiskKleinInv w‖ = r / (1 + s) := by
    unfold idealDiskKleinInv
    rw [norm_div]
    have hden : ‖(1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ))‖ =
        1 + Real.sqrt (1 - ‖w‖ ^ 2) := by
      have he : (1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ)) =
          ((1 + Real.sqrt (1 - ‖w‖ ^ 2) : ℝ) : ℂ) := by norm_num
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hden]
  unfold idealDiskKlein
  rw [hnorm]
  change 2 * (idealDiskKleinInv w) /
      ((1 + (r / (1 + s)) ^ 2 : ℝ) : ℂ) = w
  unfold idealDiskKleinInv
  have hden_eq :
      (1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ)) =
        ((1 + s : ℝ) : ℂ) := by
    dsimp [s, r]
    push_cast
    rfl
  rw [hden_eq]
  change 2 * (w / ((1 + s : ℝ) : ℂ)) /
      ((1 + (r / (1 + s)) ^ 2 : ℝ) : ℂ) = w
  have hcoefR : (2 : ℝ) / (1 + s) / (1 + (r / (1 + s)) ^ 2) = 1 := by
    field_simp [hcR]
    nlinarith [hs]
  have hcoefC : (2 : ℂ) / ((1 + s : ℝ) : ℂ) /
      ((1 + (r / (1 + s)) ^ 2 : ℝ) : ℂ) = 1 := by
    exact_mod_cast hcoefR
  calc
    2 * (w / ((1 + s : ℝ) : ℂ)) /
        ((1 + (r / (1 + s)) ^ 2 : ℝ) : ℂ) =
      w * ((2 : ℂ) / ((1 + s : ℝ) : ℂ) /
        ((1 + (r / (1 + s)) ^ 2 : ℝ) : ℂ)) := by ring
    _ = w := by rw [hcoefC, mul_one]

/-- The Klein-coordinate ideal-triangle interior is nonempty. -/
theorem markedIdealDiskTriangle_interior_nonempty
    (T : MarkedIdealDiskTriangle) : T.interiorSet.Nonempty := by
  have haff := markedIdealDiskTriangle_vertices_affineIndependent T
  have hspan : affineSpan ℝ (Set.range T.vertex) = ⊤ := by
    apply (haff.affineSpan_eq_top_iff_card_eq_finrank_add_one).2
    simp [Complex.finrank_real_complex]
  obtain ⟨w, hw⟩ :=
    (interior_convexHull_nonempty_iff_affineSpan_eq_top (s := Set.range T.vertex)).mpr hspan
  have hsub : convexHull ℝ (Set.range T.vertex) ⊆ Metric.closedBall (0 : ℂ) 1 := by
    apply convexHull_min
    · intro v hv
      rcases hv with ⟨i, hi⟩
      rw [← hi, Metric.mem_closedBall, dist_zero_right]
      simpa using (le_of_eq (T.norm_vertex i))
    · exact convex_closedBall _ _
  have hwball : w ∈ Metric.ball (0 : ℂ) 1 := by
    have hi := interior_mono hsub hw
    rw [interior_closedBall (0 : ℂ) (by norm_num)] at hi
    exact hi
  have hwlt : ‖w‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hwball
  refine ⟨idealDiskKleinInv w, ?_⟩
  have hnorm : ‖idealDiskKleinInv w‖ < 1 := by
    unfold idealDiskKleinInv
    rw [norm_div]
    have hden : ‖(1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ))‖ =
        1 + Real.sqrt (1 - ‖w‖ ^ 2) := by
      have he : (1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ)) =
          ((1 + Real.sqrt (1 - ‖w‖ ^ 2) : ℝ) : ℂ) := by norm_num
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    change ‖w‖ / ‖(1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ))‖ < 1
    rw [hden]
    exact (div_lt_iff₀ (by positivity : 0 < 1 + Real.sqrt (1 - ‖w‖ ^ 2))).2
      (by linarith [hwlt, Real.sqrt_nonneg (1 - ‖w‖ ^ 2)])
  have hinv : idealDiskKlein (idealDiskKleinInv w) = w :=
    idealDiskKlein_right_inverse (by simpa [idealDiskKleinInv] using hwlt)
  change ‖idealDiskKleinInv w‖ < 1 ∧
      idealDiskKlein (idealDiskKleinInv w) ∈ interior (convexHull ℝ (Set.range T.vertex))
  refine ⟨hnorm, ?_⟩
  rw [hinv]
  exact hw

/-- The literal marked ideal-triangle interior is open. -/
theorem markedIdealDiskTriangle_interior_isOpen
    (T : MarkedIdealDiskTriangle) : IsOpen T.interiorSet := by
  unfold MarkedIdealDiskTriangle.interiorSet
  have hk : Continuous idealDiskKlein := by
    unfold idealDiskKlein
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · intro z
      exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + ‖z‖ ^ 2))
  exact (isOpen_lt continuous_norm continuous_const).and
    (isOpen_interior.preimage hk)

/-- The literal marked ideal-triangle interior is bounded. -/
theorem markedIdealDiskTriangle_interior_isBounded
    (T : MarkedIdealDiskTriangle) : Bornology.IsBounded T.interiorSet := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
  refine ⟨1, ?_⟩
  intro z hz
  simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hz.1

/-- The marked ideal-triangle interior is simply connected. -/
theorem markedIdealDiskTriangle_interior_isSimplyConnected
    (T : MarkedIdealDiskTriangle) : IsSimplyConnected T.interiorSet := by
  let U : Set ℂ := interior (convexHull ℝ (Set.range T.vertex))
  have hsub : convexHull ℝ (Set.range T.vertex) ⊆ Metric.closedBall (0 : ℂ) 1 := by
    apply convexHull_min
    · intro v hv
      rcases hv with ⟨i, hi⟩
      rw [← hi, Metric.mem_closedBall, dist_zero_right]
      simpa using (le_of_eq (T.norm_vertex i))
    · exact convex_closedBall _ _
  have hUball : ∀ {w : ℂ}, w ∈ U → ‖w‖ < 1 := by
    intro w hw
    have hi := interior_mono hsub hw
    rw [interior_closedBall (0 : ℂ) (by norm_num)] at hi
    simpa [Metric.mem_ball, dist_zero_right] using hi
  have hk : Continuous idealDiskKlein := by
    unfold idealDiskKlein
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · intro z
      exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + ‖z‖ ^ 2))
  have hi : ContinuousOn idealDiskKleinInv U := by
    unfold idealDiskKleinInv
    apply ContinuousOn.div₀ continuousOn_id
    · have harg : ContinuousOn (fun x : ℂ ↦ (1 : ℝ) - ‖x‖ ^ 2) U :=
        continuousOn_const.sub (continuous_norm.continuousOn.pow 2)
      have hsqrt := harg.sqrt
      have hc : ContinuousOn
          (fun x : ℂ ↦ ((1 + Real.sqrt (1 - ‖x‖ ^ 2) : ℝ) : ℂ)) U :=
        Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_const (c := (1 : ℝ)).add hsqrt)
      simpa using hc
    · intro w hw
      exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + Real.sqrt (1 - ‖w‖ ^ 2)))
  have hinvnorm : ∀ {w : ℂ}, w ∈ U → ‖idealDiskKleinInv w‖ < 1 := by
    intro w hw
    unfold idealDiskKleinInv
    rw [norm_div]
    have hden : ‖(1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ))‖ =
        1 + Real.sqrt (1 - ‖w‖ ^ 2) := by
      have he : (1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ)) =
          ((1 + Real.sqrt (1 - ‖w‖ ^ 2) : ℝ) : ℂ) := by norm_num
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    change ‖w‖ / ‖(1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ))‖ < 1
    rw [hden]
    exact (div_lt_iff₀ (by positivity : 0 < 1 + Real.sqrt (1 - ‖w‖ ^ 2))).2
      (by linarith [hUball hw, Real.sqrt_nonneg (1 - ‖w‖ ^ 2)])
  have hinv_mem : ∀ w : U, idealDiskKleinInv w.1 ∈ T.interiorSet := by
    intro w
    exact ⟨hinvnorm w.property,
      by rw [idealDiskKlein_right_inverse (hUball w.property)]; exact w.property⟩
  let e : T.interiorSet ≃ₜ U := {
    toFun := fun z => ⟨idealDiskKlein z, z.property.2⟩
    invFun := fun w => ⟨idealDiskKleinInv w, by
      exact hinv_mem w⟩
    left_inv := fun z => Subtype.ext (idealDiskKleinInv_left z.property.1)
    right_inv := fun w => Subtype.ext (idealDiskKlein_right_inverse (hUball w.property))
    continuous_toFun := hk.continuousOn.domRestrict.subtype_mk _
    continuous_invFun := hi.domRestrict.subtype_mk hinv_mem }
  obtain ⟨z, hz⟩ := markedIdealDiskTriangle_interior_nonempty T
  let : ContractibleSpace U := (Convex.interior (convex_convexHull ℝ _)).contractibleSpace
    ⟨idealDiskKlein z, hz.2⟩
  have hcontract : ContractibleSpace T.interiorSet :=
    Homeomorph.contractibleSpace e
  let := hcontract
  exact SimplyConnectedSpace.ofContractible _

/-- The marked ideal-triangle interior has Jordan boundary. -/
theorem markedIdealDiskTriangle_interior_hasJordanBoundary
    (T : MarkedIdealDiskTriangle) :
    Analysis.MarkedRectangle.HasJordanBoundary T.interiorSet := by
  let C : Set ℂ := convexHull ℝ (Set.range T.vertex)
  have hCclosed : IsClosed C := (Set.finite_range T.vertex).isClosed_convexHull ℝ
  have hsub : C ⊆ closedBall (0 : ℂ) 1 := by
    apply convexHull_min
    · rintro v ⟨i, rfl⟩
      simp [mem_closedBall, dist_zero_right, T.norm_vertex i]
    · exact convex_closedBall _ _
  have hUball : ∀ {w : ℂ}, w ∈ interior C → ‖w‖ < 1 := by
    intro w hw
    have hh := interior_mono hsub hw
    rw [interior_closedBall (0 : ℂ) (by norm_num)] at hh
    simpa [mem_ball, dist_zero_right] using hh
  have hinvnorm (w : ℂ) :
      ‖idealDiskKleinInv w‖ = ‖w‖ / (1 + Real.sqrt (1 - ‖w‖ ^ 2)) := by
    unfold idealDiskKleinInv
    have he : (1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ)) =
        ((1 + Real.sqrt (1 - ‖w‖ ^ 2) : ℝ) : ℂ) := by norm_num
    rw [norm_div, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hinv_lt {w : ℂ} (hw : ‖w‖ < 1) : ‖idealDiskKleinInv w‖ < 1 := by
    rw [hinvnorm]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith [Real.sqrt_nonneg (1 - ‖w‖ ^ 2)])
  have hinv_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖idealDiskKleinInv w‖ ≤ 1 := by
    rw [hinvnorm]
    exact (div_le_iff₀ (by positivity)).2 (by linarith [Real.sqrt_nonneg (1 - ‖w‖ ^ 2)])
  have hright {w : ℂ} (hw : ‖w‖ ≤ 1) : idealDiskKlein (idealDiskKleinInv w) = w := by
    rcases lt_or_eq_of_le hw with hw | hw
    · exact idealDiskKlein_right_inverse hw
    · have hiw : idealDiskKleinInv w = w := by simp [idealDiskKleinInv, hw]
      rw [hiw]
      norm_num [idealDiskKlein, hw]
  have hleft {z : ℂ} (hz : ‖z‖ ≤ 1) : idealDiskKleinInv (idealDiskKlein z) = z := by
    rcases lt_or_eq_of_le hz with hz | hz
    · exact idealDiskKleinInv_left hz
    · have hkz : idealDiskKlein z = z := by norm_num [idealDiskKlein, hz]
      rw [hkz]
      simp [idealDiskKleinInv, hz]
  have hcont : Continuous idealDiskKleinInv := by
    unfold idealDiskKleinInv
    apply Continuous.div₀ continuous_id
    · fun_prop
    · intro z
      exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + Real.sqrt (1 - ‖z‖ ^ 2)))
  have hk : Continuous idealDiskKlein := by
    unfold idealDiskKlein
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · intro z
      exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + ‖z‖ ^ 2))
  have hclosure : closure T.interiorSet = T.closedSet := by
    let C : Set ℂ := convexHull ℝ (Set.range T.vertex)
    have hInvU : idealDiskKleinInv '' interior C ⊆ T.interiorSet := by
      rintro z ⟨w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · unfold idealDiskKleinInv
        have he : (1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ)) =
            ((1 + Real.sqrt (1 - ‖w‖ ^ 2) : ℝ) : ℂ) := by norm_num
        rw [norm_div, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact (div_lt_iff₀ (by positivity : 0 < 1 + Real.sqrt (1 - ‖w‖ ^ 2))).2
          (by linarith [hUball hw, Real.sqrt_nonneg (1 - ‖w‖ ^ 2)])
      · rw [idealDiskKlein_right_inverse (hUball hw)]
        exact hw
    have hleft' : ∀ {z : ℂ}, ‖z‖ ≤ 1 → idealDiskKleinInv (idealDiskKlein z) = z := by
      intro z hz
      rcases lt_or_eq_of_le hz with hz | hz
      · exact idealDiskKleinInv_left hz
      · have hkz : idealDiskKlein z = z := by norm_num [idealDiskKlein, hz]
        rw [hkz]
        simp [idealDiskKleinInv, hz]
    apply Set.Subset.antisymm
    · apply closure_minimal
      · intro z hz
        exact ⟨le_of_lt hz.1, interior_subset hz.2⟩
      · exact (isClosed_le continuous_norm continuous_const).inter (hCclosed.preimage hk)
    · intro z hz
      obtain ⟨w, hw⟩ := markedIdealDiskTriangle_interior_nonempty T
      have hCreg : closure (interior C) = C := by
        rw [(convex_convexHull ℝ (Set.range T.vertex)).closure_interior_eq_closure_of_nonempty_interior
          ⟨idealDiskKlein w, hw.2⟩, hCclosed.closure_eq]
      have himg : z ∈ idealDiskKleinInv '' closure (interior C) := by
        refine ⟨idealDiskKlein z, ?_, hleft' hz.1⟩
        rw [hCreg]
        exact hz.2
      exact closure_mono hInvU (image_closure_subset_closure_image hcont himg)
  have hfront : idealDiskKleinInv '' frontier C = frontier T.interiorSet := by
    rw [(markedIdealDiskTriangle_interior_isOpen T).frontier_eq,
      hclosure, hCclosed.frontier_eq]
    ext z
    constructor
    · rintro ⟨w, ⟨hwC, hwU⟩, rfl⟩
      have hwle : ‖w‖ ≤ 1 := by simpa using hsub hwC
      refine ⟨⟨hinv_le hwle, ?_⟩, ?_⟩
      · rw [hright hwle]
        exact hwC
      · intro hz
        apply hwU
        simpa only [hright hwle] using hz.2
    · rintro ⟨hzC, hzU⟩
      refine ⟨idealDiskKlein z, ⟨hzC.2, ?_⟩, hleft hzC.1⟩
      intro hwU
      apply hzU
      refine ⟨?_, hwU⟩
      rw [← hleft hzC.1]
      exact hinv_lt (hUball hwU)
  obtain ⟨z, hz⟩ := markedIdealDiskTriangle_interior_nonempty T
  obtain ⟨h, _, _, hsphere⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_convexHull ℝ (Set.range T.vertex)) ⟨idealDiskKlein z, hz.2⟩
      (Metric.isBounded_closedBall.subset hsub)
  let j : Circle → ℂ := fun ζ ↦ idealDiskKleinInv (h.symm ζ)
  have hjfront (ζ : Circle) : h.symm (ζ : ℂ) ∈ frontier C := by
    have hmem : (ζ : ℂ) ∈ h '' frontier C := by rw [hsphere]; exact ζ.property
    obtain ⟨w, hw, he⟩ := hmem
    simpa [← he] using hw
  have hjcont : Continuous j := hcont.comp (h.symm.continuous.comp continuous_subtype_val)
  have hjinj : Function.Injective j := by
    intro ζ η he
    apply Subtype.ext
    apply h.symm.injective
    have hζ : ‖h.symm (ζ : ℂ)‖ ≤ 1 := by
      simpa using hsub (hCclosed.frontier_subset (hjfront ζ))
    have hη : ‖h.symm (η : ℂ)‖ ≤ 1 := by
      simpa using hsub (hCclosed.frontier_subset (hjfront η))
    have hh := congrArg idealDiskKlein he
    simpa only [j, hright hζ, hright hη] using hh
  refine ⟨j, (hjcont.isClosedEmbedding hjinj).isEmbedding, ?_⟩
  rw [← hfront]
  ext x
  constructor
  · rintro ⟨ζ, rfl⟩
    exact ⟨h.symm ζ, hjfront ζ, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hhw : h w ∈ sphere (0 : ℂ) 1 := by rw [← hsphere]; exact mem_image_of_mem h hw
    refine ⟨⟨h w, hhw⟩, ?_⟩
    simp [j]

/-- The closure of the marked ideal-triangle interior is its filled carrier. -/
theorem markedIdealDiskTriangle_closure_interior_eq_closedSet
    (T : MarkedIdealDiskTriangle) : closure T.interiorSet = T.closedSet := by
  let C : Set ℂ := convexHull ℝ (Set.range T.vertex)
  have hCclosed : IsClosed C := (Set.finite_range T.vertex).isClosed_convexHull ℝ
  have hk : Continuous idealDiskKlein := by
    unfold idealDiskKlein
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · intro z
      exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + ‖z‖ ^ 2))
  have hi : Continuous idealDiskKleinInv := by
    unfold idealDiskKleinInv
    apply Continuous.div₀ continuous_id
    · fun_prop
    · intro z
      exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + Real.sqrt (1 - ‖z‖ ^ 2)))
  have hsub : C ⊆ Metric.closedBall (0 : ℂ) 1 := by
    apply convexHull_min
    · rintro v ⟨i, rfl⟩
      simp [Metric.mem_closedBall, dist_zero_right, T.norm_vertex i]
    · exact convex_closedBall _ _
  have hUball : ∀ {w : ℂ}, w ∈ interior C → ‖w‖ < 1 := by
    intro w hw
    have h := interior_mono hsub hw
    rw [interior_closedBall (0 : ℂ) (by norm_num)] at h
    simpa [Metric.mem_ball, dist_zero_right] using h
  have hInvU : idealDiskKleinInv '' interior C ⊆ T.interiorSet := by
    rintro z ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · unfold idealDiskKleinInv
      have he : (1 + (Real.sqrt (1 - ‖w‖ ^ 2) : ℂ)) =
          ((1 + Real.sqrt (1 - ‖w‖ ^ 2) : ℝ) : ℂ) := by norm_num
      rw [norm_div, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (div_lt_iff₀ (by positivity : 0 < 1 + Real.sqrt (1 - ‖w‖ ^ 2))).2
        (by linarith [hUball hw, Real.sqrt_nonneg (1 - ‖w‖ ^ 2)])
    · rw [idealDiskKlein_right_inverse (hUball hw)]
      exact hw
  have hleft : ∀ {z : ℂ}, ‖z‖ ≤ 1 → idealDiskKleinInv (idealDiskKlein z) = z := by
    intro z hz
    rcases lt_or_eq_of_le hz with h | h
    · exact idealDiskKleinInv_left h
    · have hkz : idealDiskKlein z = z := by
        unfold idealDiskKlein
        rw [h]
        norm_num
      rw [hkz]
      unfold idealDiskKleinInv
      rw [h]
      norm_num
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro z hz
      exact ⟨le_of_lt hz.1, interior_subset hz.2⟩
    · exact (isClosed_le continuous_norm continuous_const).inter (hCclosed.preimage hk)
  · intro z hz
    obtain ⟨w, hw⟩ := markedIdealDiskTriangle_interior_nonempty T
    have hCreg : closure (interior C) = C := by
      rw [(convex_convexHull ℝ (Set.range T.vertex)).closure_interior_eq_closure_of_nonempty_interior
        ⟨idealDiskKlein w, hw.2⟩, hCclosed.closure_eq]
    have himg : z ∈ idealDiskKleinInv '' closure (interior C) := by
      refine ⟨idealDiskKlein z, ?_, hleft hz.1⟩
      rw [hCreg]
      exact hz.2
    exact closure_mono hInvU (image_closure_subset_closure_image hi himg)

end HolomorphicAnosov
