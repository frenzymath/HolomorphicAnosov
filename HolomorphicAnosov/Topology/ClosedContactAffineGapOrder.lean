import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Affine filling of the gaps of a closed contact set

This module states DAG node `topo.closed_contact_interval_affine_gap_order_g5`.
It is an explicitly agent-written proof of the retained-contact-order step omitted
in Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§3(E), printed p.863. It is not attributed to Tietze or to a written Cairns proof.
The real unit interval always carries its usual induced topology and order.
-/

namespace HolomorphicAnosov

open Set

/-- Every point outside a closed contact set in the unit interval lies in a genuine
maximal complementary gap. This is the compact-extrema part of the affine-gap
construction, proved without enumerating or assuming finitely many gaps. -/
theorem exists_closed_contact_gap
    (F : Set ℝ) (hF_closed : IsClosed F)
    (hF_subset : F ⊆ Icc (0 : ℝ) 1)
    (hzero : (0 : ℝ) ∈ F) (hone : (1 : ℝ) ∈ F)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htF : t ∉ F) :
    ∃ l r : ℝ, l ∈ F ∧ r ∈ F ∧ l < t ∧ t < r ∧ Disjoint (Ioo l r) F := by
  have hI : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have hcompact : IsCompact (F ∩ Icc (0 : ℝ) 1) := by
    simpa [inter_comm] using hI.inter_right hF_closed
  let L : Set ℝ := F ∩ Icc (0 : ℝ) t
  let R : Set ℝ := F ∩ Icc t 1
  have hLc : IsCompact L := by
    simpa [L, inter_comm] using (isCompact_Icc.inter_right hF_closed : IsCompact (Icc (0 : ℝ) t ∩ F))
  have hRc : IsCompact R := by
    simpa [R, inter_comm] using (isCompact_Icc.inter_right hF_closed : IsCompact (Icc t 1 ∩ F))
  have hLn : L.Nonempty := ⟨0, hzero, ⟨le_rfl, ht.1⟩⟩
  have hRn : R.Nonempty := ⟨1, hone, ⟨ht.2, le_rfl⟩⟩
  obtain ⟨l, hlL, hlmax⟩ := hLc.exists_isMaxOn hLn continuousOn_id
  obtain ⟨r, hrR, hrmin⟩ := hRc.exists_isMinOn hRn continuousOn_id
  refine ⟨l, r, hlL.1, hrR.1, ?_, ?_, ?_⟩
  · have hlt : l ≤ t := hlL.2.2
    exact lt_of_le_of_ne hlt (Ne.symm (by
      intro h
      apply htF
      exact h ▸ hlL.1))
  · have hle : t ≤ r := hrR.2.1
    exact lt_of_ne_of_le (by
      intro h
      apply htF
      exact h ▸ hrR.1) hle
  · rw [Set.disjoint_left]
    intro x hxI hxF
    by_cases hxl : x ≤ t
    · have hxlL : x ∈ L := ⟨hxF, ⟨le_trans (hF_subset hlL.1).1 hxI.1.le, hxl⟩⟩
      exact (not_lt_of_ge (hlmax hxlL)) hxI.1
    · have hxrR : x ∈ R := ⟨hxF, ⟨le_of_not_ge hxl, le_trans hxI.2.le (hF_subset hrR.1).2⟩⟩
      exact (not_lt_of_ge (hrmin hxrR)) hxI.2

/-! The fixed-gap interpolation is continuous on the entire closed gap, including
its contact endpoints. This is the local analytic component of the global filling. -/
theorem affine_gap_continuousOn
    {l r fl fr : ℝ} (hlr : l < r) :
    ContinuousOn
      (fun x : ℝ ↦ (1 - (x - l) / (r - l)) * fl +
        ((x - l) / (r - l)) * fr) (Icc l r) := by
  have hden : (r - l : ℝ) ≠ 0 := sub_ne_zero.mpr hlr.ne'
  have hconst : Continuous (fun _ : ℝ ↦ (r - l : ℝ)⁻¹) := continuous_const
  have hquot : Continuous (fun x : ℝ ↦ (x - l) / (r - l)) := by
    apply Continuous.div (continuous_id.sub continuous_const) continuous_const
    intro _
    exact hden
  have hleft : Continuous (fun x : ℝ ↦ 1 - (x - l) / (r - l)) :=
    continuous_const.sub hquot
  exact ((hleft.mul continuous_const).add (hquot.mul continuous_const)).continuousOn

/-! Quantitative estimate used at an accumulation point of complementary gaps.
The only input about the endpoint values is their common `[0,1]` range. -/
theorem affine_gap_accumulation_bound
    {F : Set ℝ} {f : ℝ → ℝ}
    (hf_range : MapsTo f F (Icc (0 : ℝ) 1))
    {a b x theta : ℝ} (ha : a ∈ F) (hb : b ∈ F) (_hx : x ∈ F)
    (htheta0 : 0 ≤ theta) (_htheta1 : theta ≤ 1) :
    |(1 - theta) * f a + theta * f b - f x| ≤ |f a - f x| + theta := by
  have hfa0 : 0 ≤ f a := (hf_range ha).1
  have hfa1 : f a ≤ 1 := (hf_range ha).2
  have hfb0 : 0 ≤ f b := (hf_range hb).1
  have hfb1 : f b ≤ 1 := (hf_range hb).2
  have habs : |f b - f a| ≤ (1 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |(1 - theta) * f a + theta * f b - f x| =
        |(f a - f x) + theta * (f b - f a)| := by
          congr 1; ring
    _ ≤ |f a - f x| + |theta * (f b - f a)| := abs_add_le _ _
    _ = |f a - f x| + theta * |f b - f a| := by
      rw [abs_mul, abs_of_nonneg htheta0]
    _ ≤ |f a - f x| + theta * 1 := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left habs htheta0) _
    _ = |f a - f x| + theta := by ring

/-! The relative continuity hypothesis on the closed bounded contact set supplies the
uniform endpoint modulus needed when gaps accumulate at a contact point. -/
theorem closed_contact_endpoint_modulus
    (F : Set ℝ) (f : ℝ → ℝ)
    (hF_closed : IsClosed F) (hF_subset : F ⊆ Icc (0 : ℝ) 1)
    (hf_continuous : ContinuousOn f F) :
    ∀ ε > 0, ∃ δ > 0, ∀ a ∈ F, ∀ b ∈ F,
      dist a b < δ → dist (f a) (f b) < ε := by
  have hF_compact : IsCompact F :=
    isCompact_Icc.of_isClosed_subset hF_closed hF_subset
  have huc : UniformContinuousOn f F :=
    hF_compact.uniformContinuousOn_of_continuous hf_continuous
  exact Metric.uniformContinuousOn_iff.mp huc

theorem affine_gap_accumulation_lt
    {F : Set ℝ} {f : ℝ → ℝ}
    (hf_range : MapsTo f F (Icc (0 : ℝ) 1))
    {a b x theta ε : ℝ} (ha : a ∈ F) (hb : b ∈ F) (hx : x ∈ F)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) (_hε : 0 < ε)
    (hendpoint : |f a - f x| < ε / 2) (htheta : theta < ε / 2) :
    |(1 - theta) * f a + theta * f b - f x| < ε := by
  have hbound := affine_gap_accumulation_bound hf_range ha hb hx htheta0 htheta1
  apply lt_of_le_of_lt hbound
  nlinarith

/-! Geometry of the endpoint on the side of a contact point. -/
theorem affine_gap_side_geometry
    {l r x t η : ℝ} (hlr : l < r) (ht : t ∈ Ioo l r)
    (hx : x ∉ Ioo l r) (hη : 0 < η) (htx : |t - x| < η / 2) :
    ∃ a b theta : ℝ,
      ((a = l ∧ b = r ∧ theta = (t - l) / (r - l)) ∨
        (a = r ∧ b = l ∧ theta = (r - t) / (r - l))) ∧
      0 ≤ theta ∧ theta ≤ 1 ∧ |a - x| ≤ |t - x| ∧
      ((r - l < η / 2 ∧ |a - x| < η ∧ |b - x| < η) ∨
        (η / 2 ≤ r - l ∧ theta ≤ 2 * |t - x| / η)) := by
  have hden : 0 < r - l := sub_pos.mpr hlr
  have htxupper := (abs_lt.mp htx).2
  have htxlower := (abs_lt.mp htx).1
  by_cases hxl : x ≤ l
  · have hat : |l - x| = l - x := abs_of_nonneg (by linarith)
    have hbt : |r - x| = r - x := abs_of_nonneg (by linarith [ht.1, ht.2])
    have htt : |t - x| = t - x := abs_of_nonneg (by linarith [ht.1])
    refine ⟨l, r, (t - l) / (r - l), Or.inl ⟨rfl, rfl, rfl⟩,
      div_nonneg (by linarith [ht.1]) hden.le,
      (div_le_one hden).2 (by linarith [ht.2]), ?_, ?_⟩
    · rw [hat, htt]; linarith [ht.1]
    · by_cases hsmall : r - l < η / 2
      · left
        rw [hat, hbt]
        exact ⟨hsmall, by linarith [ht.1], by linarith [ht.1]⟩
      · right
        have hlarge := le_of_not_gt hsmall
        refine ⟨hlarge, (div_le_div_iff₀ hden hη).2 ?_⟩
        rw [htt]
        have hm := mul_le_mul_of_nonneg_left hlarge (by linarith [ht.1] : 0 ≤ 2 * (t - x))
        have hn := mul_le_mul_of_nonneg_right (by linarith : t - l ≤ t - x) hη.le
        nlinarith
  · have hrx : r ≤ x := by
      by_contra h
      exact hx ⟨lt_of_not_ge hxl, lt_of_not_ge h⟩
    have hat : |r - x| = x - r := by rw [abs_of_nonpos (by linarith)]; ring
    have hbt : |l - x| = x - l := by
      rw [abs_of_nonpos (by linarith [ht.1, ht.2])]; ring
    have htt : |t - x| = x - t := by
      rw [abs_of_nonpos (by linarith [ht.2])]; ring
    refine ⟨r, l, (r - t) / (r - l), Or.inr ⟨rfl, rfl, rfl⟩,
      div_nonneg (by linarith [ht.2]) hden.le,
      (div_le_one hden).2 (by linarith [ht.1]), ?_, ?_⟩
    · rw [hat, htt]; linarith [ht.2]
    · by_cases hsmall : r - l < η / 2
      · left
        rw [hat, hbt]
        exact ⟨hsmall, by linarith [ht.2], by linarith [ht.2]⟩
      · right
        have hlarge := le_of_not_gt hsmall
        refine ⟨hlarge, (div_le_div_iff₀ hden hη).2 ?_⟩
        rw [htt]
        have hm := mul_le_mul_of_nonneg_left hlarge (by linarith [ht.2] : 0 ≤ 2 * (x - t))
        have hn := mul_le_mul_of_nonneg_right (by linarith : r - t ≤ x - t) hη.le
        nlinarith



/-- Uniform continuity estimate across all complementary gaps at once. The contact
modulus and unit-range bound give a single radius independent of the gap. -/
theorem closed_contact_all_gaps_modulus
    (F : Set ℝ) (f : ℝ → ℝ)
    (hF_closed : IsClosed F) (hF_subset : F ⊆ Icc (0 : ℝ) 1)
    (hf_continuous : ContinuousOn f F)
    (hf_range : MapsTo f F (Icc (0 : ℝ) 1)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ F, ∀ l ∈ F, ∀ r ∈ F,
      l < r → Disjoint (Ioo l r) F → ∀ t ∈ Ioo l r, |t - x| < δ →
      |(1 - (t - l) / (r - l)) * f l +
        ((t - l) / (r - l)) * f r - f x| < ε := by
  intro ε hε
  obtain ⟨η, hη, hmod⟩ := closed_contact_endpoint_modulus F f hF_closed hF_subset
    hf_continuous (ε / 2) (half_pos hε)
  refine ⟨min (η / 2) (ε * η / 4), lt_min (half_pos hη) (by positivity), ?_⟩
  intro x hx l hl r hr hlr hgap t ht htx
  have htxη : |t - x| < η / 2 := lt_of_lt_of_le htx (min_le_left _ _)
  have htxε : |t - x| < ε * η / 4 := lt_of_lt_of_le htx (min_le_right _ _)
  have hxout : x ∉ Ioo l r := fun h ↦ Set.disjoint_left.mp hgap h hx
  obtain ⟨a, b, theta, horient, htheta0, htheta1, hax, hcases⟩ :=
    affine_gap_side_geometry hlr ht hxout hη htxη
  have ha : a ∈ F := by rcases horient with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> assumption
  have hb : b ∈ F := by rcases horient with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> assumption
  have hformula : (1 - (t - l) / (r - l)) * f l +
      ((t - l) / (r - l)) * f r = (1 - theta) * f a + theta * f b := by
    rcases horient with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rfl
    · have hne := ne_of_gt (sub_pos.mpr hlr)
      field_simp [hne]
      ; ring
  rw [hformula]
  have hnear : |f a - f x| < ε / 2 := by
    have h := hmod a ha x hx (by
      simpa only [Real.dist_eq] using (hax.trans_lt (htxη.trans (by linarith))))
    simpa only [Real.dist_eq] using h
  rcases hcases with ⟨_, _, hbx⟩ | ⟨_, hweight⟩
  · have hfar : |f b - f x| < ε / 2 := by
      simpa only [Real.dist_eq] using hmod b hb x hx (by simpa only [Real.dist_eq] using hbx)
    have heq : (1 - theta) * f a + theta * f b - f x =
        (1 - theta) * (f a - f x) + theta * (f b - f x) := by ring
    rw [heq]
    have hbnd : |(1 - theta) * (f a - f x) + theta * (f b - f x)| ≤ ε / 2 := by
      calc
        _ ≤ |(1 - theta) * (f a - f x)| + |theta * (f b - f x)| := abs_add_le _ _
        _ = (1 - theta) * |f a - f x| + theta * |f b - f x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - theta),
            abs_of_nonneg htheta0]
        _ ≤ (1 - theta) * (ε / 2) + theta * (ε / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hnear.le (by linarith))
            (mul_le_mul_of_nonneg_left hfar.le htheta0)
        _ = ε / 2 := by ring
    exact hbnd.trans_lt (by linarith)
  · apply affine_gap_accumulation_lt hf_range ha hb hx htheta0 htheta1 hε hnear
    apply hweight.trans_lt
    apply (div_lt_iff₀ hη).2
    nlinarith


/-- Every actual affine filling is continuous at each contact point, including
accumulation points of infinitely many complementary gaps. -/
theorem affine_filling_continuousWithinAt_contact
    (F : Set ℝ) (f g : ℝ → ℝ)
    (hF_closed : IsClosed F) (hF_subset : F ⊆ Icc (0 : ℝ) 1)
    (hzero : (0 : ℝ) ∈ F) (hone : (1 : ℝ) ∈ F)
    (hf_continuous : ContinuousOn f F)
    (hf_range : MapsTo f F (Icc (0 : ℝ) 1))
    (hcontact : EqOn g f F)
    (hfill : ∀ l ∈ F, ∀ r ∈ F, l < r → Disjoint (Ioo l r) F →
      ∀ t ∈ Ioo l r, g t = (1 - (t - l) / (r - l)) * f l +
        ((t - l) / (r - l)) * f r)
    {x : ℝ} (hx : x ∈ F) : ContinuousWithinAt g (Icc (0 : ℝ) 1) x := by
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ₁, hδ₁, hgapmod⟩ :=
    closed_contact_all_gaps_modulus F f hF_closed hF_subset hf_continuous hf_range ε hε
  obtain ⟨δ₂, hδ₂, hcontactmod⟩ :=
    closed_contact_endpoint_modulus F f hF_closed hF_subset hf_continuous ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro t ht htx
  rw [hcontact hx]
  by_cases htF : t ∈ F
  · rw [hcontact htF]
    exact hcontactmod t htF x hx (htx.trans_le (min_le_right _ _))
  · obtain ⟨l, r, hl, hr, hlt, htr, hgap⟩ :=
      exists_closed_contact_gap F hF_closed hF_subset hzero hone ht htF
    rw [hfill l hl r hr (hlt.trans htr) hgap t ⟨hlt, htr⟩]
    have h := hgapmod x hx l hl r hr (hlt.trans htr) hgap t ⟨hlt, htr⟩
      (by simpa only [Real.dist_eq] using htx.trans_le (min_le_left _ _))
    simpa only [Real.dist_eq] using h


/-- An affine filling of the actual complementary gaps is continuous on the
whole interval. No injectivity or orientation premise enters this step. -/
theorem affine_filling_continuousOn
    (F : Set ℝ) (f g : ℝ → ℝ)
    (hF_closed : IsClosed F) (hF_subset : F ⊆ Icc (0 : ℝ) 1)
    (hzero : (0 : ℝ) ∈ F) (hone : (1 : ℝ) ∈ F)
    (hf_continuous : ContinuousOn f F)
    (hf_range : MapsTo f F (Icc (0 : ℝ) 1))
    (hcontact : EqOn g f F)
    (hfill : ∀ l ∈ F, ∀ r ∈ F, l < r → Disjoint (Ioo l r) F →
      ∀ t ∈ Ioo l r, g t = (1 - (t - l) / (r - l)) * f l +
        ((t - l) / (r - l)) * f r) : ContinuousOn g (Icc (0 : ℝ) 1) := by
  intro x hx
  by_cases hxF : x ∈ F
  · exact affine_filling_continuousWithinAt_contact F f g hF_closed hF_subset
      hzero hone hf_continuous hf_range hcontact hfill hxF
  · obtain ⟨l, r, hl, hr, hlx, hxr, hgap⟩ :=
      exists_closed_contact_gap F hF_closed hF_subset hzero hone hx hxF
    have hc := (affine_gap_continuousOn (fl := f l) (fr := f r) (hlx.trans hxr)).mono
      (show Ioo l r ⊆ Icc l r from fun _ h ↦ ⟨h.1.le, h.2.le⟩)
    have hg : ContinuousWithinAt g (Ioo l r) x :=
      (hc x ⟨hlx, hxr⟩).congr_of_mem (hfill l hl r hr (hlx.trans hxr) hgap) ⟨hlx, hxr⟩
    exact (hg.continuousAt (isOpen_Ioo.mem_nhds ⟨hlx, hxr⟩)).continuousWithinAt


/-- The actual complementary intervals determine an affine filling consistently.
For a noncontact point choose a gap; any second gap containing it has the same
endpoints, since an endpoint strictly inside the other gap would belong to F.
Outside the unit interval the filling is totalized by f. -/
theorem exists_affine_filling
    (F : Set ℝ) (f : ℝ → ℝ)
    (hF_closed : IsClosed F) (hF_subset : F ⊆ Icc (0 : ℝ) 1)
    (hzero : (0 : ℝ) ∈ F) (hone : (1 : ℝ) ∈ F) :
    ∃ g : ℝ → ℝ, EqOn g f F ∧
      ∀ l ∈ F, ∀ r ∈ F, l < r → Disjoint (Ioo l r) F →
        ∀ t ∈ Ioo l r, g t = (1 - (t - l) / (r - l)) * f l +
          ((t - l) / (r - l)) * f r := by
  classical
  have huniq : ∀ l r l' r' t : ℝ,
      l ∈ F → r ∈ F → l' ∈ F → r' ∈ F →
      Disjoint (Ioo l r) F → Disjoint (Ioo l' r') F →
      t ∈ Ioo l r → t ∈ Ioo l' r' → l = l' ∧ r = r' := by
    intro l r l' r' t hl hr hl' hr' hd hd' ht ht'
    constructor
    · apply le_antisymm
      · by_contra h
        exact Set.disjoint_left.mp hd' ⟨lt_of_not_ge h, ht.1.trans ht'.2⟩ hl
      · by_contra h
        exact Set.disjoint_left.mp hd ⟨lt_of_not_ge h, ht'.1.trans ht.2⟩ hl'
    · apply le_antisymm
      · by_contra h
        exact Set.disjoint_left.mp hd ⟨ht.1.trans ht'.2, lt_of_not_ge h⟩ hr'
      · by_contra h
        exact Set.disjoint_left.mp hd' ⟨ht'.1.trans ht.2, lt_of_not_ge h⟩ hr
  have hvalue : ∀ t : ℝ, ∃ y : ℝ, (t ∈ F → y = f t) ∧
      ∀ l ∈ F, ∀ r ∈ F, l < r → Disjoint (Ioo l r) F →
        t ∈ Ioo l r → y = (1 - (t - l) / (r - l)) * f l +
          ((t - l) / (r - l)) * f r := by
    intro t
    by_cases htF : t ∈ F
    · refine ⟨f t, fun _ ↦ rfl, ?_⟩
      intro l hl r hr hlr hd ht
      exact (Set.disjoint_left.mp hd ht htF).elim
    · by_cases htI : t ∈ Icc (0 : ℝ) 1
      · obtain ⟨l, r, hl, hr, hlt, htr, hd⟩ :=
          exists_closed_contact_gap F hF_closed hF_subset hzero hone htI htF
        refine ⟨(1 - (t - l) / (r - l)) * f l + ((t - l) / (r - l)) * f r,
          fun h ↦ (htF h).elim, ?_⟩
        intro l' hl' r' hr' hlr' hd' ht'
        obtain ⟨rfl, rfl⟩ := huniq l r l' r' t hl hr hl' hr' hd hd' ⟨hlt, htr⟩ ht'
        rfl
      · refine ⟨f t, fun h ↦ (htF h).elim, ?_⟩
        intro l hl r hr hlr hd ht
        exact (htI ⟨(hF_subset hl).1.trans ht.1.le, ht.2.le.trans (hF_subset hr).2⟩).elim
  choose g hg using hvalue
  exact ⟨g, fun t ht ↦ (hg t).1 ht, fun l hl r hr hlr hd t ht ↦
    (hg t).2 l hl r hr hlr hd ht⟩


/-- The prescribed contact and pairwise image-gap separation make the actual
filling injective: contact/contact, contact/gap, and equal/distinct gap cases. -/
theorem affine_filling_injOn
    (F : Set ℝ) (f g : ℝ → ℝ)
    (hF_closed : IsClosed F) (hF_subset : F ⊆ Icc (0 : ℝ) 1)
    (hzero : (0 : ℝ) ∈ F) (hone : (1 : ℝ) ∈ F)
    (hf_injective : InjOn f F)
    (hcontact : EqOn g f F)
    (hfill : ∀ l ∈ F, ∀ r ∈ F, l < r → Disjoint (Ioo l r) F →
      ∀ t ∈ Ioo l r, g t = (1 - (t - l) / (r - l)) * f l +
        ((t - l) / (r - l)) * f r)
    (hgap_avoids : ∀ l r : ℝ, l ∈ F → r ∈ F → l < r →
      Disjoint (Ioo l r) F →
      Disjoint (Ioo (min (f l) (f r)) (max (f l) (f r))) (f '' F))
    (hgap_disjoint : ∀ l r l' r' : ℝ,
      l ∈ F → r ∈ F → l < r → Disjoint (Ioo l r) F →
      l' ∈ F → r' ∈ F → l' < r' → Disjoint (Ioo l' r') F →
      (l, r) ≠ (l', r') →
      Disjoint (Ioo (min (f l) (f r)) (max (f l) (f r)))
        (Ioo (min (f l') (f r')) (max (f l') (f r')))) :
    InjOn g (Icc (0 : ℝ) 1) := by
  have hmem : ∀ l ∈ F, ∀ r ∈ F, l < r → Disjoint (Ioo l r) F →
      ∀ t ∈ Ioo l r, g t ∈ Ioo (min (f l) (f r)) (max (f l) (f r)) := by
    intro l hl r hr hlr hd t ht
    have hdpos : 0 < r - l := sub_pos.mpr hlr
    have htpos : 0 < (t - l) / (r - l) := div_pos (sub_pos.mpr ht.1) hdpos
    have htone : (t - l) / (r - l) < 1 := (div_lt_one hdpos).2 (by linarith [ht.2])
    have hne : f l ≠ f r := fun h ↦ hlr.ne (hf_injective hl hr h)
    rw [hfill l hl r hr hlr hd t ht]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · simp only [min_eq_left hlt.le, max_eq_right hlt.le, mem_Ioo]
      constructor <;> nlinarith [mul_pos htpos (sub_pos.mpr hlt),
        mul_pos (sub_pos.mpr htone) (sub_pos.mpr hlt)]
    · simp only [min_eq_right hgt.le, max_eq_left hgt.le, mem_Ioo]
      constructor <;> nlinarith [mul_pos htpos (sub_pos.mpr hgt),
        mul_pos (sub_pos.mpr htone) (sub_pos.mpr hgt)]
  intro x hx y hy hxy
  by_cases hxF : x ∈ F
  · by_cases hyF : y ∈ F
    · apply hf_injective hxF hyF
      simpa only [hcontact hxF, hcontact hyF] using hxy
    · obtain ⟨l, r, hl, hr, hly, hyr, hd⟩ :=
        exists_closed_contact_gap F hF_closed hF_subset hzero hone hy hyF
      have hJ := hmem l hl r hr (hly.trans hyr) hd y ⟨hly, hyr⟩
      have him : g y ∈ f '' F := ⟨x, hxF, (hcontact hxF).symm.trans hxy⟩
      exact (Set.disjoint_left.mp (hgap_avoids l r hl hr (hly.trans hyr) hd) hJ him).elim
  · obtain ⟨l, r, hl, hr, hlx, hxr, hd⟩ :=
      exists_closed_contact_gap F hF_closed hF_subset hzero hone hx hxF
    have hJ := hmem l hl r hr (hlx.trans hxr) hd x ⟨hlx, hxr⟩
    by_cases hyF : y ∈ F
    · have him : g x ∈ f '' F := ⟨y, hyF, (hcontact hyF).symm.trans hxy.symm⟩
      exact (Set.disjoint_left.mp (hgap_avoids l r hl hr (hlx.trans hxr) hd) hJ him).elim
    · obtain ⟨l', r', hl', hr', hly, hyr, hd'⟩ :=
        exists_closed_contact_gap F hF_closed hF_subset hzero hone hy hyF
      by_cases he : (l, r) = (l', r')
      · have hel := congrArg Prod.fst he
        have her := congrArg Prod.snd he
        dsimp at hel her
        subst l'; subst r'
        have hfne : f l ≠ f r := fun h ↦ (hlx.trans hxr).ne (hf_injective hl hr h)
        rw [hfill l hl r hr (hlx.trans hxr) hd x ⟨hlx, hxr⟩,
          hfill l hl r hr (hly.trans hyr) hd' y ⟨hly, hyr⟩] at hxy
        have hdne : r - l ≠ 0 := ne_of_gt (sub_pos.mpr (hlx.trans hxr))
        field_simp [hdne] at hxy
        have hprod : (x - y) * (f r - f l) = 0 := by nlinarith [hxy]
        rcases mul_eq_zero.mp hprod with h | h
        · exact sub_eq_zero.mp h
        · exact (hfne (sub_eq_zero.mp h).symm).elim
      · have hJ' := hmem l' hl' r' hr' (hly.trans hyr) hd' y ⟨hly, hyr⟩
        rw [← hxy] at hJ'
        exact (Set.disjoint_left.mp
          (hgap_disjoint l r l' r' hl hr (hlx.trans hxr) hd hl' hr'
            (hly.trans hyr) hd' he) hJ hJ').elim


/-- A closed contact set with contact-free, disjoint endpoint image gaps has a
unique affine filling that is an increasing homeomorphism of the unit interval.

The two assumptions on gaps quantify over every endpoint pair in `F` whose open
interval avoids `F`. Neither increasing order nor exhaustion of the target gaps
is assumed. The homeomorphism in the conclusion has the prescribed contact values
and the literal affine formula on every source gap. Its uniqueness ranges over
all functions between the interval subtypes, without assuming continuity. `BijOn`
of the endpoint-pair map expresses the full bijection of complementary intervals,
including when there are no gaps.

Source and provenance: explicit bounded agent proof for the omitted step in
Cairns (1951), §3(E), p.863, recorded in
`dag/nodes/topo.closed_contact_interval_affine_gap_order_g5.json`.
The following is the complete natural-language proof of that node.

Step G1. Put I=[0,1]. The set F is compact because it is ambient closed and contained in compact
I. It is nonempty because it contains0,1. For t∈I\F, the sets F∩[0,t] and F∩[t,1] are compact by
intersecting each compact closed interval with ambient closed F, and nonempty by0 and1. Apply the
attained maximum/minimum leaves to the identity function: l(t)=max(F∩[0,t]) and r(t)=min(F∩[t,1])
belong to F. Since t∉F, l(t)<t<r(t). There is no F-point strictly between them: any such point on
either side of t contradicts the chosen extremum. Conversely any l<r in F with (l,r)∩F=∅ gives
precisely these same l(t),r(t) for every t∈(l,r). Thus these open intervals cover I\F and two such
intervals either coincide or are disjoint. This requires no enumeration, nowhere-denseness or
finite-gap premise.

Step G2. Define g(t)=f(t) for t∈F. For t∈I\F with its actual endpoints l<r put θ=(t−l)/(r−l) and
g(t)=(1−θ)f(l)+θ f(r). Here r−l>0 and 0<θ<1. Both endpoint values lie in I, so g(t)∈I, strictly
between the distinct endpoint values because InjOn f F gives f(l)≠f(r). The affine formula extends
to the closed gap interval with endpoint values f(l),f(r), consistently with the first branch.
Totalize g arbitrarily outside I only to fit ambient-function interfaces; every continuity/order
assertion below is restricted to I. The prescribed formula makes this extension unique. If F=I
there are no gaps and g=f on I.

Step G3. On every actual open gap the endpoints are constant by G1, and the formula is the real
affine map t↦f(l)+(t−l)(f(r)−f(l))/(r−l). It is continuous there by real continuous difference,
scalar multiplication and addition, with the denominator a FIXED positive number. Thus g is
continuous at every t∈I\F in its native interval topology. This does not assume a locally finite
family or pasting over all gaps.

Step G4. Fix x∈F and ε>0. Restrict the SAME f to the ACTUAL native compact subtype F: continuity
follows from ContinuousOn f F by continuousOn_iff_continuous_domRestrict and CompactSpace F by
isCompact_iff_compactSpace. Apply the existing Heine–Cantor supplier to this globally continuous
subtype map on its compact univ, then the metric modulus supplier, obtaining η>0 such that a,b∈F
and |a−b|<η imply |f(a)−f(b)|<ε/2. Set ζ=min(η/2,εη/4)>0 and take t∈I with |t−x|<ζ. If t∈F, the
required difference is already <ε/2. Otherwise x cannot lie strictly inside the gap(l,r)
containing t. Its nearer endpoint a on the side of x satisfies |a−x|≤|t−x| and |t−a|≤|t−x|; let b
be the other endpoint. If r−l<η/2, both endpoints are within η of x, so the affine convex
combination differs from f(x) by <ε/2. If r−l≥η/2, rewrite g(t)=f(a)+λ(f(b)−f(a)), where
λ=|t−a|/(r−l)≤2|t−x|/η. The GIVEN range f(F)⊂[0,1] gives |f(b)−f(a)|≤1, so
|g(t)−f(x)|≤|f(a)−f(x)|+2|t−x|/η<ε/2+ε/2=ε. This handles every gap, arbitrarily many and
arbitrarily accumulating, as well as x=0,1. Combined with G3 it proves ContinuousOn g I. No global
continuity of the original ambient totalization f is invoked.

Step G5. Prove InjOn g I by four cases. On F it is the given injectivity. A gap-interior image
lies in its open target endpoint interval J_(l,r), which by hypothesis is disjoint from f(F), so
it cannot equal a contact image. On one gap the affine slope is nonzero and hence the map is
injective. Points in two DISTINCT gaps have images in the hypothesized pairwise disjoint target
intervals, hence cannot agree. Gap endpoints belong to F and are handled there; target intervals
are open, so a shared endpoint creates no extra fibre. Thus no target-exhaustivity or preexisting
orientation assumption has entered.

Step G6. Now apply the exact existing closed-interval monotonicity theorem to a=0,b=1 and this
SAME g, using 0≤1, g(0)=0≤1=g(1), ContinuousOn g I and InjOn g I. It gives StrictMonoOn g I
directly, including its endpoints. In particular f preserves the order of ALL points of F,
including retained intervals and arbitrary accumulations. This invokes neither analytic smoothness
nor a prior order on F.

Step G7. The range bound in G2 gives g(I)⊂I. The ordinary intermediate-value theorem on closed I
with endpoint values0,1 gives the reverse inclusion, hence g is bijective I→I. The native
restriction is continuous by the domRestrict theorem. This first gives the continuous map I→ℝ; the
proven range g(I)⊂I and the existing mathlib.continuous_subtype_mk then give continuity of the
ACTUAL codomain-restricted map I→I used by the equivalence and homeomorphism constructor. Package
this actual bijection by Equiv.ofBijective; compactness of I and the Hausdorff real interval
subtype allow Continuous.homeoOfEquivCompactToT2, yielding a homeomorphism whose underlying
function is exactly this g. It extends f on F and preserves the exact affine formulas on gaps.

Step G8. Finally injectivity and g|F=f imply g(I\F)=I\f(F): every noncontact source point cannot
map into f(F), and the inverse of a target noncontact point cannot belong to F. Strict increase
identifies the image of EACH source gap(l,r) exactly with (f(l),f(r)), using its affine formula or
the interval intermediate-value theorem. The source intervals cover the complement by G1, so these
target intervals exhaust the target complement. In particular no extra target gap was assumed
away: exhaustive gap correspondence is a conclusion. This also covers the empty gap family F=I; F
itself is never empty because0,1∈F.
-/
theorem closed_contact_interval_affine_gap_order
    (F : Set ℝ) (f : ℝ → ℝ)
    (hF_closed : IsClosed F)
    (hF_subset : F ⊆ Icc (0 : ℝ) 1)
    (hzero : (0 : ℝ) ∈ F) (hone : (1 : ℝ) ∈ F)
    (hf_continuous : ContinuousOn f F)
    (hf_injective : InjOn f F)
    (hf_range : MapsTo f F (Icc (0 : ℝ) 1))
    (hf_zero : f 0 = 0) (hf_one : f 1 = 1)
    (hgap_avoids : ∀ l r : ℝ, l ∈ F → r ∈ F → l < r →
      Disjoint (Ioo l r) F →
      Disjoint (Ioo (min (f l) (f r)) (max (f l) (f r))) (f '' F))
    (hgap_disjoint : ∀ l r l' r' : ℝ,
      l ∈ F → r ∈ F → l < r → Disjoint (Ioo l r) F →
      l' ∈ F → r' ∈ F → l' < r' → Disjoint (Ioo l' r') F →
      (l, r) ≠ (l', r') →
      Disjoint (Ioo (min (f l) (f r)) (max (f l) (f r)))
        (Ioo (min (f l') (f r')) (max (f l') (f r')))) :
    ∃ g : ↥(Icc (0 : ℝ) 1) ≃ₜ ↥(Icc (0 : ℝ) 1),
      StrictMono g ∧
      (∀ x : ↥(Icc (0 : ℝ) 1), (x : ℝ) ∈ F → (g x : ℝ) = f x) ∧
      (∀ l r : ℝ, l ∈ F → r ∈ F → l < r → Disjoint (Ioo l r) F →
        ∀ x : ↥(Icc (0 : ℝ) 1), (x : ℝ) ∈ Ioo l r →
          (g x : ℝ) = (1 - ((x : ℝ) - l) / (r - l)) * f l +
            (((x : ℝ) - l) / (r - l)) * f r) ∧
      (∀ k : ↥(Icc (0 : ℝ) 1) → ↥(Icc (0 : ℝ) 1),
        (∀ x : ↥(Icc (0 : ℝ) 1), (x : ℝ) ∈ F → (k x : ℝ) = f x) →
        (∀ l r : ℝ, l ∈ F → r ∈ F → l < r → Disjoint (Ioo l r) F →
          ∀ x : ↥(Icc (0 : ℝ) 1), (x : ℝ) ∈ Ioo l r →
            (k x : ℝ) = (1 - ((x : ℝ) - l) / (r - l)) * f l +
              (((x : ℝ) - l) / (r - l)) * f r) →
        k = (fun x ↦ g x)) ∧
      StrictMonoOn f F ∧
      (∀ l r : ℝ, l ∈ F → r ∈ F → l < r → Disjoint (Ioo l r) F →
        (fun x : ↥(Icc (0 : ℝ) 1) ↦ (g x : ℝ)) ''
          {x : ↥(Icc (0 : ℝ) 1) | (x : ℝ) ∈ Ioo l r} = Ioo (f l) (f r)) ∧
      BijOn (fun p : ℝ × ℝ ↦ (f p.1, f p.2))
        {p : ℝ × ℝ | p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 < p.2 ∧ Disjoint (Ioo p.1 p.2) F}
        {p : ℝ × ℝ | p.1 ∈ f '' F ∧ p.2 ∈ f '' F ∧ p.1 < p.2 ∧
          Disjoint (Ioo p.1 p.2) (f '' F)} := by
  classical
  obtain ⟨g, hcontact, hfill⟩ := exists_affine_filling F f hF_closed hF_subset hzero hone
  have hcont := affine_filling_continuousOn F f g hF_closed hF_subset hzero hone
    hf_continuous hf_range hcontact hfill
  have hinj := affine_filling_injOn F f g hF_closed hF_subset hzero hone hf_injective
    hcontact hfill hgap_avoids hgap_disjoint
  have hg0 : g 0 = 0 := (hcontact hzero).trans hf_zero
  have hg1 : g 1 = 1 := (hcontact hone).trans hf_one
  have hmono : StrictMonoOn g (Icc (0 : ℝ) 1) :=
    ContinuousOn.strictMonoOn_of_injOn_Icc (by norm_num) (by rw [hg0, hg1]; norm_num)
      hcont hinj
  have hfmono : StrictMonoOn f F := by
    intro a ha b hb hab
    simpa only [hcontact ha, hcontact hb] using hmono (hF_subset ha) (hF_subset hb) hab
  have hmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    constructor
    · have h := hmono.monotoneOn (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ht ht.1
      simpa only [hg0] using h
    · have h := hmono.monotoneOn ht (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ht.2
      simpa only [hg1] using h
  let G : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t ↦ ⟨g t, hmap t.property⟩
  have hGc : Continuous G := (continuousOn_iff_continuous_domRestrict.mp hcont).subtype_mk _
  have hGi : Function.Injective G := by
    intro x y h
    apply Subtype.ext
    exact hinj x.property y.property (congrArg Subtype.val h)
  have hGs : Function.Surjective G := by
    intro y
    have hy : (y : ℝ) ∈ Icc (g 0) (g 1) := by simpa only [hg0, hg1] using y.property
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : Icc (0 : ℝ) 1 ≃ Icc (0 : ℝ) 1 := Equiv.ofBijective G ⟨hGi, hGs⟩
  let H : Icc (0 : ℝ) 1 ≃ₜ Icc (0 : ℝ) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f := e) hGc
  have hH : ∀ t, (H t : ℝ) = g t := fun _ ↦ rfl
  refine ⟨H, ?_, ?_, ?_, ?_, hfmono, ?_, ?_⟩
  · intro a b hab
    exact hmono a.property b.property hab
  · intro x hx
    exact (hH x).trans (hcontact hx)
  · intro l r hl hr hlr hd x hx
    exact (hH x).trans (hfill l hl r hr hlr hd x hx)
  · intro k hkF hkg
    funext x
    apply Subtype.ext
    by_cases hxF : (x : ℝ) ∈ F
    · exact (hkF x hxF).trans ((hH x).trans (hcontact hxF)).symm
    · obtain ⟨l, r, hl, hr, hlx, hxr, hd⟩ :=
        exists_closed_contact_gap F hF_closed hF_subset hzero hone x.property hxF
      rw [hkg l r hl hr (hlx.trans hxr) hd x ⟨hlx, hxr⟩, hH x,
        hfill l hl r hr (hlx.trans hxr) hd x ⟨hlx, hxr⟩]
  · intro l r hl hr hlr hd
    have hsub : Icc l r ⊆ Icc (0 : ℝ) 1 := fun x hx ↦
      ⟨(hF_subset hl).1.trans hx.1, hx.2.trans (hF_subset hr).2⟩
    have himg := (hcont.mono hsub).image_Ioo_of_strictMonoOn hlr.le (hmono.mono hsub)
    rw [hcontact hl, hcontact hr] at himg
    rw [← himg]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hH x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hsub ⟨hx.1.le, hx.2.le⟩⟩, hx, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rcases hp with ⟨hl, hr, hlr, hd⟩
      have hfr := hfmono hl hr hlr
      refine ⟨⟨p.1, hl, rfl⟩, ⟨p.2, hr, rfl⟩, hfr, ?_⟩
      simpa only [min_eq_left hfr.le, max_eq_right hfr.le] using
        hgap_avoids p.1 p.2 hl hr hlr hd
    · intro p hp q hq heq
      apply Prod.ext
      · exact hf_injective hp.1 hq.1 (congrArg Prod.fst heq)
      · exact hf_injective hp.2.1 hq.2.1 (congrArg Prod.snd heq)
    · intro p hp
      rcases hp with ⟨⟨l, hl, hfl⟩, ⟨r, hr, hfr⟩, hporder, hd⟩
      have hlr : l < r := by
        by_contra h
        have hle := hfmono.monotoneOn hr hl (le_of_not_gt h)
        rw [hfl, hfr] at hle
        exact (not_lt_of_ge hle) hporder
      have hgap : Disjoint (Ioo l r) F := by
        apply Set.disjoint_left.mpr
        intro t ht htF
        have hlt := hfmono hl htF ht.1
        have htr := hfmono htF hr ht.2
        rw [hfl] at hlt
        rw [hfr] at htr
        exact Set.disjoint_left.mp hd ⟨hlt, htr⟩ ⟨t, htF, rfl⟩
      exact ⟨(l, r), ⟨hl, hr, hlr, hgap⟩, Prod.ext hfl hfr⟩

end HolomorphicAnosov

