import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic

open Set Metric

namespace HolomorphicAnosov.Topology

def cairnsClosedHalfDisk (upper : Bool) : Set ℂ :=
  closedBall (0 : ℂ) 1 ∩ if upper then {z : ℂ | 0 ≤ z.im} else {z : ℂ | z.im ≤ 0}

def cairnsUnitDiameter : Set ℂ :=
  closedBall (0 : ℂ) 1 ∩ {z : ℂ | z.im = 0}

/-! Explicit parametrization of the diameter used by the seam branch. -/
theorem cairns_halfdisk_diameter_homeomorph :
    ∃ d : unitInterval ≃ₜ cairnsUnitDiameter,
      ∀ t : unitInterval,
        (d t : ℂ) = ((2 * (t : ℝ) - 1 : ℝ) : ℂ) := by
  let d : unitInterval ≃ₜ cairnsUnitDiameter :=
    { toFun := fun t =>
        ⟨((2 * (t : ℝ) - 1 : ℝ) : ℂ), by
          constructor
          · rw [mem_closedBall, dist_zero_right]
            rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
            constructor <;> nlinarith [t.property.1, t.property.2]
          · norm_num⟩
      invFun := fun z =>
        ⟨((z : ℂ).re + 1) / 2, by
          have hz := z.property.1
          rw [mem_closedBall, dist_zero_right] at hz
          have hr : |(z : ℂ).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hz
          rw [mem_Icc]
          constructor <;> nlinarith [neg_le_of_abs_le hr,
            le_abs_self (Complex.re (z : ℂ))]⟩
      left_inv := by
        intro t
        apply Subtype.ext
        dsimp
        norm_num
      right_inv := by
        intro z
        apply Subtype.ext
        apply Complex.ext
        · dsimp
          nlinarith
        · change 0 = (z : ℂ).im
          exact z.property.2.symm
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop
      continuous_invFun := by
        apply Continuous.subtype_mk
        fun_prop }
  refine ⟨d, ?_⟩
  intro t
  rfl

/-! Every diameter point is a frontier point of either closed half disk. -/
theorem cairns_halfdisk_diameter_subset_frontier (upper : Bool) :
    cairnsUnitDiameter ⊆ frontier (cairnsClosedHalfDisk upper) := by
  have hclosed : IsClosed (cairnsClosedHalfDisk upper) := by
    cases upper with
    | false =>
        simp only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte]
        exact isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const)
    | true =>
        simp only [cairnsClosedHalfDisk, ↓reduceIte]
        exact isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)
  have hinterior : interior (cairnsClosedHalfDisk upper) =
      ball (0 : ℂ) 1 ∩ if upper then {z : ℂ | 0 < z.im} else {z : ℂ | z.im < 0} := by
    cases upper with
    | false =>
        simp only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte]
        rw [interior_inter, interior_closedBall]
        change ball (0 : ℂ) 1 ∩ interior (Complex.im ⁻¹' Iic (0 : ℝ)) = _
        rw [Complex.interior_preimage_im, interior_Iic]
        ext z
        rfl
        all_goals norm_num
    | true =>
        simp only [cairnsClosedHalfDisk, ↓reduceIte]
        rw [interior_inter, interior_closedBall]
        change ball (0 : ℂ) 1 ∩ interior (Complex.im ⁻¹' Ici (0 : ℝ)) = _
        rw [Complex.interior_preimage_im, interior_Ici]
        ext z
        rfl
        all_goals norm_num
  cases upper with
  | false =>
      intro z hz
      rw [hclosed.frontier_eq, hinterior]
      change (z ∈ closedBall (0 : ℂ) 1 ∧ z.im ≤ 0) ∧
        ¬ (z ∈ ball (0 : ℂ) 1 ∧ z.im < 0)
      change z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0 at hz
      refine ⟨⟨hz.1, le_of_eq hz.2⟩, ?_⟩
      intro hzint
      linarith [hz.2, hzint.2]
  | true =>
      intro z hz
      rw [hclosed.frontier_eq, hinterior]
      change (z ∈ closedBall (0 : ℂ) 1 ∧ 0 ≤ z.im) ∧
        ¬ (z ∈ ball (0 : ℂ) 1 ∧ 0 < z.im)
      change z ∈ closedBall (0 : ℂ) 1 ∧ z.im = 0 at hz
      refine ⟨⟨hz.1, le_of_eq hz.2.symm⟩, ?_⟩
      intro hzint
      linarith [hz.2, hzint.2]

/-! The remaining closed-pair pasting step in Cairns §4(D).

The two embedded arcs cover the source boundary and intersect only at their
marked endpoints.  One arc is prescribed to the affine diameter; the other is
sent to the selected closed semicircle of the half-disk frontier.  Cairns'
printed argument invokes finite closed-set pasting and compact-to-Hausdorff
upgrade without expanding the subtype maps.  This named provider isolates that
exact bookkeeping obligation for reuse by the boundary transport parent. -/
theorem cairns_closed_arc_pair_boundary_homeomorph
    (upper : Bool) (c : Set ℂ) (p q : ℂ)
    (e₂ e₃ b : unitInterval → ℂ)
    (he₂ : Topology.IsEmbedding e₂) (he₃ : Topology.IsEmbedding e₃)
    (hb : Topology.IsEmbedding b)
    (h0 : b 0 = p) (h1 : b 1 = q)
    (h0₂ : e₂ 0 = p) (h1₂ : e₂ 1 = q)
    (h0₃ : e₃ 0 = q) (h1₃ : e₃ 1 = p)
    (hcover : range e₂ ∪ range e₃ = c)
    (hintersect : range e₂ ∩ range e₃ = {p, q})
    (hseam : range b = range e₂ ∨ range b = range e₃)
    (hB : range b ⊆ c) (_hpq : p ≠ q) :
    ∃ H : c ≃ₜ frontier (cairnsClosedHalfDisk upper),
      ∀ t : unitInterval,
        ((H (⟨b t, hB (mem_range_self t)⟩ : c) :
          frontier (cairnsClosedHalfDisk upper)) : ℂ) =
          ((2 * (t : ℝ) - 1 : ℝ) : ℂ) := by
  classical
  let S : Set ℂ := sphere (0 : ℂ) 1 ∩
    if upper then {z : ℂ | 0 ≤ z.im} else {z : ℂ | z.im ≤ 0}
  have hsemicircle : ∃ d : unitInterval ≃ₜ S,
      (d 0 : ℂ) = -1 ∧ (d 1 : ℂ) = 1 ∧
      ∀ t, (d t : ℂ).re = 2 * (t : ℝ) - 1 := by
    let f : unitInterval → ℂ := fun t ↦
      ⟨2 * (t : ℝ) - 1, if upper then Real.sqrt (1 - (2 * (t : ℝ) - 1)^2)
        else -Real.sqrt (1 - (2 * (t : ℝ) - 1)^2)⟩
    have hf (t : unitInterval) : f t ∈ S := by
      have hs : 0 ≤ 1 - (2 * (t : ℝ) - 1)^2 := by
        nlinarith [t.property.1, t.property.2,
          mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)]
      have hsq := Real.sq_sqrt hs
      have hnorm : ‖f t‖ = 1 := by
        have hn : ‖f t‖ ^ 2 = 1 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          dsimp [f]
          cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith
        nlinarith [norm_nonneg (f t)]
      refine ⟨?_, ?_⟩
      · simpa only [mem_sphere, dist_zero_right] using hnorm
      · cases upper <;> simp [f, Real.sqrt_nonneg]
    let d : unitInterval ≃ₜ S :=
      { toFun := fun t ↦ ⟨f t, hf t⟩
        invFun := fun z ↦ ⟨((z : ℂ).re + 1) / 2, by
          have hz : ‖(z : ℂ)‖ = 1 := by
            simpa only [mem_sphere, dist_zero_right] using z.property.1
          have hr := Complex.abs_re_le_norm (z : ℂ)
          rw [hz, abs_le] at hr
          constructor <;> linarith [hr.1, hr.2]⟩
        left_inv := by
          intro t
          apply Subtype.ext
          dsimp [f]
          ring
        right_inv := by
          intro z
          apply Subtype.ext
          have hz : ‖(z : ℂ)‖ = 1 := by
            simpa only [mem_sphere, dist_zero_right] using z.property.1
          have hsq : (z : ℂ).re^2 + (z : ℂ).im^2 = 1 := by
            have hn := Complex.normSq_eq_norm_sq (z : ℂ)
            rw [hz, Complex.normSq_apply] at hn
            nlinarith
          have heq : 1 - (2 * (((z : ℂ).re + 1) / 2) - 1)^2 = (z : ℂ).im^2 := by
            nlinarith
          apply Complex.ext
          · dsimp [f]
            ring
          · change (if upper then Real.sqrt _ else -Real.sqrt _) = _
            rw [heq, Real.sqrt_sq_eq_abs]
            have him := z.property.2
            cases upper with
            | false =>
                change (z : ℂ).im ≤ 0 at him
                simp [abs_of_nonpos him]
            | true =>
                change 0 ≤ (z : ℂ).im at him
                simp [abs_of_nonneg him]
        continuous_toFun := by
          apply Continuous.subtype_mk
          cases upper <;> dsimp [f] <;>
            simp_rw [Complex.mk_eq_add_mul_I] <;> fun_prop
        continuous_invFun := by
          apply Continuous.subtype_mk
          fun_prop }
    refine ⟨d, ?_, ?_, fun _ ↦ rfl⟩
    · apply Complex.ext <;> cases upper <;> norm_num [d, f]
    · apply Complex.ext <;> cases upper <;> norm_num [d, f]
  obtain ⟨a, ha, ha0, ha1, hacover, haoverlap⟩ :
      ∃ a : unitInterval → ℂ, Topology.IsEmbedding a ∧ a 0 = p ∧ a 1 = q ∧
        range b ∪ range a = c ∧ range b ∩ range a = {p, q} := by
    have hsymm : Function.Surjective unitInterval.symm :=
      unitInterval.symmHomeomorph.surjective
    rcases hseam with hs | hs
    · refine ⟨e₃ ∘ unitInterval.symm, he₃.comp unitInterval.symmHomeomorph.isEmbedding,
        ?_, ?_, ?_, ?_⟩
      · simpa using h1₃
      · simpa using h0₃
      · simpa only [hs, range_comp, hsymm.range_eq,
          image_univ] using hcover
      · simpa only [hs, range_comp, hsymm.range_eq,
          image_univ] using hintersect
    · exact ⟨e₂, he₂, h0₂, h1₂, by rw [hs, union_comm, hcover],
        by rw [hs, inter_comm, hintersect]⟩
  have hcross (t u : unitInterval) : b t = a u ↔
      (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1) := by
    constructor
    · intro h
      have hmem : b t ∈ ({p, q} : Set ℂ) := by
        rw [← haoverlap]
        exact ⟨mem_range_self t, h ▸ mem_range_self u⟩
      rcases hmem with hmem | hmem
      · exact Or.inl ⟨hb.injective (hmem.trans h0.symm),
          ha.injective (h.symm.trans (hmem.trans ha0.symm))⟩
      · exact Or.inr ⟨hb.injective (hmem.trans h1.symm),
          ha.injective (h.symm.trans (hmem.trans ha1.symm))⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact h0.trans ha0.symm
      · exact h1.trans ha1.symm
  have hfront : frontier (cairnsClosedHalfDisk upper) = cairnsUnitDiameter ∪ S := by
    have hclosed : IsClosed (cairnsClosedHalfDisk upper) := by
      cases upper with
      | false =>
          exact isClosed_closedBall.inter
            (isClosed_le Complex.continuous_im continuous_const)
      | true =>
          exact isClosed_closedBall.inter
            (isClosed_le continuous_const Complex.continuous_im)
    have hi : interior (cairnsClosedHalfDisk upper) = ball (0 : ℂ) 1 ∩
        if upper then {z : ℂ | 0 < z.im} else {z : ℂ | z.im < 0} := by
      cases upper with
      | false =>
          change interior (closedBall (0 : ℂ) 1 ∩ Complex.im ⁻¹' Iic 0) = _
          rw [interior_inter, interior_closedBall _ one_ne_zero,
            Complex.interior_preimage_im, interior_Iic]
          rfl
      | true =>
          change interior (closedBall (0 : ℂ) 1 ∩ Complex.im ⁻¹' Ici 0) = _
          rw [interior_inter, interior_closedBall _ one_ne_zero,
            Complex.interior_preimage_im, interior_Ici]
          rfl
    rw [hclosed.frontier_eq, hi]
    ext z
    cases upper <;>
      simp only [cairnsClosedHalfDisk, cairnsUnitDiameter, S, Bool.false_eq_true,
        ↓reduceIte, mem_sdiff, mem_inter_iff, mem_union, mem_ofPred_eq,
        mem_closedBall, mem_ball, mem_sphere, dist_zero_right] <;> grind
  obtain ⟨d, hd⟩ := cairns_halfdisk_diameter_homeomorph
  obtain ⟨s, hs0, hs1, hsre⟩ := hsemicircle
  have hd0 : (d 0 : ℂ) = -1 := by simpa using hd 0
  have hd1 : (d 1 : ℂ) = 1 := by simpa using (hd 1).trans (by norm_num)
  have htargetcross (t u : unitInterval) : (d t : ℂ) = (s u : ℂ) ↔
      (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1) := by
    constructor
    · intro h
      have hr : 2 * (t : ℝ) - 1 = 2 * (u : ℝ) - 1 := by
        have hh := congrArg Complex.re h
        rw [hd, Complex.ofReal_re, hsre] at hh
        exact hh
      have htu : t = u := Subtype.ext (by linarith)
      subst u
      have hnorm : ‖(d t : ℂ)‖ = 1 := by
        rw [h]
        simpa only [mem_sphere, dist_zero_right] using (s t).property.1
      rw [hd, Complex.norm_real, Real.norm_eq_abs] at hnorm
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hnorm with hpos | hneg
      · right
        have ht : t = 1 := Subtype.ext (by change (t : ℝ) = 1; linarith)
        exact ⟨ht, ht⟩
      · left
        have ht : t = 0 := Subtype.ext (by change (t : ℝ) = 0; linarith)
        exact ⟨ht, ht⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hd0.trans hs0.symm
      · exact hd1.trans hs1.symm
  have haC (t : unitInterval) : a t ∈ c := by
    rw [← hacover]
    exact Or.inr (mem_range_self t)
  have hdF (t : unitInterval) : (d t : ℂ) ∈ frontier (cairnsClosedHalfDisk upper) := by
    exact cairns_halfdisk_diameter_subset_frontier upper (d t).property
  have hsF (t : unitInterval) : (s t : ℂ) ∈ frontier (cairnsClosedHalfDisk upper) := by
    rw [hfront]
    exact Or.inr (s t).property
  let f : C(unitInterval ⊕ unitInterval, c) :=
    ⟨Sum.elim (fun t ↦ ⟨b t, hB (mem_range_self t)⟩) (fun t ↦ ⟨a t, haC t⟩),
      continuous_sum_dom.mpr
        ⟨hb.continuous.subtype_mk _, ha.continuous.subtype_mk _⟩⟩
  let g : C(unitInterval ⊕ unitInterval, frontier (cairnsClosedHalfDisk upper)) :=
    ⟨Sum.elim (fun t ↦ ⟨d t, hdF t⟩) (fun t ↦ ⟨s t, hsF t⟩),
      continuous_sum_dom.mpr
        ⟨d.continuous.subtype_val.subtype_mk _, s.continuous.subtype_val.subtype_mk _⟩⟩
  have hf_surj : Function.Surjective f := by
    intro z
    have hz : (z : ℂ) ∈ range b ∪ range a := hacover ▸ z.property
    rcases hz with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨Sum.inl t, Subtype.ext ht⟩
    · exact ⟨Sum.inr t, Subtype.ext ht⟩
  have hg_surj : Function.Surjective g := by
    intro z
    have hz : (z : ℂ) ∈ cairnsUnitDiameter ∪ S := hfront ▸ z.property
    rcases hz with hz | hz
    · obtain ⟨t, ht⟩ := d.surjective ⟨z, hz⟩
      exact ⟨Sum.inl t, Subtype.ext (congrArg (fun w : cairnsUnitDiameter ↦ (w : ℂ)) ht)⟩
    · obtain ⟨t, ht⟩ := s.surjective ⟨z, hz⟩
      exact ⟨Sum.inr t, Subtype.ext (congrArg (fun w : S ↦ (w : ℂ)) ht)⟩
  have hker (x y : unitInterval ⊕ unitInterval) : f x = f y ↔ g x = g y := by
    cases x with
    | inl t =>
        cases y with
        | inl u =>
            change (⟨b t, _⟩ : c) = ⟨b u, _⟩ ↔
              (⟨(d t : ℂ), _⟩ : frontier _) = ⟨(d u : ℂ), _⟩
            simp only [Subtype.mk.injEq, hb.injective.eq_iff]
            exact ⟨fun h ↦ congrArg (fun t ↦ (d t : ℂ)) h,
              fun h ↦ d.injective (Subtype.ext h)⟩
        | inr u =>
            change (⟨b t, _⟩ : c) = ⟨a u, _⟩ ↔
              (⟨(d t : ℂ), _⟩ : frontier _) = ⟨(s u : ℂ), _⟩
            simp only [Subtype.mk.injEq]
            exact (hcross t u).trans (htargetcross t u).symm
    | inr t =>
        cases y with
        | inl u =>
            change (⟨a t, _⟩ : c) = ⟨b u, _⟩ ↔
              (⟨(s t : ℂ), _⟩ : frontier _) = ⟨(d u : ℂ), _⟩
            simp only [Subtype.mk.injEq]
            exact eq_comm.trans ((hcross u t).trans ((htargetcross u t).symm.trans eq_comm))
        | inr u =>
            change (⟨a t, _⟩ : c) = ⟨a u, _⟩ ↔
              (⟨(s t : ℂ), _⟩ : frontier _) = ⟨(s u : ℂ), _⟩
            simp only [Subtype.mk.injEq, ha.injective.eq_iff]
            exact ⟨fun h ↦ congrArg (fun t ↦ (s t : ℂ)) h,
              fun h ↦ s.injective (Subtype.ext h)⟩
  have hquot : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous hf_surj f.continuous
  let h : C(c, frontier (cairnsClosedHalfDisk upper)) :=
    hquot.lift g (fun {x y} hxy ↦ (hker x y).mp hxy)
  have hfg (x : unitInterval ⊕ unitInterval) : h (f x) = g x :=
    congrArg (fun k : C(unitInterval ⊕ unitInterval, frontier (cairnsClosedHalfDisk upper)) ↦ k x)
      (hquot.lift_comp g (fun {x y} hxy ↦ (hker x y).mp hxy))
  have hbij : Function.Bijective h := by
    constructor
    · intro z w hzw
      obtain ⟨x, rfl⟩ := hf_surj z
      obtain ⟨y, rfl⟩ := hf_surj w
      apply (hker x y).mpr
      simpa only [hfg] using hzw
    · intro z
      obtain ⟨x, rfl⟩ := hg_surj z
      exact ⟨f x, hfg x⟩
  let : CompactSpace c := isCompact_univ_iff.mp (by
    rw [← hf_surj.range_eq]
    exact isCompact_range f.continuous)
  let H : c ≃ₜ frontier (cairnsClosedHalfDisk upper) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective h hbij) h.continuous
  refine ⟨H, ?_⟩
  intro t
  exact (congrArg Subtype.val (hfg (Sum.inl t))).trans (hd t)

end HolomorphicAnosov.Topology
