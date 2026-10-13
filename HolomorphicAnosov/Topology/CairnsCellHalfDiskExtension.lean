import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.UnitInterval
import HolomorphicAnosov.Topology.WhyburnCircleSplit
import HolomorphicAnosov.Topology.CairnsHalfDiskBoundaryTransport

open Set Metric

namespace HolomorphicAnosov.Topology

/-!
The source statement is Cairns, *An Elementary Proof of the Jordan--Schoenflies
Theorem* (1951), §4(D), equation (4.5), pp.865--866.  Cairns states the
amalgamation corollary but suppresses the half-disk chart construction.  The
following named obligation isolates that construction for reuse by the
relative-chart parent.

Given one disk-cell chart and its prescribed-boundary extension property,
restrict the chart to the boundary and split the circle at the endpoints of
the proper embedded seam.  The seam arc is sent monotonically to the diameter
parameter `2 t - 1`; the complementary arc is sent to the upper (respectively
lower) semicircle.  Closed-pair pasting gives a boundary homeomorphism onto the
boundary of `cairnsClosedHalfDisk upper`.  The convex-body normalization of a
closed half-disk followed by the supplied prescribed-boundary extension gives
the required chart on the whole cell.  The ball/sphere image equations force
the open cell to map to the half-disk interior and the boundary to its
frontier.  The endpoint and properness hypotheses exclude a collapsed seam.

The printed Cairns pages provide the construction and extension principle, while
the exact subtype/pasting bookkeeping is not printed.  The theorem is intentionally named so the
remaining proof can be completed independently without weakening the parent
statement.
-/
theorem cairns_cell_halfdisk_extension
    (upper : Bool) (U c B : Set ℂ) (p q : ℂ)
    (hc : c ⊆ closure U)
    (hcell : ∃ H : closure U ≃ₜ closedBall (0 : ℂ) 1,
      H '' {z | (z : ℂ) ∈ U} = {w | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
      H '' {z | (z : ℂ) ∈ c} = {w | (w : ℂ) ∈ sphere (0 : ℂ) 1})
    (hext : ∀ h : c ≃ₜ sphere (0 : ℂ) 1,
      ∃ H : closure U ≃ₜ closedBall (0 : ℂ) 1,
        ∀ z : closure U, ∀ hz : (z : ℂ) ∈ c,
          (H z : ℂ) = (h ⟨(z : ℂ), hz⟩ : ℂ))
    (hpq : p ≠ q)
    (b : unitInterval → ℂ) (hb : Topology.IsEmbedding b)
    (hrange : range b = B) (h0 : b 0 = p) (h1 : b 1 = q)
    (hproper : B ⊆ c ∧ B ≠ c) :
    ∃ H : closure U ≃ₜ cairnsClosedHalfDisk upper,
      H '' {z : closure U | (z : ℂ) ∈ U} =
        {w : cairnsClosedHalfDisk upper |
          (w : ℂ) ∈ interior (cairnsClosedHalfDisk upper)} ∧
      H '' {z : closure U | (z : ℂ) ∈ c} =
        {w : cairnsClosedHalfDisk upper |
          (w : ℂ) ∈ frontier (cairnsClosedHalfDisk upper)} ∧
      ∀ t : unitInterval,
        ((H ⟨b t, hc (hproper.1 (hrange ▸ mem_range_self t))⟩ :
          cairnsClosedHalfDisk upper) : ℂ) =
          ((2 * (t : ℝ) - 1 : ℝ) : ℂ) := by
  obtain ⟨H₀, hU, hC⟩ := hcell
  have hUi (z : closure U) : (z : ℂ) ∈ U ↔ (H₀ z : ℂ) ∈ ball (0 : ℂ) 1 := by
    have him : (fun w : closure U ↦ (H₀ w : ℂ)) '' {w : closure U | (w : ℂ) ∈ U} =
        ball (0 : ℂ) 1 := by
      ext x
      simpa only [image_image, mem_ofPred_eq] using Set.ext_iff.mp hU x
    rw [← him]
    exact ⟨fun hz ↦ ⟨z, hz, rfl⟩,
      fun ⟨w, hw, he⟩ ↦ H₀.injective (Subtype.ext he) ▸ hw⟩
  have hCi (z : closure U) : (z : ℂ) ∈ c ↔ (H₀ z : ℂ) ∈ sphere (0 : ℂ) 1 := by
    have him : (fun w : closure U ↦ (H₀ w : ℂ)) '' {w : closure U | (w : ℂ) ∈ c} =
        sphere (0 : ℂ) 1 := by
      ext x
      simpa only [image_image, mem_ofPred_eq] using Set.ext_iff.mp hC x
    rw [← him]
    exact ⟨fun hz ↦ ⟨z, hz, rfl⟩,
      fun ⟨w, hw, he⟩ ↦ H₀.injective (Subtype.ext he) ▸ hw⟩
  let e : c ≃ₜ sphere (0 : ℂ) 1 :=
    { toFun := fun z ↦ ⟨H₀ ⟨z, hc z.property⟩, (hCi _).mp z.property⟩
      invFun := fun w ↦ ⟨H₀.symm ⟨w, sphere_subset_closedBall w.property⟩,
        (hCi _).mpr (by simpa only [H₀.apply_symm_apply] using w.property)⟩
      left_inv := by
        intro z
        apply Subtype.ext
        change (H₀.symm (H₀ ⟨z, hc z.property⟩) : ℂ) = z
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        change (H₀ (H₀.symm ⟨w, sphere_subset_closedBall w.property⟩) : ℂ) = w
        simp
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (H₀.continuous.comp
          (continuous_subtype_val.subtype_mk (fun z ↦ hc z.property))).subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (H₀.symm.continuous.comp
          (continuous_subtype_val.subtype_mk
            (fun w : sphere (0 : ℂ) 1 ↦ sphere_subset_closedBall w.property))).subtype_val }
  obtain ⟨hboundary, hboundary_seam⟩ := cairns_halfdisk_boundary_transport
    upper c B p q e hpq b hb hrange h0 h1 hproper
  have hclosure : closure U = U ∪ c := by
    apply Subset.antisymm
    · intro z hz
      rcases lt_or_eq_of_le (mem_closedBall.mp (H₀ ⟨z, hz⟩).property) with hlt | heq
      · exact Or.inl ((hUi ⟨z, hz⟩).mpr hlt)
      · exact Or.inr ((hCi ⟨z, hz⟩).mpr heq)
    · exact union_subset subset_closure hc
  have hdisjoint : Disjoint U c := by
    rw [Set.disjoint_left]
    intro z hzU hzc
    have hlt := (hUi ⟨z, subset_closure hzU⟩).mp hzU
    have heq := (hCi ⟨z, subset_closure hzU⟩).mp hzc
    exact (ne_of_lt hlt) heq
  have hconv : Convex ℝ (cairnsClosedHalfDisk upper) := by
    cases upper with
    | false =>
        simp only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte]
        exact (convex_closedBall (0 : ℂ) 1).inter
          ((convex_Iic (0 : ℝ)).is_linear_preimage Complex.imLm.isLinear)
    | true =>
        simp only [cairnsClosedHalfDisk, ↓reduceIte]
        exact (convex_closedBall (0 : ℂ) 1).inter
          ((convex_Ici (0 : ℝ)).is_linear_preimage Complex.imLm.isLinear)
  have hne : (interior (cairnsClosedHalfDisk upper)).Nonempty := by
    cases upper with
    | false =>
        simp only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte]
        rw [interior_inter, interior_closedBall]
        change (ball (0 : ℂ) 1 ∩ interior (Complex.im ⁻¹' Iic (0 : ℝ))).Nonempty
        rw [Complex.interior_preimage_im, interior_Iic]
        exact ⟨(-Complex.I / 2 : ℂ), by norm_num⟩
        all_goals norm_num
    | true =>
        simp only [cairnsClosedHalfDisk, ↓reduceIte]
        rw [interior_inter, interior_closedBall]
        change (ball (0 : ℂ) 1 ∩ interior (Complex.im ⁻¹' Ici (0 : ℝ))).Nonempty
        rw [Complex.interior_preimage_im, interior_Ici]
        exact ⟨(Complex.I / 2 : ℂ), by norm_num⟩
        all_goals norm_num
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
  have hfrontierFalse : frontier (cairnsClosedHalfDisk false) =
      cairnsUnitDiameter ∪ {z : ℂ | z ∈ sphere (0 : ℂ) 1 ∧ z.im ≤ 0} := by
    have hc : IsClosed (cairnsClosedHalfDisk false) := by
      simp only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte]
      exact isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const)
    have hi : interior (cairnsClosedHalfDisk false) =
        ball (0 : ℂ) 1 ∩ {z : ℂ | z.im < 0} := by
      simp only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte]
      rw [interior_inter, interior_closedBall]
      change ball (0 : ℂ) 1 ∩ interior (Complex.im ⁻¹' Iic (0 : ℝ)) = _
      rw [Complex.interior_preimage_im, interior_Iic]
      ext z; rfl
      all_goals norm_num
    rw [hc.frontier_eq, hi]
    ext z
    simp only [cairnsClosedHalfDisk, cairnsUnitDiameter, Bool.false_eq_true, ↓reduceIte,
      mem_sdiff, mem_inter_iff, mem_ball, mem_closedBall, mem_ofPred_eq, mem_union,
      mem_sphere, dist_zero_right]
    constructor
    · rintro ⟨⟨hz,hz_im⟩, hn⟩
      rcases lt_or_eq_of_le hz with hlt | heq
      · left
        refine ⟨hz, ?_⟩
        have : ¬z.im < 0 := by
          intro hneg
          exact hn ⟨hlt,hneg⟩
        exact le_antisymm hz_im (le_of_not_gt this)
      · right
        exact ⟨heq, hz_im⟩
    · rintro (hz | ⟨hz,hz_im⟩)
      · rcases hz with ⟨hz,hz_im⟩
        refine ⟨⟨hz, le_of_eq hz_im⟩, ?_⟩
        intro h
        exact (not_lt_of_ge (le_of_eq hz_im.symm)) h.2
      · refine ⟨⟨le_of_eq hz, hz_im⟩, ?_⟩
        intro h
        linarith [hz, h.1]
  have hfrontierTrue : frontier (cairnsClosedHalfDisk true) =
      cairnsUnitDiameter ∪ {z : ℂ | z ∈ sphere (0 : ℂ) 1 ∧ 0 ≤ z.im} := by
    have hc : IsClosed (cairnsClosedHalfDisk true) := by
      simp only [cairnsClosedHalfDisk, ↓reduceIte]
      exact isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)
    have hi : interior (cairnsClosedHalfDisk true) =
        ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < z.im} := by
      simp only [cairnsClosedHalfDisk, ↓reduceIte]
      rw [interior_inter, interior_closedBall]
      change ball (0 : ℂ) 1 ∩ interior (Complex.im ⁻¹' Ici (0 : ℝ)) = _
      rw [Complex.interior_preimage_im, interior_Ici]
      ext z; rfl
      all_goals norm_num
    rw [hc.frontier_eq, hi]
    ext z
    simp only [cairnsClosedHalfDisk, cairnsUnitDiameter, ↓reduceIte,
      mem_sdiff, mem_inter_iff, mem_ball, mem_closedBall, mem_ofPred_eq, mem_union,
      mem_sphere, dist_zero_right]
    constructor
    · rintro ⟨⟨hz,hz_im⟩, hn⟩
      rcases lt_or_eq_of_le hz with hlt | heq
      · left
        refine ⟨hz, ?_⟩
        have : ¬0 < z.im := by
          intro hpos
          exact hn ⟨hlt,hpos⟩
        exact le_antisymm (le_of_not_gt this) hz_im
      · right
        exact ⟨heq, hz_im⟩
    · rintro (hz | ⟨hz,hz_im⟩)
      · rcases hz with ⟨hz,hz_im⟩
        refine ⟨⟨hz, le_of_eq hz_im.symm⟩, ?_⟩
        intro h
        exact (not_lt_of_ge (le_of_eq hz_im)) h.2
      · refine ⟨⟨le_of_eq hz, hz_im⟩, ?_⟩
        intro h
        linarith [hz, h.1]
  have hclosed : IsClosed (cairnsClosedHalfDisk upper) := by
    cases upper with
    | false =>
        simp only [cairnsClosedHalfDisk, Bool.false_eq_true, ↓reduceIte]
        exact isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const)
    | true =>
        simp only [cairnsClosedHalfDisk, ↓reduceIte]
        exact isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)
  have hbounded : Bornology.IsBounded (cairnsClosedHalfDisk upper) :=
    Metric.isBounded_closedBall.subset inter_subset_left
  obtain ⟨N, hNint, hNclosure, hNfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbounded
  let n : cairnsClosedHalfDisk upper ≃ₜ closedBall (0 : ℂ) 1 :=
    { toFun := fun z ↦ ⟨N z, by
          have hz : (z : ℂ) ∈ closure (cairnsClosedHalfDisk upper) := by
            rw [hclosed.closure_eq]
            exact z.property
          rw [← hNclosure]
          exact ⟨z, hz, rfl⟩⟩
      invFun := fun w ↦ ⟨N.symm w, by
          have hw : (w : ℂ) ∈ N '' closure (cairnsClosedHalfDisk upper) := by
            rw [hNclosure]
            exact w.property
          rcases hw with ⟨z, hz, heq⟩
          have hz' : N.symm (w : ℂ) = z := by
            rw [← heq, N.symm_apply_apply]
          rw [hz']
          exact hclosed.closure_eq ▸ hz⟩
      left_inv := by
        intro z
        apply Subtype.ext
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        simp
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact N.continuous.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact N.symm.continuous.comp continuous_subtype_val }
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
  let seam : B ≃ₜ cairnsUnitDiameter :=
    ((Homeomorph.setCongr hrange).symm.trans hb.toHomeomorph.symm).trans d
  have hseam (t : unitInterval) :
      (seam ⟨b t, hrange ▸ mem_range_self t⟩ : ℂ) =
        ((2 * (t : ℝ) - 1 : ℝ) : ℂ) := by
    simp [seam, d]
    have hset : (Homeomorph.setCongr hrange).symm
        ⟨b t, hrange ▸ mem_range_self t⟩ = ⟨b t, mem_range_self t⟩ := by
      apply Subtype.ext
      rfl
    rw [hset]
    have hforward : hb.toHomeomorph t = ⟨b t, mem_range_self t⟩ := by
      rfl
    rw [← hforward]
    exact congrArg Subtype.val (hb.toHomeomorph.symm_apply_apply t)
  let nF : frontier (cairnsClosedHalfDisk upper) ≃ₜ sphere (0 : ℂ) 1 :=
    { toFun := fun z =>
        ⟨N z, by
          rw [← hNfrontier]
          exact ⟨z, z.property, rfl⟩⟩
      invFun := fun w =>
        ⟨N.symm w, by
          have hw : (w : ℂ) ∈ N '' frontier (cairnsClosedHalfDisk upper) := by
            rw [hNfrontier]
            exact w.property
          rcases hw with ⟨z, hz, hzw⟩
          have heq : N.symm (w : ℂ) = z := by
            rw [← hzw, N.symm_apply_apply]
          rw [heq]
          exact hz⟩
      left_inv := by
        intro z
        apply Subtype.ext
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        simp
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact N.continuous.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact N.symm.continuous.comp continuous_subtype_val }
  obtain ⟨E, hE⟩ := hext (hboundary.trans nF)
  let H : closure U ≃ₜ cairnsClosedHalfDisk upper := E.trans n.symm
  have hH (z : closure U) (hz : (z : ℂ) ∈ c) :
      (H z : ℂ) = (hboundary ⟨z, hz⟩ : ℂ) := by
    change N.symm (E z : ℂ) = _
    rw [hE z hz]
    exact N.symm_apply_apply _
  have hHC (z : closure U) : (z : ℂ) ∈ c ↔
      (H z : ℂ) ∈ frontier (cairnsClosedHalfDisk upper) := by
    constructor
    · intro hz
      rw [hH z hz]
      exact (hboundary ⟨z, hz⟩).property
    · intro hz
      let w : c := hboundary.symm ⟨H z, hz⟩
      have hw : H ⟨w, hc w.property⟩ = H z := by
        apply Subtype.ext
        rw [hH _ w.property]
        exact congrArg Subtype.val (hboundary.apply_symm_apply ⟨H z, hz⟩)
      have heq := congrArg Subtype.val (H.injective hw)
      exact heq ▸ w.property
  have hHU (z : closure U) : (z : ℂ) ∈ U ↔
      (H z : ℂ) ∈ interior (cairnsClosedHalfDisk upper) := by
    have hcU : (z : ℂ) ∈ U ↔ (z : ℂ) ∉ c := by
      constructor
      · exact fun hz hz' => Set.disjoint_left.mp hdisjoint hz hz'
      · intro hz
        have hzcl : (z : ℂ) ∈ U ∪ c := by rw [← hclosure]; exact z.property
        rcases hzcl with h | h
        · exact h
        · exact False.elim (hz h)
    rw [hcU, hHC, hclosed.frontier_eq]
    change ¬ ((H z : ℂ) ∈ cairnsClosedHalfDisk upper ∧
      (H z : ℂ) ∉ interior (cairnsClosedHalfDisk upper)) ↔ _
    simp only [(H z).property, true_and, not_not]
  refine ⟨H, ?_, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hHU z).mp hz
    · intro hw
      exact ⟨H.symm w, (hHU _).mpr (by simpa using hw), H.apply_symm_apply w⟩
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hHC z).mp hz
    · intro hw
      exact ⟨H.symm w, (hHC _).mpr (by simpa using hw), H.apply_symm_apply w⟩
  · intro t
    rw [hH _ (hproper.1 (hrange ▸ mem_range_self t))]
    exact hboundary_seam t

end HolomorphicAnosov.Topology

