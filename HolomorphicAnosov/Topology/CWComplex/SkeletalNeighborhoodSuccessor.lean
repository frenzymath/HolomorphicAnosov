import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Homotopy.Basic

/-!
# One skeletal extension of an open neighborhood with a closed buffer

This public theorem is proposed for `topo.cw_skeletal_neighborhood_successor_g1`.
It is extracted from the proof of `topo.cw_contractible_open_neighborhoods`.
-/

namespace HolomorphicAnosov

/-- Extend a relatively open neighborhood and its ambient closed buffer across
one layer of cells, with a radial retraction, endpoint and fixed-point identities,
and continuity on every characteristic prism.

Source: Hatcher, *Algebraic Topology*, Appendix, the radial neighborhood construction
and Proposition A.4, printed p.522; characteristic homotopy continuity, p.523.
The strengthened buffer and characteristic-prism interface is an agent-written
explication of the compactness and continuity steps compressed in that proof.
It does not assume continuity of a characteristic map outside its closed disk.

Proof. For each (m+1)-cell, pull the closed buffer back to its boundary sphere.
This is compact. Scalar multiplication on the unit interval times this compact
set and compact eventual-forall give a cell-dependent width strictly between
zero and one half whose closed radial collar maps into O. The boundary preimage
of the old open set is relatively open and lies in this compact boundary set.
Take the union of its open radial collar with the old open set; use the compact
closed collar over the buffer for the new buffer. Disjoint open cells and the
fact that their frontiers lie in the previous skeleton prove the exact old-
skeleton intersections and characteristic preimage formulas. In positive-radius
coordinates, these preimages are relatively open or compact closed, respectively.
The inherited CW closed-cell criterion gives relative openness of the new open
set and ambient closedness of the buffer.

Fix the old open set. On a new collar point r theta, send it to the attaching
point theta for the retraction and to ((1-t)r+t) theta for the deformation.
Cell-interior uniqueness makes this prescription independent of representatives;
on the boundary the formula is the identity. The cutoff max(1-width,norm z)
provides a continuous whole-disk radial formula, agreeing with the desired formula
on the collar and with the identity at the boundary. Consequently each inherited
characteristic prism has a continuous pullback, including all attaching points.
The formulas prove the endpoints and fix the old set throughout. If the assembled
deformation is continuous, its time-one evaluation is a continuous retraction
into the old subtype, and the same deformation bundles as HomotopyRel. This last
implication exposes the separate quotient-descent input required by the consumer.
-/
theorem cw_skeletal_neighborhood_successor
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (x : X) (O : Set X) (hO : IsOpen O)
    (m : ℕ) (V₀ C₀ : Set X)
    (hstage : V₀ ⊆ C₀ ∧ C₀ ⊆ O ∧ C₀ ⊆
      (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1) : Set X) ∧
      IsOpen {y : Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1) |
        y.val ∈ V₀} ∧ IsClosed C₀ ∧ x ∈ V₀) :
    ∃ (A B : Set X) (hVA : V₀ ⊆ A),
      (A ⊆ B ∧ B ⊆ O ∧ B ⊆
      (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) ((m + 1 : ℕ) + 1) : Set X) ∧
      IsOpen {y : Topology.RelCWComplex.skeletonLT (Set.univ : Set X) ((m + 1 : ℕ) + 1) |
        y.val ∈ A} ∧ IsClosed B ∧ x ∈ A) ∧ C₀ ⊆ B ∧
      A ∩ (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1) : Set X) = V₀ ∧ B ∩ (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1) : Set X) = C₀ ∧
      ∃ (R : A → V₀) (H : unitInterval × A → A),
        (∀ y : V₀, R ⟨y.val, hVA y.property⟩ = y) ∧
        (∀ y, H (0, y) = y) ∧ (∀ y, (H (1, y)).val = (R y).val) ∧
        (∀ t (y : A), y.val ∈ V₀ → H (t, y) = y) ∧
        (∀ n (i : Topology.RelCWComplex.cell (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 2) : Set X) n),
          Continuous (fun p : unitInterval ×
              {z : Metric.closedBall (0 : Fin n → ℝ) 1 //
                Topology.RelCWComplex.map n i z.val ∈ A} ↦
            H (p.1, ⟨Topology.RelCWComplex.map n i p.2.val.val, p.2.property⟩))) ∧
        (Continuous H → ∃ r : C(A, V₀),
          (∀ y, r y = R y) ∧
          r.comp (ContinuousMap.inclusion hVA) = ContinuousMap.id V₀ ∧
          Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id A)
            ((ContinuousMap.inclusion hVA).comp r) {y : A | y.val ∈ V₀})) := by
  classical
  let Stage : ℕ → Set X → Set X → Prop := fun n A B ↦
    A ⊆ B ∧ B ⊆ O ∧ B ⊆
      (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (n + 1) : Set X) ∧
    IsOpen {y : Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (n + 1) |
      y.val ∈ A} ∧ IsClosed B ∧ x ∈ A
  obtain ⟨hV₀C₀, hC₀O, hC₀skeleton, hV₀openInSkeleton, hC₀closed, hxV₀⟩ := hstage
  let S := Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 1)
  have hV₀skeleton : V₀ ⊆ (S : Set X) := hV₀C₀.trans hC₀skeleton
  -- The first higher-dimensional cell sees a compact boundary part above the buffer.
  let boundaryBuffer (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) :
      Set (Fin (m + 1) → ℝ) :=
    Metric.sphere 0 1 ∩ Topology.RelCWComplex.map (m + 1) j ⁻¹' C₀
  have hboundaryBuffer_compact
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) :
      IsCompact (boundaryBuffer j) := by
    apply (isCompact_sphere 0 1).of_isClosed_subset
    · exact ((Topology.RelCWComplex.continuousOn (m + 1) j).mono
        Metric.sphere_subset_closedBall).preimage_isClosed_of_isClosed
          Metric.isClosed_sphere hC₀closed
    · exact Set.inter_subset_left
  let closedCollar (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) (δ : ℝ) :
      Set (Fin (m + 1) → ℝ) :=
    (fun p : ℝ × (Fin (m + 1) → ℝ) ↦ p.1 • p.2) ''
      (Set.Icc (1 - δ) 1 ×ˢ boundaryBuffer j)
  have hclosedCollar_compact
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) (δ : ℝ) :
      IsCompact (closedCollar j δ) :=
    (isCompact_Icc.prod (hboundaryBuffer_compact j)).image
      (continuous_fst.smul continuous_snd)
  have hclosedCollar_disk
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (δ : ℝ) (hδ : δ < 1) : closedCollar j δ ⊆ Metric.closedBall 0 1 := by
    rintro _ ⟨⟨t, θ⟩, ⟨ht, hθ⟩, rfl⟩
    have hθnorm : ‖θ‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hθ.1
    have ht0 : 0 ≤ t := le_trans (sub_nonneg.mpr hδ.le) ht.1
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht0, hθnorm, mul_one] using ht.2
  have hclosedCollar_image_closed
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (δ : ℝ) (hδ : δ < 1) :
      IsClosed (Topology.RelCWComplex.map (m + 1) j '' closedCollar j δ) :=
    ((hclosedCollar_compact j δ).image_of_continuousOn
      ((Topology.RelCWComplex.continuousOn (m + 1) j).mono
        (hclosedCollar_disk j δ hδ))).isClosed
  have hclosedCollar_boundary
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
      closedCollar j δ ∩ Metric.sphere 0 1 = boundaryBuffer j := by
    ext z
    constructor
    · rintro ⟨⟨⟨t, θ⟩, ⟨ht, hθ⟩, rfl⟩, hz⟩
      have hθnorm : ‖θ‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hθ.1
      have ht0 : 0 ≤ t := le_trans (sub_nonneg.mpr hδ1.le) ht.1
      have ht1 : t = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ht0, hθnorm, mul_one] using hz
      simpa only [ht1, one_smul] using hθ
    · intro hz
      refine ⟨⟨⟨1, z⟩, ⟨⟨?_, le_rfl⟩, hz⟩, one_smul ℝ z⟩, hz.1⟩
      exact sub_le_self 1 hδ0
  have hcollar_width (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) :
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
        Topology.RelCWComplex.map (m + 1) j '' closedCollar j δ ⊆ O := by
    let B := boundaryBuffer j
    let : CompactSpace B := isCompact_iff_compactSpace.mp (hboundaryBuffer_compact j)
    let radial : unitInterval × B → Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 :=
      fun p ↦ ⟨(p.1 : ℝ) • p.2.val, by
        have hn : ‖p.2.val‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property.1
        simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg p.1.property.1, hn, mul_one] using p.1.property.2⟩
    have hradial : Continuous radial :=
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    let F : unitInterval × B → X := fun p ↦
      Topology.RelCWComplex.map (m + 1) j (radial p).val
    have hF : Continuous F :=
      (Topology.RelCWComplex.continuousOn (m + 1) j).domRestrict.comp hradial
    have hP : ∀ θ ∈ (Set.univ : Set B),
        Filter.Eventually (fun p ↦ F p ∈ O) (nhds ((1 : unitInterval), θ)) := by
      intro θ _
      exact hF.continuousAt.preimage_mem_nhds (hO.mem_nhds
        (by simpa [F, radial] using hC₀O θ.property.2))
    have hev : Filter.Eventually (fun r : unitInterval ↦ ∀ θ ∈ (Set.univ : Set B),
        F (r, θ) ∈ O) (nhds (1 : unitInterval)) :=
      isCompact_univ.eventually_forall_of_forall_eventually hP
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev
    let δ := min (ε / 2) (1 / 4 : ℝ)
    have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
    have hδhalf : δ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    refine ⟨δ, hδpos, hδhalf, ?_⟩
    rintro y ⟨_, ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩, rfl⟩
    have hr0 : 0 ≤ r := by linarith [hr.1]
    let t : unitInterval := ⟨r, hr0, hr.2⟩
    have hdist : dist t (1 : unitInterval) ≤ δ := by
      change dist r 1 ≤ δ
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hr.1, hr.2]
    have hmem : t ∈ Metric.ball (1 : unitInterval) ε := by
      rw [Metric.mem_ball]
      have hδε : δ ≤ ε / 2 := min_le_left _ _
      exact hdist.trans_lt (by linarith)
    exact hsub hmem ⟨θ, hθ⟩ (Set.mem_univ _)
  let boundaryOpen (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) :
      Set (Fin (m + 1) → ℝ) :=
    Metric.sphere 0 1 ∩ Topology.RelCWComplex.map (m + 1) j ⁻¹' V₀
  have hboundaryOpen_open
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) :
      IsOpen {z : Metric.sphere (0 : Fin (m + 1) → ℝ) 1 | z.val ∈ boundaryOpen j} := by
    let b : Metric.sphere (0 : Fin (m + 1) → ℝ) 1 → S :=
      fun z ↦ ⟨Topology.RelCWComplex.map (m + 1) j z,
        (Topology.RelCWComplex.cellFrontier_subset_skeletonLT (m + 1) j)
          ⟨z.1, z.2, rfl⟩⟩
    have hb : Continuous b :=
      ((Topology.RelCWComplex.continuousOn (m + 1) j).mono
        Metric.sphere_subset_closedBall).domRestrict.subtype_mk _
    have hpre := hV₀openInSkeleton.preimage hb
    have heq : b ⁻¹' {y : S | y.val ∈ V₀} =
        {z : Metric.sphere (0 : Fin (m + 1) → ℝ) 1 | z.val ∈ boundaryOpen j} := by
      ext z
      change Topology.RelCWComplex.map (m + 1) j z.val ∈ V₀ ↔
        z.val ∈ Metric.sphere 0 1 ∧ Topology.RelCWComplex.map (m + 1) j z.val ∈ V₀
      exact ⟨fun h ↦ ⟨z.property, h⟩, fun h ↦ h.2⟩
    rwa [heq] at hpre
  let openCollar (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) (δ : ℝ) :
      Set (Fin (m + 1) → ℝ) :=
    (fun p : ℝ × (Fin (m + 1) → ℝ) ↦ p.1 • p.2) ''
      (Set.Ioo (1 - δ) 1 ×ˢ boundaryOpen j)
  have hopenCollar_iff_radial
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) {z : Fin (m + 1) → ℝ} :
      z ∈ openCollar j δ ↔
        z ∈ Metric.ball 0 1 ∧ 1 - δ < ‖z‖ ∧
          (‖z‖⁻¹ • z) ∈ boundaryOpen j := by
    constructor
    · rintro ⟨⟨t, θ⟩, ⟨ht, hθ⟩, rfl⟩
      have hθnorm : ‖θ‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hθ.1
      have ht0 : 0 < t := lt_trans (sub_pos.mpr hδ1) ht.1
      have hnorm : ‖t • θ‖ = t := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hθnorm]
      refine ⟨?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, hnorm]
        exact ht.2
      · simpa [hnorm] using ht.1
      · change ‖t • θ‖⁻¹ • (t • θ) ∈ boundaryOpen j
        simpa only [hnorm, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul] using hθ
    · rintro ⟨hzball, hzδ, hzθ⟩
      have hz0 : 0 < ‖z‖ := lt_trans (sub_pos.mpr hδ1) hzδ
      refine ⟨⟨‖z‖, ‖z‖⁻¹ • z⟩, ⟨⟨hzδ, ?_⟩, hzθ⟩, ?_⟩
      · simpa only [Metric.mem_ball, dist_zero_right] using hzball
      · change ‖z‖ • (‖z‖⁻¹ • z) = z
        rw [smul_smul, mul_inv_cancel₀ hz0.ne', one_smul]
  have hboundary_union_collar_iff
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
      (z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1) :
      z.val ∈ boundaryOpen j ∪ openCollar j δ ↔
        1 - δ < ‖z.val‖ ∧ (‖z.val‖⁻¹ • z.val) ∈ boundaryOpen j := by
    constructor
    · rintro (hz | hz)
      · have hn : ‖z.val‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using hz.1
        refine ⟨?_, ?_⟩
        · rw [hn]
          exact sub_lt_self 1 hδ0
        · simpa only [hn, inv_one, one_smul] using hz
      · exact ((hopenCollar_iff_radial j δ hδ0 hδ1).mp hz).2
    · rintro ⟨hzn, hzθ⟩
      by_cases hzball : z.val ∈ Metric.ball 0 1
      · exact Or.inr ((hopenCollar_iff_radial j δ hδ0 hδ1).mpr ⟨hzball, hzn, hzθ⟩)
      · have hn : ‖z.val‖ = 1 := by
          have hnle : ‖z.val‖ ≤ 1 := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
          have hnge : 1 ≤ ‖z.val‖ := le_of_not_gt (by
            simpa only [Metric.mem_ball, dist_zero_right] using hzball)
          exact le_antisymm hnle hnge
        exact Or.inl (by simpa only [hn, inv_one, one_smul] using hzθ)
  have hboundary_union_collar_open
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
      IsOpen {z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 |
        z.val ∈ boundaryOpen j ∪ openCollar j δ} := by
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp (hboundaryOpen_open j)
    let A : Set (Fin (m + 1) → ℝ) := {z | 1 - δ < ‖z‖}
    have hA : IsOpen A := isOpen_lt continuous_const continuous_norm
    have hpositive : ∀ z ∈ A, ‖z‖ ≠ 0 :=
      fun z hz ↦ (lt_trans (sub_pos.mpr hδ1) hz).ne'
    have hnormalize : ContinuousOn (fun z : Fin (m + 1) → ℝ ↦ ‖z‖⁻¹ • z) A :=
      (continuous_norm.continuousOn.inv₀ hpositive).smul continuousOn_id
    have hW : IsOpen (A ∩ (fun z : Fin (m + 1) → ℝ ↦ ‖z‖⁻¹ • z) ⁻¹' U) :=
      hnormalize.isOpen_inter_preimage hA hU
    have heq : {z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 |
        z.val ∈ boundaryOpen j ∪ openCollar j δ} =
        (Subtype.val : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 → _) ⁻¹'
          (A ∩ (fun z : Fin (m + 1) → ℝ ↦ ‖z‖⁻¹ • z) ⁻¹' U) := by
      ext z
      rw [Set.mem_ofPred, hboundary_union_collar_iff j δ hδ0 hδ1]
      change (_ ∧ _) ↔ (1 - δ < ‖z.val‖ ∧ (‖z.val‖⁻¹ • z.val) ∈ U)
      apply and_congr_right
      intro hzn
      have hz0 : ‖z.val‖ ≠ 0 := (lt_trans (sub_pos.mpr hδ1) hzn).ne'
      have hθ : ‖z.val‖⁻¹ • z.val ∈ Metric.sphere 0 1 := by
        simp only [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hz0]
      have hmem := Set.ext_iff.mp hUeq (⟨‖z.val‖⁻¹ • z.val, hθ⟩ : Metric.sphere (0 : Fin (m + 1) → ℝ) 1)
      exact hmem.symm
    rw [heq]
    exact hW.preimage continuous_subtype_val
  have hopenCollar_closedCollar
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) (δ : ℝ) :
      openCollar j δ ⊆ closedCollar j δ := by
    apply Set.image_mono
    rintro ⟨t, θ⟩ ⟨ht, hθ⟩
    exact ⟨⟨ht.1.le, ht.2.le⟩, hθ.1, hV₀C₀ hθ.2⟩
  have hopenCollar_ball
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (δ : ℝ) (hδ1 : δ < 1) : openCollar j δ ⊆ Metric.ball 0 1 := by
    rintro _ ⟨⟨t, θ⟩, ⟨ht, hθ⟩, rfl⟩
    have hθnorm : ‖θ‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hθ.1
    have ht0 : 0 ≤ t := (lt_trans (sub_pos.mpr hδ1) ht.1).le
    simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht0, hθnorm, mul_one] using ht.2
  have hfirstCell_preimage
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (δ : ℝ) (hδ1 : δ < 1) :
      Metric.closedBall 0 1 ∩ Topology.RelCWComplex.map (m + 1) j ⁻¹'
        (V₀ ∪ Topology.RelCWComplex.map (m + 1) j '' openCollar j δ) =
      boundaryOpen j ∪ openCollar j δ := by
    let ψ := Topology.RelCWComplex.map (C := (Set.univ : Set X)) (m + 1) j
    have hd : Disjoint (S : Set X) (Topology.RelCWComplex.openCell (m + 1) j) :=
      Topology.RelCWComplex.disjoint_skeletonLT_openCell (le_refl _)
    have hsource : openCollar j δ ⊆ ψ.source := by
      rw [Topology.RelCWComplex.source_eq]
      exact hopenCollar_ball j δ hδ1
    ext z
    constructor
    · rintro ⟨hz, hzV | ⟨w, hw, hwz⟩⟩
      · left
        refine ⟨?_, hzV⟩
        rw [Metric.mem_sphere]
        apply le_antisymm hz
        apply le_of_not_gt
        intro hzball
        exact Set.disjoint_left.mp hd (hV₀skeleton hzV) ⟨z, hzball, rfl⟩
      · right
        have hzball : z ∈ Metric.ball 0 1 := by
          by_contra hnot
          have hzsphere : z ∈ Metric.sphere 0 1 :=
            le_antisymm hz (le_of_not_gt hnot)
          have hzS : ψ z ∈ (S : Set X) :=
            Topology.RelCWComplex.cellFrontier_subset_skeletonLT (m + 1) j
              ⟨z, hzsphere, rfl⟩
          exact Set.disjoint_left.mp hd hzS ⟨w, hopenCollar_ball j δ hδ1 hw, hwz⟩
        have hzsource : z ∈ ψ.source := by rwa [Topology.RelCWComplex.source_eq]
        have hw_eq : w = z := ψ.injOn (hsource hw) hzsource hwz
        rwa [← hw_eq]
    · rintro (hz | hz)
      · exact ⟨Metric.sphere_subset_closedBall hz.1, Or.inl hz.2⟩
      · exact ⟨Metric.ball_subset_closedBall (hopenCollar_ball j δ hδ1 hz),
          Or.inr ⟨z, hz, rfl⟩⟩
  let Vnext (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ) : Set X :=
    V₀ ∪ ⋃ j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1),
      Topology.RelCWComplex.map (m + 1) j '' openCollar j (δ j)
  let Cnext (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ) : Set X :=
    C₀ ∪ ⋃ j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1),
      Topology.RelCWComplex.map (m + 1) j '' closedCollar j (δ j)
  have hVnext_carrier (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδ : ∀ j, δ j < 1) : Vnext δ ⊆
      (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 2) : Set X) := by
    intro y hy
    rcases hy with hy | hy
    · exact Topology.RelCWComplex.skeletonLT_mono
        (by exact_mod_cast Nat.add_le_add_left (by decide : 1 ≤ 2) m) (hV₀skeleton hy)
    · rcases Set.mem_iUnion.mp hy with ⟨j, z, hz, rfl⟩
      exact Topology.RelCWComplex.openCell_subset_skeletonLT (m + 1) j
        ⟨z, hopenCollar_ball j (δ j) (hδ j) hz, rfl⟩
  have hCnext_carrier (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδ : ∀ j, δ j < 1) : Cnext δ ⊆
      (Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 2) : Set X) := by
    intro y hy
    rcases hy with hy | hy
    · exact Topology.RelCWComplex.skeletonLT_mono
        (by exact_mod_cast Nat.add_le_add_left (by decide : 1 ≤ 2) m) (hC₀skeleton hy)
    · rcases Set.mem_iUnion.mp hy with ⟨j, z, hz, rfl⟩
      exact Topology.RelCWComplex.closedCell_subset_skeletonLT (m + 1) j
        ⟨z, hclosedCollar_disk j (δ j) (hδ j) hz, rfl⟩
  have hVnext_Cnext (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ) :
      Vnext δ ⊆ Cnext δ := by
    rintro y (hy | hy)
    · exact Or.inl (hV₀C₀ hy)
    · obtain ⟨j, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, z, hopenCollar_closedCollar j (δ j) hz, rfl⟩)
  have hCnext_O (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδO : ∀ j, Topology.RelCWComplex.map (m + 1) j '' closedCollar j (δ j) ⊆ O) :
      Cnext δ ⊆ O := by
    rintro y (hy | hy)
    · exact hC₀O hy
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
      exact hδO j hj
  have hVnext_inter_S (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδ : ∀ j, δ j < 1) :
      Vnext δ ∩ (S : Set X) = V₀ := by
    ext y
    constructor
    · rintro ⟨hyV, hyS⟩
      rcases hyV with hy | hy
      · exact hy
      · rcases Set.mem_iUnion.mp hy with ⟨j, z, hz, rfl⟩
        have hzball := hopenCollar_ball j (δ j) (hδ j) hz
        have hcell : Topology.RelCWComplex.map (m + 1) j z ∈
            Topology.RelCWComplex.openCell (m + 1) j := ⟨z, hzball, rfl⟩
        exact False.elim (Set.disjoint_left.mp
          (Topology.RelCWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
            (j := j) (by exact_mod_cast (le_refl (m + 1)))) hyS hcell)
    · intro hy
      exact ⟨Or.inl hy, hV₀skeleton hy⟩
  have hVnext_preimage
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) :
      Metric.closedBall 0 1 ∩ Topology.RelCWComplex.map (m + 1) j ⁻¹' Vnext δ =
        boundaryOpen j ∪ openCollar j (δ j) := by
    ext z
    constructor
    · rintro ⟨hz, hzV | hzA⟩
      · rw [← hfirstCell_preimage j (δ j) (hδlt j)]
        exact ⟨hz, Or.inl hzV⟩
      · rcases Set.mem_iUnion.mp hzA with ⟨k, w, hw, hwz⟩
        have hzball : z ∈ Metric.ball 0 1 := by
          by_contra hnot
          have hzsphere : z ∈ Metric.sphere 0 1 := le_antisymm hz (le_of_not_gt hnot)
          have hzS := Topology.RelCWComplex.cellFrontier_subset_skeletonLT (m + 1) j
            (show Topology.RelCWComplex.map (m + 1) j z ∈
              Topology.RelCWComplex.cellFrontier (m + 1) j from ⟨z, hzsphere, rfl⟩)
          exact Set.disjoint_left.mp
            (Topology.RelCWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
              (j := k) (le_refl _)) hzS
            ⟨w, hopenCollar_ball k (δ k) (hδlt k) hw, hwz⟩
        have hkj : k = j := by
          by_contra hne
          have hsig : (⟨m + 1, k⟩ :
              Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n) ≠ ⟨m + 1, j⟩ := by
            simpa using hne
          exact Set.disjoint_left.mp (Topology.RelCWComplex.disjoint_openCell_of_ne hsig)
            ⟨w, hopenCollar_ball k (δ k) (hδlt k) hw, hwz⟩ ⟨z, hzball, rfl⟩
        subst k
        rw [← hfirstCell_preimage j (δ j) (hδlt j)]
        exact ⟨hz, Or.inr ⟨w, hw, hwz⟩⟩
    · intro hz
      rw [← hfirstCell_preimage j (δ j) (hδlt j)] at hz
      rcases hz with ⟨hz, hzV | hzA⟩
      · exact ⟨hz, Or.inl hzV⟩
      · exact ⟨hz, Or.inr (Set.mem_iUnion.mpr ⟨j, hzA⟩)⟩
  let Snext := Topology.RelCWComplex.skeletonLT (Set.univ : Set X) (m + 2)
  have hVnext_open
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1) :
      IsOpen {y : Snext | y.val ∈ Vnext δ} := by
    have hdiskOpen : ∀ n (i : Topology.RelCWComplex.cell (Snext : Set X) n),
        IsOpen {z : Metric.closedBall (0 : Fin n → ℝ) 1 |
          Topology.RelCWComplex.map n i z.val ∈ Vnext δ} := by
      intro n i
      have hn : n < m + 2 := by
        have h := i.property
        have h' : (n : ℕ∞) < (m : ℕ∞) + 2 := by
          simpa only [Snext, Topology.RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] using h
        exact_mod_cast h'
      by_cases heq : n = m + 1
      · subst n
        change IsOpen {z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 |
          Topology.RelCWComplex.map (m + 1) i.val z.val ∈ Vnext δ}
        have heq : {z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 |
            Topology.RelCWComplex.map (m + 1) i.val z.val ∈ Vnext δ} =
            {z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 |
              z.val ∈ boundaryOpen i.val ∪ openCollar i.val (δ i.val)} := by
          ext z
          have h := Set.ext_iff.mp (hVnext_preimage δ hδlt i.val) z.val
          simpa only [Set.mem_inter_iff, Set.mem_preimage, z.property, true_and,
            Set.mem_ofPred_eq] using h
        rw [heq]
        exact hboundary_union_collar_open i.val (δ i.val) (hδpos i.val) (hδlt i.val)
      · have hnm : n ≤ m := by omega
        have hiS : Topology.RelCWComplex.closedCell n i.val ⊆ (S : Set X) :=
          (Topology.RelCWComplex.closedCell_subset_skeletonLT n i.val).trans
            (Topology.RelCWComplex.skeletonLT_mono
              (by exact_mod_cast Nat.add_le_add_right hnm 1))
        let f : Metric.closedBall (0 : Fin n → ℝ) 1 → S :=
          fun z ↦ ⟨Topology.RelCWComplex.map n i.val z.val, hiS ⟨z.val, z.property, rfl⟩⟩
        have hf : Continuous f :=
          (Topology.RelCWComplex.continuousOn n i.val).domRestrict.subtype_mk _
        have heq : {z : Metric.closedBall (0 : Fin n → ℝ) 1 |
            Topology.RelCWComplex.map n i z.val ∈ Vnext δ} =
            f ⁻¹' {y : S | y.val ∈ V₀} := by
          ext z
          change Topology.RelCWComplex.map n i.val z.val ∈ Vnext δ ↔
            Topology.RelCWComplex.map n i.val z.val ∈ V₀
          constructor
          · intro hz
            rw [← hVnext_inter_S δ hδlt]
            exact ⟨hz, (f z).property⟩
          · exact fun hz ↦ Or.inl hz
        rw [heq]
        exact hV₀openInSkeleton.preimage hf
    have hclosed : IsClosed ((Snext : Set X) \ Vnext δ) := by
      apply (Topology.CWComplex.closed (Snext : Set X) _ Set.sdiff_subset).mpr
      intro n i
      let D := Metric.closedBall (0 : Fin n → ℝ) 1
      let χ : D → X := fun z ↦ Topology.RelCWComplex.map n i z.val
      have hχ : Continuous χ := (Topology.RelCWComplex.continuousOn n i).domRestrict
      have hcompact : IsCompact {z : D | χ z ∉ Vnext δ} := by
        let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
        exact (hdiskOpen n i).isClosed_compl.isCompact
      have heq : ((Snext : Set X) \ Vnext δ) ∩ Topology.CWComplex.closedCell n i =
          χ '' {z : D | χ z ∉ Vnext δ} := by
        ext y
        constructor
        · rintro ⟨⟨_, hy⟩, z, hz, rfl⟩
          exact ⟨⟨z, hz⟩, hy, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨⟨Topology.RelCWComplex.closedCell_subset_complex n i
            ⟨z.val, z.property, rfl⟩, hz⟩, ⟨z.val, z.property, rfl⟩⟩
      rw [heq]
      exact (hcompact.image hχ).isClosed
    have hc := hclosed.preimage
      (continuous_subtype_val : Continuous (Subtype.val : Snext → X))
    have heq : (Subtype.val : Snext → X) ⁻¹' ((Snext : Set X) \ Vnext δ) =
        {y : Snext | y.val ∈ Vnext δ}ᶜ := by
      ext y
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨y.property, h⟩⟩
    rw [heq] at hc
    simpa only [compl_compl] using hc.isOpen_compl
  have hCnext_inter_S
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδlt : ∀ j, δ j < 1) : Cnext δ ∩ (S : Set X) = C₀ := by
    ext y
    constructor
    · rintro ⟨hy | hy, hyS⟩
      · exact hy
      · obtain ⟨j, _, ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hy
        have hr0 : 0 ≤ r := (sub_nonneg.mpr (hδlt j).le).trans hr.1
        have hθnorm : ‖θ‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using hθ.1
        by_cases hr1 : r = 1
        · change Topology.RelCWComplex.map (m + 1) j (r • θ) ∈ C₀
          rw [hr1, one_smul]
          exact hθ.2
        · have hrlt : r < 1 := lt_of_le_of_ne hr.2 hr1
          have hball : r • θ ∈ Metric.ball 0 1 := by
            simpa only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg hr0, hθnorm, mul_one] using hrlt
          exact False.elim (Set.disjoint_left.mp
            (Topology.RelCWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
              (j := j) (le_refl _)) hyS ⟨r • θ, hball, rfl⟩)
    · intro hy
      exact ⟨Or.inl hy, hC₀skeleton hy⟩
  have hCnext_closed
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδlt : ∀ j, δ j < 1) : IsClosed (Cnext δ) := by
    apply (Topology.CWComplex.closed (Snext : Set X) _ (hCnext_carrier δ hδlt)).mpr
    intro n i
    have hn : n < m + 2 := by
      have h := i.property
      have h' : (n : ℕ∞) < (m : ℕ∞) + 2 := by
        simpa only [Snext, Topology.RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] using h
      exact_mod_cast h'
    by_cases heq : n = m + 1
    · subst n
      have heq : Cnext δ ∩ Topology.RelCWComplex.closedCell (m + 1) i.val =
          (C₀ ∩ Topology.RelCWComplex.closedCell (m + 1) i.val) ∪
            Topology.RelCWComplex.map (m + 1) i.val '' closedCollar i.val (δ i.val) := by
        ext y
        constructor
        · rintro ⟨hy, hycell⟩
          by_cases hyS : y ∈ (S : Set X)
          · left
            refine ⟨?_, hycell⟩
            rw [← hCnext_inter_S δ hδlt]
            exact ⟨hy, hyS⟩
          · rcases hy with hy | hy
            · exact (hyS (hC₀skeleton hy)).elim
            · obtain ⟨k, w, hw, hwz⟩ := Set.mem_iUnion.mp hy
              obtain ⟨z, hz, hzy⟩ := hycell
              have hzball : z ∈ Metric.ball 0 1 := by
                by_contra hnot
                have hzsphere : z ∈ Metric.sphere 0 1 := le_antisymm hz (le_of_not_gt hnot)
                exact hyS (Topology.RelCWComplex.cellFrontier_subset_skeletonLT (m + 1) i.val
                  ⟨z, hzsphere, hzy⟩)
              have hwball : w ∈ Metric.ball 0 1 := by
                by_contra hnot
                have hwsphere : w ∈ Metric.sphere 0 1 :=
                  le_antisymm (hclosedCollar_disk k (δ k) (hδlt k) hw) (le_of_not_gt hnot)
                exact hyS (Topology.RelCWComplex.cellFrontier_subset_skeletonLT (m + 1) k
                  ⟨w, hwsphere, hwz⟩)
              have hki : k = i.val := by
                by_contra hne
                have hsig : (⟨m + 1, k⟩ :
                    Σ n, Topology.RelCWComplex.cell (Set.univ : Set X) n) ≠ ⟨m + 1, i.val⟩ := by
                  simpa using hne
                exact Set.disjoint_left.mp (Topology.RelCWComplex.disjoint_openCell_of_ne hsig)
                  ⟨w, hwball, hwz⟩ ⟨z, hzball, hzy⟩
              right
              subst k
              exact ⟨w, hw, hwz⟩
        · rintro (⟨hy, hycell⟩ | ⟨z, hz, rfl⟩)
          · exact ⟨Or.inl hy, hycell⟩
          · exact ⟨Or.inr (Set.mem_iUnion.mpr ⟨i.val, z, hz, rfl⟩),
              ⟨z, hclosedCollar_disk i.val (δ i.val) (hδlt i.val) hz, rfl⟩⟩
      change IsClosed (Cnext δ ∩ Topology.RelCWComplex.closedCell (m + 1) i.val)
      rw [heq]
      exact (hC₀closed.inter Topology.RelCWComplex.isClosed_closedCell).union
        (hclosedCollar_image_closed i.val (δ i.val) (hδlt i.val))
    · have hnm : n ≤ m := by omega
      have hiS : Topology.RelCWComplex.closedCell n i.val ⊆ (S : Set X) :=
        (Topology.RelCWComplex.closedCell_subset_skeletonLT n i.val).trans
          (Topology.RelCWComplex.skeletonLT_mono
            (by exact_mod_cast Nat.add_le_add_right hnm 1))
      have heq : Cnext δ ∩ Topology.RelCWComplex.closedCell n i.val =
          C₀ ∩ Topology.RelCWComplex.closedCell n i.val := by
        ext y
        constructor
        · rintro ⟨hy, hycell⟩
          refine ⟨?_, hycell⟩
          rw [← hCnext_inter_S δ hδlt]
          exact ⟨hy, hiS hycell⟩
        · exact fun h ↦ ⟨Or.inl h.1, h.2⟩
      change IsClosed (Cnext δ ∩ Topology.RelCWComplex.closedCell n i.val)
      rw [heq]
      exact hC₀closed.inter Topology.RelCWComplex.isClosed_closedCell
  have hfirst_stage : ∃ δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ,
      (∀ j, 0 < δ j ∧ δ j < 1 / 2) ∧
      IsOpen {y : Snext | y.val ∈ Vnext δ} ∧ IsClosed (Cnext δ) ∧
      x ∈ Vnext δ ∧ Vnext δ ⊆ Cnext δ ∧ Cnext δ ⊆ O := by
    let δ := fun j ↦ (hcollar_width j).choose
    have hδpos : ∀ j, 0 < δ j := fun j ↦ (hcollar_width j).choose_spec.1
    have hδhalf : ∀ j, δ j < 1 / 2 := fun j ↦ (hcollar_width j).choose_spec.2.1
    have hδlt : ∀ j, δ j < 1 := fun j ↦ (hδhalf j).trans (by norm_num)
    exact ⟨δ, fun j ↦ ⟨hδpos j, hδhalf j⟩, hVnext_open δ hδpos hδlt,
      hCnext_closed δ hδlt, Or.inl hxV₀, hVnext_Cnext δ,
      hCnext_O δ (fun j ↦ (hcollar_width j).choose_spec.2.2)⟩
  have hnew_coordinates
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (y : Vnext δ) (hy : y.val ∉ V₀) :
      ∃ j, ∃ z ∈ openCollar j (δ j), Topology.RelCWComplex.map (m + 1) j z = y.val := by
    rcases y.property with hold | hnew
    · exact (hy hold).elim
    · exact Set.mem_iUnion.mp hnew
  have hnew_coordinates_unique
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδlt : ∀ j, δ j < 1)
      (j k : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (z w : Fin (m + 1) → ℝ) (hz : z ∈ openCollar j (δ j))
      (hw : w ∈ openCollar k (δ k))
      (heq : Topology.RelCWComplex.map (m + 1) j z =
        Topology.RelCWComplex.map (m + 1) k w) : j = k ∧ z = w := by
    have hzball := hopenCollar_ball j (δ j) (hδlt j) hz
    have hwball := hopenCollar_ball k (δ k) (hδlt k) hw
    have hjk : j = k := by
      by_contra hne
      have hd := Topology.RelCWComplex.disjoint_openCell_of_ne
        (C := (Set.univ : Set X)) (n := m + 1) (m := m + 1) (i := j) (j := k)
        (by intro h; exact hne (eq_of_heq (Sigma.mk.inj h).2))
      exact Set.disjoint_left.mp hd ⟨z, hzball, rfl⟩ ⟨w, hwball, heq.symm⟩
    subst k
    refine ⟨rfl, ?_⟩
    apply (Topology.RelCWComplex.map (m + 1) j).injOn _ _ heq
    · rwa [Topology.RelCWComplex.source_eq]
    · rwa [Topology.RelCWComplex.source_eq]
  let firstRetraction
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1) : Vnext δ → V₀ := fun y ↦
    if hy : y.val ∈ V₀ then ⟨y.val, hy⟩ else
      let j := (hnew_coordinates δ y hy).choose
      let z := (hnew_coordinates δ y hy).choose_spec.choose
      let hz := (hnew_coordinates δ y hy).choose_spec.choose_spec.1
      ⟨Topology.RelCWComplex.map (m + 1) j (‖z‖⁻¹ • z),
        ((hopenCollar_iff_radial j (δ j) (hδpos j) (hδlt j)).mp hz).2.2.2⟩
  have hfirstRetraction_fixed
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1) (y : V₀) :
      firstRetraction δ hδpos hδlt ⟨y.val, Or.inl y.property⟩ = y := by
    apply Subtype.ext
    simp only [firstRetraction, dite_eq_left y.property]
  have hfirstRetraction_on_collar
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (z : Fin (m + 1) → ℝ) (hz : z ∈ openCollar j (δ j)) :
      (firstRetraction δ hδpos hδlt
        ⟨Topology.RelCWComplex.map (m + 1) j z,
          Or.inr (Set.mem_iUnion.mpr ⟨j, z, hz, rfl⟩)⟩).val =
      Topology.RelCWComplex.map (m + 1) j (‖z‖⁻¹ • z) := by
    have hnot : Topology.RelCWComplex.map (m + 1) j z ∉ V₀ := by
      intro hy
      exact Set.disjoint_left.mp
        (Topology.RelCWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
          (j := j) (le_refl _)) (hV₀skeleton hy)
        ⟨z, hopenCollar_ball j (δ j) (hδlt j) hz, rfl⟩
    dsimp only [firstRetraction]
    rw [dite_eq_right hnot]
    dsimp only
    have hcoords := hnew_coordinates δ
      ⟨Topology.RelCWComplex.map (m + 1) j z,
        Or.inr (Set.mem_iUnion.mpr ⟨j, z, hz, rfl⟩)⟩ hnot
    obtain ⟨hj, hw⟩ := hnew_coordinates_unique δ hδlt hcoords.choose j
      hcoords.choose_spec.choose z hcoords.choose_spec.choose_spec.1 hz
      hcoords.choose_spec.choose_spec.2
    change Topology.RelCWComplex.map (m + 1) hcoords.choose
      (‖hcoords.choose_spec.choose‖⁻¹ • hcoords.choose_spec.choose) = _
    rw [hw]
    exact congrArg (fun k ↦ Topology.RelCWComplex.map (m + 1) k (‖z‖⁻¹ • z)) hj
  -- Extend this first collar deformation across each entire characteristic disk.
  -- The positive cutoff makes the extension continuous even at the disk's centre.
  let firstCellPrism
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (p : unitInterval × Metric.closedBall (0 : Fin (m + 1) → ℝ) 1) :
      Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 :=
    ⟨(1 - (p.1 : ℝ)) • p.2.val +
        (p.1 : ℝ) • ((max (1 - δ j) ‖p.2.val‖)⁻¹ • p.2.val), by
      have hp : 0 < max (1 - δ j) ‖p.2.val‖ :=
        (sub_pos.mpr (hδlt j)).trans_le (le_max_left _ _)
      have hnorm : ‖(max (1 - δ j) ‖p.2.val‖)⁻¹ • p.2.val‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp),
          ← div_eq_inv_mul, div_le_one hp]
        exact le_max_right _ _
      apply (convex_closedBall (0 : Fin (m + 1) → ℝ) 1) p.2.property
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm)
        (sub_nonneg.mpr p.1.property.2) p.1.property.1
      ring⟩
  have hfirstCellPrism_continuous
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) :
      Continuous (firstCellPrism δ hδlt j) := by
    have hc : Continuous (fun z : Fin (m + 1) → ℝ ↦
        (max (1 - δ j) ‖z‖)⁻¹ • z) :=
      ((continuous_const.max continuous_norm).inv₀
        (fun z ↦ ne_of_gt ((sub_pos.mpr (hδlt j)).trans_le
          (le_max_left _ _)))).smul continuous_id
    exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (hc.comp (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
  have hfirstCellPrism_characteristic_continuous
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1)) :
      Continuous (fun p ↦ Topology.RelCWComplex.map (m + 1) j
        (firstCellPrism δ hδlt j p).val) := by
    exact (Topology.RelCWComplex.continuousOn (m + 1) j).comp_continuous
      (continuous_subtype_val.comp (hfirstCellPrism_continuous δ hδlt j))
      (fun p ↦ (firstCellPrism δ hδlt j p).property)
  have hfirstCellPrism_zero
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1) :
      firstCellPrism δ hδlt j (0, z) = z := by
    apply Subtype.ext
    simp [firstCellPrism]
  have hfirstCellPrism_boundary
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (t : unitInterval) (z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1)
      (hz : ‖z.val‖ = 1) : firstCellPrism δ hδlt j (t, z) = z := by
    apply Subtype.ext
    change (1 - (t : ℝ)) • z.val +
      (t : ℝ) • ((max (1 - δ j) ‖z.val‖)⁻¹ • z.val) = z.val
    rw [hz, max_eq_right (by linarith [hδpos j]), inv_one, one_smul, ← add_smul]
    simp
  have hfirstCellPrism_one_on_collar
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1)
      (hz : z.val ∈ openCollar j (δ j)) :
      Topology.RelCWComplex.map (m + 1) j (firstCellPrism δ hδlt j (1, z)).val =
        (firstRetraction δ hδpos hδlt
          ⟨Topology.RelCWComplex.map (m + 1) j z.val,
            Or.inr (Set.mem_iUnion.mpr ⟨j, z.val, hz, rfl⟩)⟩).val := by
    rw [hfirstRetraction_on_collar δ hδpos hδlt j z.val hz]
    have hr := ((hopenCollar_iff_radial j (δ j) (hδpos j) (hδlt j)).mp hz).2.1
    simp [firstCellPrism, max_eq_right hr.le]
  have hfirstCellPrism_preserves
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (t : unitInterval) (z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1)
      (hz : z.val ∈ boundaryOpen j ∪ openCollar j (δ j)) :
      Topology.RelCWComplex.map (m + 1) j (firstCellPrism δ hδlt j (t, z)).val ∈
        Vnext δ := by
    rcases hz with hz | hz
    · have hnorm : ‖z.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz.1
      rw [hfirstCellPrism_boundary δ hδpos hδlt j t z hnorm]
      exact Or.inl hz.2
    · obtain ⟨⟨r, θ⟩, ⟨hr, hθ⟩, heq⟩ := hz
      have hrpos : 0 < r := (sub_pos.mpr (hδlt j)).trans hr.1
      have hθnorm : ‖θ‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hθ.1
      have hnorm : ‖r • θ‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hθnorm, mul_one]
      have hformula : (firstCellPrism δ hδlt j (t, z)).val =
          ((1 - (t : ℝ)) * r + (t : ℝ)) • θ := by
        change (1 - (t : ℝ)) • z.val +
          (t : ℝ) • ((max (1 - δ j) ‖z.val‖)⁻¹ • z.val) = _
        rw [← heq, hnorm, max_eq_right hr.1.le, smul_smul r⁻¹ r θ,
          inv_mul_cancel₀ hrpos.ne', one_smul, smul_smul, ← add_smul]
      rw [hformula]
      by_cases ht : (t : ℝ) = 1
      · simp only [ht, sub_self, zero_mul, zero_add, one_smul]
        exact Or.inl hθ.2
      · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
        have hrle : r ≤ (1 - (t : ℝ)) * r + (t : ℝ) := by
          nlinarith [t.property.1, hr.2]
        have hrlt : (1 - (t : ℝ)) * r + (t : ℝ) < 1 := by
          nlinarith [mul_pos (sub_pos.mpr htlt) (sub_pos.mpr hr.2)]
        exact Or.inr (Set.mem_iUnion.mpr ⟨j, _,
          ⟨⟨(1 - (t : ℝ)) * r + (t : ℝ), θ⟩,
            ⟨⟨hr.1.trans_le hrle, hrlt⟩, hθ⟩, rfl⟩, rfl⟩)
  let firstDeformation
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1) :
      unitInterval × Vnext δ → Vnext δ := fun p ↦
    if hy : p.2.val ∈ V₀ then p.2 else
      let coords := hnew_coordinates δ p.2 hy
      let j := coords.choose
      let z := coords.choose_spec.choose
      let hz := coords.choose_spec.choose_spec.1
      let zDisk : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 :=
        ⟨z, Metric.ball_subset_closedBall (hopenCollar_ball j (δ j) (hδlt j) hz)⟩
      ⟨Topology.RelCWComplex.map (m + 1) j (firstCellPrism δ hδlt j (p.1, zDisk)).val,
        hfirstCellPrism_preserves δ hδpos hδlt j p.1 zDisk (Or.inr hz)⟩
  have hfirstDeformation_fixed
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1)
      (t : unitInterval) (y : Vnext δ) (hy : y.val ∈ V₀) :
      firstDeformation δ hδpos hδlt (t, y) = y := by
    simp only [firstDeformation, dite_eq_left hy]
  have hfirstDeformation_zero
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1) (y : Vnext δ) :
      firstDeformation δ hδpos hδlt (0, y) = y := by
    by_cases hy : y.val ∈ V₀
    · exact hfirstDeformation_fixed δ hδpos hδlt 0 y hy
    · apply Subtype.ext
      simp only [firstDeformation, dite_eq_right hy]
      rw [hfirstCellPrism_zero δ hδlt]
      exact (hnew_coordinates δ y hy).choose_spec.choose_spec.2
  have hfirstDeformation_one
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1) (y : Vnext δ) :
      (firstDeformation δ hδpos hδlt (1, y)).val =
        (firstRetraction δ hδpos hδlt y).val := by
    by_cases hy : y.val ∈ V₀
    · simp only [firstDeformation, firstRetraction, dite_eq_left hy]
    · simp only [firstDeformation, firstRetraction, dite_eq_right hy]
      have coords := hnew_coordinates δ y hy
      have hz := coords.choose_spec.choose_spec.1
      have hr := ((hopenCollar_iff_radial coords.choose (δ coords.choose)
        (hδpos coords.choose) (hδlt coords.choose)).mp hz).2.1
      simp [firstCellPrism, max_eq_right hr.le]
  have hfirstDeformation_on_collar
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (t : unitInterval) (z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1)
      (hz : z.val ∈ openCollar j (δ j)) :
      (firstDeformation δ hδpos hδlt
        (t, ⟨Topology.RelCWComplex.map (m + 1) j z.val,
          Or.inr (Set.mem_iUnion.mpr ⟨j, z.val, hz, rfl⟩)⟩)).val =
      Topology.RelCWComplex.map (m + 1) j (firstCellPrism δ hδlt j (t, z)).val := by
    have hnot : Topology.RelCWComplex.map (m + 1) j z.val ∉ V₀ := by
      intro hy
      exact Set.disjoint_left.mp
        (Topology.RelCWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
          (j := j) (le_refl _)) (hV₀skeleton hy)
        ⟨z.val, hopenCollar_ball j (δ j) (hδlt j) hz, rfl⟩
    dsimp only [firstDeformation]
    rw [dite_eq_right hnot]
    dsimp only
    have coords := hnew_coordinates δ
      ⟨Topology.RelCWComplex.map (m + 1) j z.val,
        Or.inr (Set.mem_iUnion.mpr ⟨j, z.val, hz, rfl⟩)⟩ hnot
    obtain ⟨hj, hw⟩ := hnew_coordinates_unique δ hδlt coords.choose j
      coords.choose_spec.choose z.val coords.choose_spec.choose_spec.1 hz
      coords.choose_spec.choose_spec.2
    change Topology.RelCWComplex.map (m + 1) coords.choose
      ((1 - (t : ℝ)) • coords.choose_spec.choose +
        (t : ℝ) • ((max (1 - δ coords.choose) ‖coords.choose_spec.choose‖)⁻¹ •
          coords.choose_spec.choose)) = _
    rw [hw]
    exact congrArg (fun k ↦ Topology.RelCWComplex.map (m + 1) k
      ((1 - (t : ℝ)) • z.val +
        (t : ℝ) • ((max (1 - δ k) ‖z.val‖)⁻¹ • z.val))) hj
  have hfirstDeformation_top_pullback
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1)
      (j : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1))
      (t : unitInterval) (z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1)
      (hz : Topology.RelCWComplex.map (m + 1) j z.val ∈ Vnext δ) :
      (firstDeformation δ hδpos hδlt
        (t, ⟨Topology.RelCWComplex.map (m + 1) j z.val, hz⟩)).val =
        Topology.RelCWComplex.map (m + 1) j (firstCellPrism δ hδlt j (t, z)).val := by
    have hpre : z.val ∈ boundaryOpen j ∪ openCollar j (δ j) := by
      rw [← hVnext_preimage δ hδlt j]
      exact ⟨z.property, hz⟩
    rcases hpre with hold | hnew
    · rw [hfirstDeformation_fixed δ hδpos hδlt t
        ⟨Topology.RelCWComplex.map (m + 1) j z.val, hz⟩ hold.2]
      have hnorm : ‖z.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hold.1
      rw [hfirstCellPrism_boundary δ hδpos hδlt j t z hnorm]
    · exact hfirstDeformation_on_collar δ hδpos hδlt j t z hnew
  have hfirstDeformation_characteristic_continuous
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1)
      (n : ℕ) (i : Topology.RelCWComplex.cell (Snext : Set X) n) :
      Continuous (fun p : unitInterval ×
          {z : Metric.closedBall (0 : Fin n → ℝ) 1 //
            Topology.RelCWComplex.map n i z.val ∈ Vnext δ} ↦
        firstDeformation δ hδpos hδlt
          (p.1, ⟨Topology.RelCWComplex.map n i p.2.val.val, p.2.property⟩)) := by
    have hn : n < m + 2 := by
      have h := i.property
      have h' : (n : ℕ∞) < (m : ℕ∞) + 2 := by
        simpa only [Snext, Topology.RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] using h
      exact_mod_cast h'
    have hambient : Continuous (fun p : unitInterval ×
          {z : Metric.closedBall (0 : Fin n → ℝ) 1 //
            Topology.RelCWComplex.map n i z.val ∈ Vnext δ} ↦
        (firstDeformation δ hδpos hδlt
          (p.1, ⟨Topology.RelCWComplex.map n i p.2.val.val, p.2.property⟩)).val) := by
      by_cases heq : n = m + 1
      · subst n
        have hc : Continuous (fun p : unitInterval ×
            {z : Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 //
              Topology.RelCWComplex.map (m + 1) i z.val ∈ Vnext δ} ↦
            Topology.RelCWComplex.map (m + 1) i.val
              (firstCellPrism δ hδlt i.val (p.1, p.2.val)).val) :=
          (hfirstCellPrism_characteristic_continuous δ hδlt i.val).comp
            (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
        convert hc using 1
        funext p
        exact hfirstDeformation_top_pullback δ hδpos hδlt i.val p.1 p.2.val p.2.property
      · have hnm : n ≤ m := by omega
        have hc : Continuous (fun p : unitInterval ×
            {z : Metric.closedBall (0 : Fin n → ℝ) 1 //
              Topology.RelCWComplex.map n i z.val ∈ Vnext δ} ↦
            Topology.RelCWComplex.map n i p.2.val.val) :=
          (Topology.RelCWComplex.continuousOn n i).domRestrict.comp
            (continuous_subtype_val.comp continuous_snd)
        convert hc using 1
        funext p
        have hyS : Topology.RelCWComplex.map n i p.2.val.val ∈ (S : Set X) := by
          apply Topology.RelCWComplex.skeletonLT_mono
            (show (n + 1 : ℕ∞) ≤ m + 1 by exact_mod_cast Nat.add_le_add_right hnm 1)
          exact Topology.RelCWComplex.closedCell_subset_skeletonLT n i.val
            ⟨p.2.val.val, p.2.val.property, rfl⟩
        have hyV : Topology.RelCWComplex.map n i p.2.val.val ∈ V₀ := by
          rw [← hVnext_inter_S δ hδlt]
          exact ⟨p.2.property, hyS⟩
        rw [hfirstDeformation_fixed δ hδpos hδlt p.1 _ hyV]
    exact hambient.subtype_mk _
  have hfirstDeformation_bundle
      (δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ)
      (hδpos : ∀ j, 0 < δ j) (hδlt : ∀ j, δ j < 1)
      (hc : Continuous (firstDeformation δ hδpos hδlt)) :
      ∃ R : C(Vnext δ, V₀),
        (∀ y, R y = firstRetraction δ hδpos hδlt y) ∧
        R.comp (ContinuousMap.inclusion (show V₀ ⊆ Vnext δ from fun _ hy ↦ Or.inl hy)) =
          ContinuousMap.id V₀ ∧
        Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id (Vnext δ))
          ((ContinuousMap.inclusion
            (show V₀ ⊆ Vnext δ from fun _ hy ↦ Or.inl hy)).comp R)
          {y : Vnext δ | y.val ∈ V₀}) := by
    have hr : Continuous (firstRetraction δ hδpos hδlt) := by
      have hend : Continuous (fun y : Vnext δ ↦
          (firstDeformation δ hδpos hδlt (1, y)).val) :=
        continuous_subtype_val.comp (hc.comp (continuous_const.prodMk continuous_id))
      have heq : (fun y : Vnext δ ↦ (firstDeformation δ hδpos hδlt (1, y)).val) =
          (fun y ↦ (firstRetraction δ hδpos hδlt y).val) :=
        funext (hfirstDeformation_one δ hδpos hδlt)
      rw [heq] at hend
      exact hend.subtype_mk _
    let R : C(Vnext δ, V₀) := ⟨firstRetraction δ hδpos hδlt, hr⟩
    refine ⟨R, fun _ ↦ rfl, ?_, ⟨?_⟩⟩
    · apply ContinuousMap.ext
      exact hfirstRetraction_fixed δ hδpos hδlt
    · exact
        { toFun := firstDeformation δ hδpos hδlt
          continuous_toFun := hc
          map_zero_left := hfirstDeformation_zero δ hδpos hδlt
          map_one_left := fun y ↦ Subtype.ext (hfirstDeformation_one δ hδpos hδlt y)
          prop' := fun t y hy ↦ hfirstDeformation_fixed δ hδpos hδlt t y hy }
  have hsuccessor_interface :
      ∃ δ : Topology.RelCWComplex.cell (Set.univ : Set X) (m + 1) → ℝ,
      ∃ hδpos : ∀ j, 0 < δ j, ∃ hδlt : ∀ j, δ j < 1,
        (∀ j, δ j < 1 / 2) ∧
        V₀ ⊆ Vnext δ ∧ C₀ ⊆ Cnext δ ∧
        Vnext δ ⊆ (Snext : Set X) ∧ Cnext δ ⊆ (Snext : Set X) ∧
        Vnext δ ∩ (S : Set X) = V₀ ∧ Cnext δ ∩ (S : Set X) = C₀ ∧
        IsOpen {y : Snext | y.val ∈ Vnext δ} ∧ IsClosed (Cnext δ) ∧
        x ∈ Vnext δ ∧ Vnext δ ⊆ Cnext δ ∧ Cnext δ ⊆ O ∧
        (∀ n (i : Topology.RelCWComplex.cell (Snext : Set X) n),
          Continuous (fun p : unitInterval ×
              {z : Metric.closedBall (0 : Fin n → ℝ) 1 //
                Topology.RelCWComplex.map n i z.val ∈ Vnext δ} ↦
            firstDeformation δ hδpos hδlt
              (p.1, ⟨Topology.RelCWComplex.map n i p.2.val.val, p.2.property⟩))) ∧
        (∀ t (y : Vnext δ), y.val ∈ V₀ →
          firstDeformation δ hδpos hδlt (t, y) = y) ∧
        (∀ y : Vnext δ, firstDeformation δ hδpos hδlt (0, y) = y) ∧
        (∀ y : Vnext δ, (firstDeformation δ hδpos hδlt (1, y)).val =
          (firstRetraction δ hδpos hδlt y).val) ∧
        (∀ y : V₀, firstRetraction δ hδpos hδlt ⟨y.val, Or.inl y.property⟩ = y) := by
    obtain ⟨δ, hδ, hopen, hclosed, hx, hVC, hCO⟩ := hfirst_stage
    let hδpos : ∀ j, 0 < δ j := fun j ↦ (hδ j).1
    let hδlt : ∀ j, δ j < 1 := fun j ↦ (hδ j).2.trans (by norm_num)
    exact ⟨δ, hδpos, hδlt, fun j ↦ (hδ j).2,
      fun _ hy ↦ Or.inl hy, fun _ hy ↦ Or.inl hy,
      hVnext_carrier δ hδlt, hCnext_carrier δ hδlt,
      hVnext_inter_S δ hδlt, hCnext_inter_S δ hδlt,
      hopen, hclosed, hx, hVC, hCO,
      fun n i ↦ hfirstDeformation_characteristic_continuous δ hδpos hδlt n i,
      fun t y hy ↦ hfirstDeformation_fixed δ hδpos hδlt t y hy,
      fun y ↦ hfirstDeformation_zero δ hδpos hδlt y,
      fun y ↦ hfirstDeformation_one δ hδpos hδlt y,
      fun y ↦ hfirstRetraction_fixed δ hδpos hδlt y⟩
  have hsuccessor_stage_data :
      ∃ (A B : Set X) (hVA : V₀ ⊆ A),
        Stage (m + 1) A B ∧ C₀ ⊆ B ∧
        A ∩ (S : Set X) = V₀ ∧ B ∩ (S : Set X) = C₀ ∧
        ∃ (R : A → V₀) (H : unitInterval × A → A),
          (∀ y : V₀, R ⟨y.val, hVA y.property⟩ = y) ∧
          (∀ y, H (0, y) = y) ∧ (∀ y, (H (1, y)).val = (R y).val) ∧
          (∀ t (y : A), y.val ∈ V₀ → H (t, y) = y) ∧
          (∀ n (i : Topology.RelCWComplex.cell (Snext : Set X) n),
            Continuous (fun p : unitInterval ×
                {z : Metric.closedBall (0 : Fin n → ℝ) 1 //
                  Topology.RelCWComplex.map n i z.val ∈ A} ↦
              H (p.1, ⟨Topology.RelCWComplex.map n i p.2.val.val, p.2.property⟩))) ∧
          (Continuous H → ∃ r : C(A, V₀),
            (∀ y, r y = R y) ∧
            r.comp (ContinuousMap.inclusion hVA) = ContinuousMap.id V₀ ∧
            Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id A)
              ((ContinuousMap.inclusion hVA).comp r) {y : A | y.val ∈ V₀})) := by
    obtain ⟨δ, hδ, hopen, hclosed, hx, hVC, hCO⟩ := hfirst_stage
    let hδpos : ∀ j, 0 < δ j := fun j ↦ (hδ j).1
    let hδlt : ∀ j, δ j < 1 := fun j ↦ (hδ j).2.trans (by norm_num)
    have hstage : Stage (m + 1) (Vnext δ) (Cnext δ) := by
      refine ⟨hVC, hCO, ?_, ?_, hclosed, hx⟩
      · simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
          hCnext_carrier δ hδlt
      · have hdim : ((m + 1 : ℕ) : ℕ∞) + 1 = (m : ℕ∞) + 2 := by
          simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
        change IsOpen {y : Topology.RelCWComplex.skeletonLT (Set.univ : Set X)
          (((m + 1 : ℕ) : ℕ∞) + 1) | y.val ∈ Vnext δ}
        rw [hdim]
        exact hopen
    exact ⟨Vnext δ, Cnext δ, (fun _ hy ↦ Or.inl hy), hstage,
      (fun _ hy ↦ Or.inl hy), hVnext_inter_S δ hδlt, hCnext_inter_S δ hδlt,
      firstRetraction δ hδpos hδlt, firstDeformation δ hδpos hδlt,
      hfirstRetraction_fixed δ hδpos hδlt, hfirstDeformation_zero δ hδpos hδlt,
      hfirstDeformation_one δ hδpos hδlt, hfirstDeformation_fixed δ hδpos hδlt,
      hfirstDeformation_characteristic_continuous δ hδpos hδlt,
      hfirstDeformation_bundle δ hδpos hδlt⟩
  exact hsuccessor_stage_data


end HolomorphicAnosov
