import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.CompactOpen
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopQuotientPresentationDataG3

open _root_.Topology
namespace HolomorphicAnosov

/-- Open collar and punctured-circle charts for the collapsed one-vertex wedge.

Source: Hatcher, *Algebraic Topology*, quotient/wedge topology p.10 and graph
quotient p.83, Proposition 1A.2 proof pp.84--85.  The quotient presentation
identifies the collapsed graph with one vertex and one closed characteristic
interval for each complementary edge.  A vertex collar consists of the root
summand together with outer annuli on every interval; the chart for an edge
contains its interval together with that collar.  These sets cover the wedge,
are open in the quotient topology, and have path-connected collar overlaps.
The collar is exactly the image of coordinates with norm greater than one half.
Move each such coordinate linearly toward its endpoint of the same sign.
This gives a contraction fixing the root. To prove joint continuity, regard
these tracks as maps into the compact-open path space: they are continuous on
each open half-interval, agree on the boundary fibres, and descend through the
quotient. Evaluation is continuous because the time interval is locally compact.
The same tracks, with an arbitrary choice of representative away from the collar,
give root paths on the whole wedge. Each track lifts to a path from its original
coordinate to one of the two interval endpoints. These lift data identify the
edge generators in the subsequent finite-subdivision proof. This radial formula
and compact-open descent are an agent-written expansion of the cited argument.
-/
theorem graph_spanning_tree_loop_collapsed_wedge_collar_cover_g3
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)]
    (hdim : ∀ n : ℕ, 1 < n → IsEmpty (RelCWComplex.cell (Set.univ : Set X) n))
    (T : RelCWComplex.Subcomplex (Set.univ : Set X))
    (hT0 : T.I 0 = Set.univ)
    (a : (T : Set X))
    (_hE : ∃ e : RelCWComplex.cell (Set.univ : Set X) 1, e ∉ T.I 1) :
    let E := {e : RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1}
    let D := Metric.closedBall (0 : Fin 1 → ℝ) 1
    let W := GoodPair.Collapsed (T : Set X)
    let π : Unit ⊕ (Σ _ : E, D) → W :=
      Sum.elim (fun _ => GoodPair.collapse (T : Set X) a.val)
        (fun p => GoodPair.collapse (T : Set X) (RelCWComplex.map 1 p.1.val p.2.val))
    ∃ V : Set W, ∃ U : E → Set W,
      IsOpen V ∧ (∀ e, IsOpen (U e)) ∧
      (V ∪ ⋃ e, U e = Set.univ) ∧
      (∀ e, IsPathConnected (V ∩ U e)) ∧
      (∀ e (z : D), ‖z.val‖ < 1 → π (.inr ⟨e, z⟩) ∈ U e) ∧
      (∀ e (z : D), π (.inr ⟨e, z⟩) ∈ V ↔ 1 / 2 < ‖z.val‖) ∧
      ∃ hb : π (.inl ()) ∈ V, ∃ H : C(unitInterval × V, W),
        (∀ y, H (0, y) = y.val) ∧
        (∀ y, H (1, y) = π (.inl ())) ∧
        (∀ t, H (t, ⟨π (.inl ()), hb⟩) = π (.inl ())) ∧
        (∀ p, H p ∈ V) ∧
        ∃ G : W → C(unitInterval, W),
          (∀ y, G y 0 = y) ∧ (∀ y, G y 1 = π (.inl ())) ∧
          (∀ t, G (π (.inl ())) t = π (.inl ())) ∧
          (∀ y ∈ V, ∀ t, G y t ∈ V) ∧
          ∀ e (z : D), ∃ v : D,
            (v.val = (fun _ ↦ -1) ∨ v.val = (fun _ ↦ 1)) ∧
            ∃ l : Path z v, ∀ t, G (π (.inr ⟨e, z⟩)) t = π (.inr ⟨e, l t⟩) := by
  classical
  dsimp only
  let E := {e : RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1}
  let D := Metric.closedBall (0 : Fin 1 → ℝ) 1
  let W := GoodPair.Collapsed (T : Set X)
  let π : Unit ⊕ (Σ _ : E, D) → W :=
    Sum.elim (fun _ ↦ GoodPair.collapse (T : Set X) a.val)
      (fun p ↦ GoodPair.collapse (T : Set X) (RelCWComplex.map 1 p.1.val p.2.val))
  let b : W := π (.inl ())
  let χ (e : E) (z : D) : W := π (.inr ⟨e, z⟩)
  obtain ⟨hπ, hroot, hinj⟩ :=
    graph_spanning_tree_loop_quotient_presentation_data_g3 hdim T hT0 a
  change _ at hπ
  have hbound (z : D) : ‖z.val‖ ≤ 1 := by
    simpa only [D, Metric.mem_closedBall, dist_zero_right] using z.property
  have hχroot (e : E) (z : D) : χ e z = b ↔ ‖z.val‖ = 1 := hroot e z
  have hχeq {e f : E} {z w : D} (h : χ e z = χ f w) :
      (‖z.val‖ = 1 ∧ ‖w.val‖ = 1) ∨ (e = f ∧ z = w) := by
    by_cases hz : ‖z.val‖ = 1
    · left
      exact ⟨hz, (hχroot f w).mp (h.symm.trans ((hχroot e z).mpr hz))⟩
    · have hw : ‖w.val‖ ≠ 1 := by
        intro hw
        exact hz ((hχroot e z).mp (h.trans ((hχroot f w).mpr hw)))
      exact Or.inr ((hinj e f z w (lt_of_le_of_ne (hbound z) hz)
        (lt_of_le_of_ne (hbound w) hw)).mp h)
  let V : Set W := {w | w = b ∨ ∃ e z, 1 / 2 < ‖z.val‖ ∧ χ e z = w}
  let U : E → Set W := fun e ↦ V ∪ Set.range (χ e)
  have hb : b ∈ V := Or.inl rfl
  have hV (e : E) (z : D) : χ e z ∈ V ↔ 1 / 2 < ‖z.val‖ := by
    constructor
    · rintro (h | ⟨f, w, hw, h⟩)
      · rw [(hχroot e z).mp h]; norm_num
      · rcases hχeq h with h | ⟨rfl, rfl⟩
        · rw [h.2]; norm_num
        · exact hw
    · intro hz
      exact Or.inr ⟨e, z, hz, rfl⟩
  have hU (e f : E) (z : D) : χ f z ∈ U e ↔ 1 / 2 < ‖z.val‖ ∨ f = e := by
    constructor
    · rintro (hz | ⟨w, hw⟩)
      · exact Or.inl ((hV f z).mp hz)
      · rcases hχeq hw with h | ⟨h, _⟩
        · left; rw [h.2]; norm_num
        · exact Or.inr h.symm
    · rintro (hz | rfl)
      · exact Or.inl ((hV f z).mpr hz)
      · exact Or.inr ⟨z, rfl⟩
  have hopenV : IsOpen V := by
    apply hπ.isOpen_preimage.mp
    apply isOpen_sum_iff.mpr
    constructor
    · change IsOpen {u : Unit | π (.inl u) ∈ V}
      have : {u : Unit | π (.inl u) ∈ V} = Set.univ := by ext u; simp [π, V, b]
      rw [this]; exact isOpen_univ
    · apply isOpen_sigma_iff.mpr
      intro e
      change IsOpen {z : D | χ e z ∈ V}
      simp_rw [hV]
      exact isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
  have hopenU (e : E) : IsOpen (U e) := by
    apply hπ.isOpen_preimage.mp
    apply isOpen_sum_iff.mpr
    constructor
    · change IsOpen {u : Unit | π (.inl u) ∈ U e}
      have : {u : Unit | π (.inl u) ∈ U e} = Set.univ := by
        ext u; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact Or.inl hb
      rw [this]; exact isOpen_univ
    · apply isOpen_sigma_iff.mpr
      intro f
      change IsOpen {z : D | χ f z ∈ U e}
      simp_rw [hU]
      by_cases hf : f = e
      · simp [hf]
      · simp only [hf, or_false]
        exact isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
  have hnorm (z : Fin 1 → ℝ) : ‖z‖ = |z 0| := by
    have hz : z = fun _ ↦ z 0 := by ext i; congr 1; exact Fin.eq_zero i
    rw [hz]
    simp
  have hpath : IsPathConnected V := by
    refine ⟨b, hb, ?_⟩
    intro y hy
    rcases hy with rfl | ⟨e, z, hz, rfl⟩
    · exact JoinedIn.refl hb
    · have hzbound : -1 ≤ z.val 0 ∧ z.val 0 ≤ 1 := by
        have := hbound z
        rw [hnorm, abs_le] at this
        exact this
      have hzabs : 1 / 2 < |z.val 0| := by rwa [hnorm] at hz
      let c : ℝ := if z.val 0 < 0 then -1 else 1
      have hc : c = -1 ∨ c = 1 := by dsimp [c]; split_ifs <;> simp
      have hcline : ∀ t : unitInterval, |(1 - (t : ℝ)) * c + (t : ℝ) * z.val 0| ≤ 1 := by
        intro t
        have ht0 := t.property.1
        have ht1 := t.property.2
        rcases hc with hc | hc <;> rw [hc, abs_le] <;> constructor <;> nlinarith
      let l : unitInterval → D := fun t ↦
        ⟨fun _ ↦ (1 - (t : ℝ)) * c + (t : ℝ) * z.val 0, by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm]
          exact hcline t⟩
      have hl : Continuous l := by
        apply Continuous.subtype_mk
        fun_prop
      have hχ : Continuous (χ e) :=
        hπ.continuous.comp (continuous_inr.comp (continuous_sigmaMk (i := e)))
      have hl0 : χ e (l 0) = b := by
        apply (hχroot e _).mpr
        rw [hnorm]
        change |(1 - (0 : ℝ)) * c + (0 : ℝ) * z.val 0| = 1
        rcases hc with hc | hc <;> simp [hc]
      have hl1 : l 1 = z := by
        apply Subtype.ext
        funext i
        change (1 - (1 : ℝ)) * c + (1 : ℝ) * z.val 0 = z.val i
        simp [Fin.eq_zero i]
      let p : Path b (χ e z) :=
        ⟨⟨fun t ↦ χ e (l t), hχ.comp hl⟩, hl0, by change χ e (l 1) = χ e z; rw [hl1]⟩
      refine ⟨p, fun t ↦ (hV e (l t)).mpr ?_⟩
      rw [hnorm]
      change 1 / 2 < |(1 - (t : ℝ)) * c + (t : ℝ) * z.val 0|
      have ht0 := t.property.1
      have ht1 := t.property.2
      by_cases hneg : z.val 0 < 0
      · have hz' : z.val 0 < -(1 / 2) := by rw [abs_of_neg hneg] at hzabs; linarith
        have hc' : c = -1 := ite_eq_left hneg
        rw [hc']
        have hn : (1 - (t : ℝ)) * (-1) + (t : ℝ) * z.val 0 < -(1 / 2) := by nlinarith
        rw [abs_of_neg (by linarith)]
        linarith
      · have hz' : 1 / 2 < z.val 0 := by rwa [abs_of_nonneg (le_of_not_gt hneg)] at hzabs
        have hc' : c = 1 := ite_eq_right hneg
        rw [hc']
        have hn : 1 / 2 < (1 - (t : ℝ)) * 1 + (t : ℝ) * z.val 0 := by nlinarith
        rw [abs_of_pos (by linarith)]
        exact hn
  let radial (c : ℝ) (hc : |c| ≤ 1) (z : D) (t : unitInterval) : D :=
    ⟨fun _ ↦ (1 - (t : ℝ)) * z.val 0 + (t : ℝ) * c, by
      rw [Metric.mem_closedBall, dist_zero_right, hnorm]
      have hz : -1 ≤ z.val 0 ∧ z.val 0 ≤ 1 := by
        simpa only [hnorm, abs_le] using hbound z
      have hc' := abs_le.mp hc
      have ht0 := t.property.1
      have ht1 := t.property.2
      rw [abs_le]
      constructor <;> nlinarith⟩
  have hradial (c : ℝ) (hc : |c| ≤ 1) :
      Continuous (fun p : D × unitInterval ↦ radial c hc p.1 p.2) := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst))).add
      ((continuous_subtype_val.comp continuous_snd).mul continuous_const)
  let radialMap (e : E) (c : ℝ) (hc : |c| ≤ 1) : C(D, C(unitInterval, W)) :=
    ContinuousMap.curry ⟨fun p ↦ χ e (radial c hc p.1 p.2),
      (hπ.continuous.comp (continuous_inr.comp (continuous_sigmaMk (i := e)))).comp
        (hradial c hc)⟩
  let F : Unit ⊕ (Σ _ : E, D) → C(unitInterval, W) :=
    Sum.elim (fun _ ↦ ContinuousMap.const _ b)
      (fun p ↦ if p.2.val 0 < 0 then radialMap p.1 (-1) (by norm_num) p.2
        else radialMap p.1 1 (by norm_num) p.2)
  have hFboundary (e : E) (z : D) (hz : ‖z.val‖ = 1) :
      F (.inr ⟨e, z⟩) = ContinuousMap.const _ b := by
    have hzabs : |z.val 0| = 1 := by rwa [hnorm] at hz
    apply ContinuousMap.ext
    intro t
    change (if z.val 0 < 0 then radialMap e (-1) (by norm_num) z else radialMap e 1 (by norm_num) z) t = b
    split_ifs with hneg
    · have hz0 : z.val 0 = -1 := by rw [abs_of_neg hneg] at hzabs; linarith
      apply (hχroot e _).mpr
      rw [hnorm]
      change |(1 - (t : ℝ)) * z.val 0 + (t : ℝ) * (-1)| = 1
      rw [hz0]; ring_nf; norm_num
    · have hz0 : z.val 0 = 1 := by rwa [abs_of_nonneg (le_of_not_gt hneg)] at hzabs
      apply (hχroot e _).mpr
      rw [hnorm]
      change |(1 - (t : ℝ)) * z.val 0 + (t : ℝ) * 1| = 1
      rw [hz0]; ring_nf; norm_num
  have hFeq : ∀ p r, π p = π r → F p = F r := by
    intro p r heq
    cases p with
    | inl u =>
      cases r with
      | inl v => rfl
      | inr r => exact (hFboundary r.1 r.2 ((hχroot r.1 r.2).mp heq.symm)).symm
    | inr p =>
      cases r with
      | inl u => exact hFboundary p.1 p.2 ((hχroot p.1 p.2).mp heq)
      | inr r =>
        rcases hχeq heq with ⟨hp, hr⟩ | ⟨he, hz⟩
        · rw [hFboundary _ _ hp, hFboundary _ _ hr]
        · cases p; cases r; cases he; cases hz; rfl
  let sel : W → Unit ⊕ (Σ _ : E, D) := fun w ↦ (hπ.surjective w).choose
  have hsel (w : W) : π (sel w) = w := (hπ.surjective w).choose_spec
  let G : W → C(unitInterval, W) := fun w ↦ F (sel w)
  have hGπ (p) : G (π p) = F p := hFeq _ _ (hsel (π p))
  have hFcont : ContinuousOn F (π ⁻¹' V) := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    cases p with
    | inl u =>
      apply IsOpenEmbedding.inl.continuousAt_iff.mp
      exact continuousAt_const
    | inr p =>
      obtain ⟨e, z⟩ := p
      apply (IsOpenEmbedding.inr.comp (IsOpenEmbedding.sigmaMk (i := e))).continuousAt_iff.mp
      have hz : 1 / 2 < |z.val 0| := by
        rw [← hnorm]
        exact (hV e z).mp hp
      by_cases hneg : z.val 0 < 0
      · have hevent : ∀ᶠ w : D in nhds z, w.val 0 < 0 :=
          (isOpen_lt (continuous_apply 0 |>.comp continuous_subtype_val)
            continuous_const).mem_nhds hneg
        apply (radialMap e (-1) (by norm_num)).continuous.continuousAt.congr_of_eventuallyEq
        filter_upwards [hevent] with w hw
        exact ite_eq_left hw
      · have hpos : 0 < z.val 0 := by
          rw [abs_of_nonneg (le_of_not_gt hneg)] at hz
          linarith
        have hevent : ∀ᶠ w : D in nhds z, 0 < w.val 0 :=
          (isOpen_lt continuous_const
            (continuous_apply 0 |>.comp continuous_subtype_val)).mem_nhds hpos
        apply (radialMap e 1 (by norm_num)).continuous.continuousAt.congr_of_eventuallyEq
        filter_upwards [hevent] with w hw
        exact ite_eq_right (not_lt_of_ge hw.le)
  have hGcont : ContinuousOn G V :=
    (hπ.continuousOn_isOpen_iff hopenV).mpr (hFcont.congr (fun p _ ↦ hGπ p))
  let H : C(unitInterval × V, W) :=
    ⟨fun p ↦ G p.2.val p.1, (continuous_eval.comp
      ((hGcont.domRestrict.comp continuous_snd).prodMk continuous_fst))⟩
  have hFzero (p) : F p 0 = π p := by
    cases p with
    | inl u => rfl
    | inr p =>
      obtain ⟨e, z⟩ := p
      have hr (c : ℝ) (hc : |c| ≤ 1) : radial c hc z 0 = z := by
        apply Subtype.ext
        funext i
        change (1 - (0 : ℝ)) * z.val 0 + (0 : ℝ) * c = z.val i
        simp [Fin.eq_zero i]
      dsimp only [F, Sum.elim_inr]
      split_ifs
      · exact congrArg (χ e) (hr (-1) (by norm_num))
      · exact congrArg (χ e) (hr 1 (by norm_num))
  have hFone (p) : F p 1 = b := by
    cases p with
    | inl u => rfl
    | inr p =>
      obtain ⟨e, z⟩ := p
      dsimp only [F, Sum.elim_inr]
      split_ifs <;> apply (hχroot e _).mpr <;> rw [hnorm] <;>
        change |(1 - (1 : ℝ)) * z.val 0 + (1 : ℝ) * _| = 1 <;> norm_num
  have hH0 (y : V) : H (0, y) = y.val := by
    change F (sel y.val) 0 = y.val
    rw [hFzero, hsel]
  have hH1 (y : V) : H (1, y) = b := hFone (sel y.val)
  have hHb (t) : H (t, ⟨b, hb⟩) = b := by
    change G (π (.inl ())) t = b
    rw [hGπ]
    rfl
  have hHmem (p) : H p ∈ V := by
    obtain ⟨t, y⟩ := p
    obtain ⟨r, hr⟩ := hπ.surjective y.val
    change π r = y.val at hr
    have hy : π r ∈ V := by rw [hr]; exact y.property
    change G y.val t ∈ V
    rw [← hr, hGπ]
    cases r with
    | inl u => exact hb
    | inr r =>
      obtain ⟨e, z⟩ := r
      have hzabs : 1 / 2 < |z.val 0| := by
        rw [← hnorm]
        exact (hV e z).mp hy
      have ht0 := t.property.1
      have ht1 := t.property.2
      have hzbound : -1 ≤ z.val 0 ∧ z.val 0 ≤ 1 := by
        simpa only [hnorm, abs_le] using hbound z
      dsimp only [F, Sum.elim_inr]
      split_ifs with hneg
      · apply (hV e _).mpr
        rw [hnorm]
        change 1 / 2 < |(1 - (t : ℝ)) * z.val 0 + (t : ℝ) * (-1)|
        rw [abs_of_neg hneg] at hzabs
        have hn : (1 - (t : ℝ)) * z.val 0 + (t : ℝ) * (-1) < -(1 / 2) := by
          nlinarith [mul_nonneg ht0 (show 0 ≤ z.val 0 + 1 by linarith)]
        rw [abs_of_neg (by linarith)]
        linarith
      · apply (hV e _).mpr
        rw [hnorm]
        change 1 / 2 < |(1 - (t : ℝ)) * z.val 0 + (t : ℝ) * 1|
        rw [abs_of_nonneg (le_of_not_gt hneg)] at hzabs
        have hn : 1 / 2 < (1 - (t : ℝ)) * z.val 0 + (t : ℝ) * 1 := by
          nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hzbound.2)]
        rw [abs_of_pos (by linarith)]
        exact hn
  have hGlift (e : E) (z : D) : ∃ v : D,
      (v.val = (fun _ ↦ -1) ∨ v.val = (fun _ ↦ 1)) ∧
      ∃ l : Path z v, ∀ t, G (χ e z) t = χ e (l t) := by
    have hr0 (c : ℝ) (hc : |c| ≤ 1) : radial c hc z 0 = z := by
      apply Subtype.ext
      funext i
      change (1 - (0 : ℝ)) * z.val 0 + (0 : ℝ) * c = z.val i
      simp [Fin.eq_zero i]
    by_cases hz : z.val 0 < 0
    · let v : D := ⟨fun _ ↦ -1, by simp [D, Metric.mem_closedBall, dist_zero_right]⟩
      let l : Path z v := ⟨⟨radial (-1) (by norm_num) z,
        (hradial (-1) (by norm_num)).comp (continuous_const.prodMk continuous_id)⟩,
        hr0 (-1) (by norm_num), by apply Subtype.ext; funext i; simp [radial, v]⟩
      refine ⟨v, Or.inl rfl, l, ?_⟩
      intro t
      change G (π (.inr ⟨e, z⟩)) t = _
      rw [hGπ]
      simp only [F, Sum.elim_inr, hz, ite_true]
      rfl
    · let v : D := ⟨fun _ ↦ 1, by simp [D, Metric.mem_closedBall, dist_zero_right]⟩
      let l : Path z v := ⟨⟨radial 1 (by norm_num) z,
        (hradial 1 (by norm_num)).comp (continuous_const.prodMk continuous_id)⟩,
        hr0 1 (by norm_num), by apply Subtype.ext; funext i; simp [radial, v]⟩
      refine ⟨v, Or.inr rfl, l, ?_⟩
      intro t
      change G (π (.inr ⟨e, z⟩)) t = _
      rw [hGπ]
      simp only [F, Sum.elim_inr, hz, ite_false]
      rfl
  refine ⟨V, U, hopenV, hopenU, ?_, ?_, ?_, hV, hb, H, hH0, hH1, hHb, hHmem, G, ?_, ?_, hHb, ?_, hGlift⟩
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨p, rfl⟩ := hπ.surjective y
    cases p with
    | inl u => exact Or.inl hb
    | inr p => exact Or.inr (Set.mem_iUnion.mpr ⟨p.1, Or.inr ⟨p.2, rfl⟩⟩)
  · intro e
    have : V ∩ U e = V := Set.inter_eq_left.mpr Set.subset_union_left
    rw [this]; exact hpath
  · intro e z _
    exact Or.inr ⟨z, rfl⟩
  · intro y
    change F (sel y) 0 = y
    rw [hFzero, hsel]
  · intro y
    exact hFone (sel y)
  · intro y hy t
    exact hHmem (t, ⟨y, hy⟩)

end HolomorphicAnosov
