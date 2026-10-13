import HolomorphicAnosov.Analysis.Regularity.AmbientJourneRegularityCore
import HolomorphicAnosov.Analysis.Regularity.GraphFoliationData
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov
open Set JourneLeafPolynomialApproximation
open scoped Manifold ContDiff

/-- The actual native smaller-box construction required by parent J1. Its image is the
range of the original chart restricted to the two smaller centered balls; its chart is the
homeomorphism onto this range supplied by the actual embedding. All graph and frame data
are retained literally. Source: original common-domain shrinking in Journé pp.187–188. -/
theorem restricted_box_exists
    {d c N n : ℕ} {Ω : Set (Block N)} (b : GraphBox d c N 1 0 Ω)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hrb : r < b.leafRadius) (hsb : s < b.transverseRadius)
    (hb : ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ Metric.ball 0 s,
      HasFiniteHolderBounds n (1 / 2) K (b.graph w) (Metric.ball 0 r)) :
    ∃ b' : GraphBox d c N n (1 / 2) Ω,
      b'.base = b.base ∧ b'.frame = b.frame ∧ b'.graph = b.graph ∧
        b'.leafRadius = r ∧ b'.transverseRadius = s ∧
          ∀ z : ↥(Metric.ball (0 : Block d) b'.leafRadius ×ˢ
            Metric.ball (0 : Block c) b'.transverseRadius),
            ∃ z₀ : ↥(Metric.ball (0 : Block d) b.leafRadius ×ˢ
              Metric.ball (0 : Block c) b.transverseRadius),
              z₀.val = z.val ∧ (b'.chart z).val = (b.chart z₀).val := by
  let D := Metric.ball (0 : Block d) r ×ˢ Metric.ball (0 : Block c) s
  let Q := Metric.ball (0 : Block d) b.leafRadius ×ˢ
    Metric.ball (0 : Block c) b.transverseRadius
  have hDQ : D ⊆ Q := fun z hz ↦
    ⟨Metric.ball_subset_ball hrb.le hz.1, Metric.ball_subset_ball hsb.le hz.2⟩
  let inc : D → Q := Set.inclusion hDQ
  let g : D → Block N := fun z ↦ (b.chart (inc z)).val
  have hemb : Topology.IsEmbedding g :=
    (Topology.IsEmbedding.subtypeVal.comp b.chart.isEmbedding).comp
      (Topology.IsEmbedding.inclusion hDQ)
  have hopen : IsOpenMap g :=
    (b.image_open.isOpenMap_subtype_val.comp b.chart.isOpenMap).comp
      ((Metric.isOpen_ball.prod Metric.isOpen_ball).isOpenMap_inclusion hDQ)
  have himage : IsOpen (Set.range g) := by
    simpa only [Set.image_univ] using hopen Set.univ isOpen_univ
  have hsubset : Set.range g ⊆ Ω := by
    rintro y ⟨z, rfl⟩
    exact b.image_subset (b.chart (inc z)).property
  let b' : GraphBox d c N n (1 / 2) Ω :=
    { base := b.base
      leafRadius := r
      transverseRadius := s
      leafRadius_pos := hr
      transverseRadius_pos := hs
      frame := b.frame
      graph := b.graph
      image := Set.range g
      image_open := himage
      image_subset := hsubset
      chart := hemb.toHomeomorph
      chart_formula := fun z ↦ b.chart_formula (inc z)
      graph_continuous := b.graph_continuous.mono hDQ
      first_jet_continuous := b.first_jet_continuous.mono hDQ
      graph_bounds := hb }
  exact ⟨b', rfl, rfl, rfl, rfl, rfl, fun z ↦ ⟨inc z, rfl, rfl⟩⟩

/-- Restrictions with the same graph and frame have exactly the original inverse coordinates.
Source: parent J1; injectivity of the original chart and its literal graph formula. -/
theorem restricted_box_coordinates
    {d c N n : ℕ} {Ω : Set (Block N)} (b : GraphBox d c N 1 0 Ω)
    (b' : GraphBox d c N n (1 / 2) Ω)
    (hb : b'.base = b.base) (hfr : b'.frame = b.frame) (hg : b'.graph = b.graph)
    (hr : b'.leafRadius ≤ b.leafRadius) (hs : b'.transverseRadius ≤ b.transverseRadius)
    (a : Block N) (ha : a ∈ b'.image) :
    ∃ ha₀ : a ∈ b.image,
      (b'.chart.symm ⟨a, ha⟩).val = (b.chart.symm ⟨a, ha₀⟩).val := by
  let z := b'.chart.symm ⟨a, ha⟩
  let z₀ : ↥(Metric.ball (0 : Block d) b.leafRadius ×ˢ
      Metric.ball (0 : Block c) b.transverseRadius) :=
    ⟨z.val, Metric.ball_subset_ball hr z.property.1,
      Metric.ball_subset_ball hs z.property.2⟩
  have heq : (b.chart z₀).val = a := by
    calc
      (b.chart z₀).val = b.base + b.frame (z.val.1, b.graph z.val.2 z.val.1) :=
        b.chart_formula z₀
      _ = (b'.chart z).val := by rw [b'.chart_formula, hb, hfr, hg]
      _ = a := congrArg Subtype.val (b'.chart.apply_symm_apply ⟨a, ha⟩)
  have ha₀ : a ∈ b.image := heq ▸ (b.chart z₀).property
  refine ⟨ha₀, ?_⟩
  have hz₀ : b.chart.symm ⟨a, ha₀⟩ = z₀ := by
    apply b.chart.injective
    exact (b.chart.apply_symm_apply _).trans (Subtype.ext heq).symm
  rw [hz₀]

/-- Restriction preserves the actual global plaque map and hence the original tangent range.
Source: parent J1, with no independently supplied distribution. -/
theorem restricted_box_tangent
    {d c N n : ℕ} {Ω : Set (Block N)} (b : GraphBox d c N 1 0 Ω)
    (b' : GraphBox d c N n (1 / 2) Ω)
    (hb : b'.base = b.base) (hfr : b'.frame = b.frame) (hg : b'.graph = b.graph)
    (hr : b'.leafRadius ≤ b.leafRadius) (hs : b'.transverseRadius ≤ b.transverseRadius)
    (a : Block N) (ha : a ∈ b'.image) :
    ∃ ha₀ : a ∈ b.image, b'.tangent a ha = b.tangent a ha₀ := by
  obtain ⟨ha₀, hcoord⟩ := restricted_box_coordinates b b' hb hfr hg hr hs a ha
  have hplaque : b'.plaque = b.plaque := by
    funext w x
    simp only [GraphBox.plaque, hb, hfr, hg]
  refine ⟨ha₀, ?_⟩
  simp only [GraphBox.tangent, hcoord, hplaque]

/-- Atlas restrictions inherit the original local slice-preserving overlaps. The overlap
neighborhood is intersected with the smaller source ball and the preimage of the smaller
receiving OPEN image. Source: parent J1 and the original GraphFoliation overlap field. -/
theorem restricted_atlas_overlap
    {d c N n : ℕ} {Ω : Set (Block N)} (F : GraphFoliation d c N 1 0 Ω)
    {J : Type} (B : J → GraphBox d c N n (1 / 2) Ω) (parent : J → F.Index)
    (hb : ∀ j, (B j).base = (F.box (parent j)).base)
    (hfr : ∀ j, (B j).frame = (F.box (parent j)).frame)
    (hg : ∀ j, (B j).graph = (F.box (parent j)).graph)
    (hr : ∀ j, (B j).leafRadius ≤ (F.box (parent j)).leafRadius)
    (hs : ∀ j, (B j).transverseRadius ≤ (F.box (parent j)).transverseRadius) :
    ∀ (i j : J)
      (z : ↥(Metric.ball (0 : Block d) (B i).leafRadius ×ˢ
        Metric.ball (0 : Block c) (B i).transverseRadius))
      (hz : ((B i).chart z).val ∈ (B j).image),
      ∃ V : Set (Block d), IsOpen V ∧ z.val.1 ∈ V ∧
        V ⊆ Metric.ball 0 (B i).leafRadius ∧
        ∀ x ∈ V, ∃ hx : (B i).plaque z.val.2 x ∈ (B j).image,
          (B j).transverseLabel ((B i).plaque z.val.2 x) hx =
            (B j).transverseLabel ((B i).chart z).val hz := by
  have hcoords := fun j a ha ↦ restricted_box_coordinates (F.box (parent j)) (B j)
    (hb j) (hfr j) (hg j) (hr j) (hs j) a ha
  have hsub : ∀ j, (B j).image ⊆ (F.box (parent j)).image :=
    fun j a ha ↦ (hcoords j a ha).choose
  have hlabel : ∀ j a (ha : a ∈ (B j).image),
      (B j).transverseLabel a ha =
        (F.box (parent j)).transverseLabel a (hsub j ha) := by
    intro j a ha
    exact congrArg Prod.snd (hcoords j a ha).choose_spec
  have hplaque : ∀ j, (B j).plaque = (F.box (parent j)).plaque := by
    intro j
    funext w x
    simp only [GraphBox.plaque, hb j, hfr j, hg j]
  intro i j z hz
  let z₀ : ↥(Metric.ball (0 : Block d) (F.box (parent i)).leafRadius ×ˢ
      Metric.ball (0 : Block c) (F.box (parent i)).transverseRadius) :=
    ⟨z.val, Metric.ball_subset_ball (hr i) z.property.1,
      Metric.ball_subset_ball (hs i) z.property.2⟩
  have hz₀ : ((F.box (parent i)).chart z₀).val = ((B i).chart z).val := by
    rw [(F.box (parent i)).chart_formula, (B i).chart_formula, hb i, hfr i, hg i]
  obtain ⟨V, hVopen, hzV, hVsub, hVoverlap⟩ := F.overlap (parent i) (parent j) z₀
    (hz₀.symm ▸ hsub j hz)
  have hgraph : ContinuousOn ((B i).graph z.val.2) (Metric.ball 0 (B i).leafRadius) :=
    (((B i).graph_bounds.choose_spec.2 z.val.2 z.property.2).1).continuousOn
  have hcont : ContinuousOn ((B i).plaque z.val.2) (Metric.ball 0 (B i).leafRadius) :=
    continuousOn_const.add ((B i).frame.continuous.comp_continuousOn
      (continuousOn_id.prodMk hgraph))
  let W := Metric.ball (0 : Block d) (B i).leafRadius ∩
    (B i).plaque z.val.2 ⁻¹' (B j).image
  have hW : IsOpen W := hcont.isOpen_inter_preimage Metric.isOpen_ball (B j).image_open
  refine ⟨V ∩ W, hVopen.inter hW, ⟨hzV, z.property.1, ?_⟩,
    fun x hx ↦ hx.2.1, ?_⟩
  · change (B i).plaque z.val.2 z.val.1 ∈ (B j).image
    rw [show (B i).plaque z.val.2 z.val.1 = ((B i).chart z).val from
      ((B i).chart_formula z).symm]
    exact hz
  · intro x hx
    have hxj : (B i).plaque z.val.2 x ∈ (B j).image := hx.2.2
    obtain ⟨hxold, heq⟩ := hVoverlap x hx.1
    refine ⟨hxj, ?_⟩
    rw [hlabel j _ hxj, hlabel j _ hz]
    simpa only [hplaque i, hz₀] using heq

/-- Parent J1's whole atlas refinement. Index all original boxes and strictly smaller
centered source radii. Original smoothness and locally uniform spatial bounds provide the
finite half-Hölder graph and scalar bounds. Every original source point lies in one such
smaller product ball. The overlap and tangent compatibility are the actual ones proved above.
Source: Journé pp.187–188, parent J1's finite-order localization; no parameter derivative. -/
theorem refine_smooth_foliation
    {d c N : ℕ} {Ω : Set (Block N)} (F : GraphFoliation d c N 1 0 Ω)
    (f : Block N → ℝ) (n : ℕ)
    (hsm : ∀ i : F.Index,
      ∀ w ∈ Metric.ball 0 (F.box i).transverseRadius,
        ContDiffOn ℝ ∞ ((F.box i).graph w) (Metric.ball 0 (F.box i).leafRadius) ∧
        ContDiffOn ℝ ∞ (f ∘ (F.box i).plaque w) (Metric.ball 0 (F.box i).leafRadius))
    (hbound : ∀ i : F.Index,
      ∀ r : ℝ, 0 < r → r < (F.box i).leafRadius →
        ∀ s : ℝ, 0 < s → s < (F.box i).transverseRadius →
          ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧
            ∀ w ∈ Metric.ball (0 : Block c) s, ∀ x ∈ Metric.ball (0 : Block d) r,
              ‖iteratedFDeriv ℝ j ((F.box i).graph w) x‖ ≤ K ∧
                ‖iteratedFDeriv ℝ j (f ∘ (F.box i).plaque w) x‖ ≤ K) :
    ∃ F' : GraphFoliation d c N n (1 / 2) Ω,
      HasLeafwiseHolderBounds F' f ∧
        ∃ parent : F'.Index → F.Index,
          ∀ i a (ha : a ∈ (F'.box i).image),
            ∃ ha₀ : a ∈ (F.box (parent i)).image,
              (F'.box i).tangent a ha = (F.box (parent i)).tangent a ha₀ := by
  classical
  let J := {t : F.Index × (ℝ × ℝ) //
    0 < t.2.1 ∧ t.2.1 < (F.box t.1).leafRadius ∧
      0 < t.2.2 ∧ t.2.2 < (F.box t.1).transverseRadius}
  have hgraphbounds : ∀ j : J,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ Metric.ball 0 j.val.2.2,
        HasFiniteHolderBounds n (1 / 2) K ((F.box j.val.1).graph w)
          (Metric.ball 0 j.val.2.1) := by
    intro j
    apply uniform_half_holder_from_smooth_bounds ((F.box j.val.1).graph)
      (Metric.ball 0 j.val.2.2) n j.property.1
    · intro w hw
      exact ((hsm j.val.1 w (Metric.ball_subset_ball j.property.2.2.2.le hw)).1).mono
        (Metric.ball_subset_ball j.property.2.1.le)
    · intro k
      obtain ⟨K, hK, hb⟩ := hbound j.val.1 _ j.property.1 j.property.2.1
        _ j.property.2.2.1 j.property.2.2.2 k
      exact ⟨K, hK, fun w hw x hx ↦ (hb w hw x hx).1⟩
  have hboxes := fun j : J ↦ restricted_box_exists (F.box j.val.1)
    j.val.2.1 j.val.2.2 j.property.1 j.property.2.2.1
    j.property.2.1 j.property.2.2.2 (hgraphbounds j)
  choose B hbase hframe hgraph hleaf htrans hchart using hboxes
  have hr : ∀ j : J, (B j).leafRadius ≤ (F.box j.val.1).leafRadius := by
    intro j
    rw [hleaf j]
    exact j.property.2.1.le
  have hs : ∀ j : J, (B j).transverseRadius ≤ (F.box j.val.1).transverseRadius := by
    intro j
    rw [htrans j]
    exact j.property.2.2.2.le
  have hcover : ∀ a ∈ Ω, ∃ j : J, a ∈ (B j).image := by
    intro a ha
    obtain ⟨i, hai⟩ := F.cover a ha
    let z := (F.box i).chart.symm ⟨a, hai⟩
    have hx : ‖z.val.1‖ < (F.box i).leafRadius := by
      simpa only [Metric.mem_ball, dist_zero_right] using z.property.1
    have hw : ‖z.val.2‖ < (F.box i).transverseRadius := by
      simpa only [Metric.mem_ball, dist_zero_right] using z.property.2
    obtain ⟨r, hxr, hrR⟩ := exists_between hx
    obtain ⟨s, hws, hsS⟩ := exists_between hw
    let j : J := ⟨(i, r, s), lt_of_le_of_lt (norm_nonneg _) hxr, hrR,
      lt_of_le_of_lt (norm_nonneg _) hws, hsS⟩
    let z' : ↥(Metric.ball (0 : Block d) (B j).leafRadius ×ˢ
      Metric.ball (0 : Block c) (B j).transverseRadius) :=
      ⟨z.val, by rw [hleaf j]; simpa [j, Metric.mem_ball, dist_zero_right] using hxr,
        by rw [htrans j]; simpa [j, Metric.mem_ball, dist_zero_right] using hws⟩
    have heq : ((B j).chart z').val = a := by
      calc
        ((B j).chart z').val = (F.box i).base +
            (F.box i).frame (z.val.1, (F.box i).graph z.val.2 z.val.1) := by
          rw [(B j).chart_formula, hbase j, hframe j, hgraph j]
        _ = ((F.box i).chart z).val := ((F.box i).chart_formula z).symm
        _ = a := congrArg Subtype.val ((F.box i).chart.apply_symm_apply ⟨a, hai⟩)
    exact ⟨j, heq ▸ ((B j).chart z').property⟩
  let F' : GraphFoliation d c N n (1 / 2) Ω :=
    { Index := J
      box := B
      cover := hcover
      overlap := restricted_atlas_overlap F B (fun j ↦ j.val.1)
        hbase hframe hgraph hr hs }
  refine ⟨F', ?_, fun j ↦ j.val.1, ?_⟩
  · intro j
    have hplaque : (B j).plaque = (F.box j.val.1).plaque := by
      funext w x
      simp only [GraphBox.plaque, hbase j, hframe j, hgraph j]
    change ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ Metric.ball 0 (B j).transverseRadius,
      HasFiniteHolderBounds n (1 / 2) K (f ∘ (B j).plaque w)
        (Metric.ball 0 (B j).leafRadius)
    rw [hplaque, hleaf j, htrans j]
    apply uniform_half_holder_from_smooth_bounds (fun w ↦ f ∘ (F.box j.val.1).plaque w)
      (Metric.ball 0 j.val.2.2) n j.property.1
    · intro w hw
      exact ((hsm j.val.1 w (Metric.ball_subset_ball j.property.2.2.2.le hw)).2).mono
        (Metric.ball_subset_ball j.property.2.1.le)
    · intro k
      obtain ⟨K, hK, hb⟩ := hbound j.val.1 _ j.property.1 j.property.2.1
        _ j.property.2.2.1 j.property.2.2.2 k
      exact ⟨K, hK, fun w hw x hx ↦ (hb w hw x hx).2⟩
  · intro j a ha
    exact restricted_box_tangent (F.box j.val.1) (B j)
      (hbase j) (hframe j) (hgraph j) (hr j) (hs j) a ha


end HolomorphicAnosov
