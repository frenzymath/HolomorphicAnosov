import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Topology.Covering.Basic

noncomputable section

/-! The file proves gluing and covering criteria for compatible holomorphic charts. (Lyubich, §2.4.13) -/

namespace HolomorphicAnosov
open Set Filter
open scoped _root_.Topology

/-- Compatible biholomorphic partial charts glue to a holomorphic map on their covered open domain, retaining the same charts as local inverses. -/
theorem exists_glued_biholomorphic_charts {ι : Type*} (e : ι → OpenPartialHomeomorph ℂ ℂ)
    (U : Set ℂ) (hsource : ∀ i, (e i).source ⊆ U)
    (hcover : ∀ z ∈ U, ∃ i, z ∈ (e i).source)
    (hcompat : ∀ i j, EqOn (e i) (e j) ((e i).source ∩ (e j).source))
    (hhol : ∀ i, DifferentiableOn ℂ (e i) (e i).source)
    (hinv : ∀ i, DifferentiableOn ℂ (e i).symm (e i).target) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      (∀ i, EqOn (e i) f (e i).source) ∧
      ∀ z ∈ U, ∃ c : OpenPartialHomeomorph ℂ ℂ,
        z ∈ c.source ∧ c.source ⊆ U ∧ EqOn c f c.source ∧
          DifferentiableOn ℂ c c.source ∧ DifferentiableOn ℂ c.symm c.target := by
  classical
  let f : ℂ → ℂ := fun z ↦ if h : ∃ i, z ∈ (e i).source then e h.choose z else 0
  have heq (i : ι) : EqOn (e i) f (e i).source := by
    intro z hz
    have hex : ∃ j, z ∈ (e j).source := ⟨i, hz⟩
    dsimp only [f]
    rw [dite_eq_left hex]
    exact hcompat i hex.choose ⟨hz, hex.choose_spec⟩
  refine ⟨f, ?_, heq, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    apply (((hhol i).differentiableAt ((e i).open_source.mem_nhds hi)).congr_of_eventuallyEq
      ?_).differentiableWithinAt
    filter_upwards [(e i).open_source.mem_nhds hi] with w hw
    exact (heq i hw).symm
  · intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    exact ⟨e i, hi, hsource i, heq i, hhol i, hinv i⟩

/-- Disjoint partial-homeomorphism sheets with a common open target give an evenly covered neighborhood when they exhaust its preimage. -/
theorem isEvenlyCovered_of_disjoint_charts
    {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X] [Nonempty ι]
    (f : E → X) (e : ι → OpenPartialHomeomorph E X) (V : Set X)
    (htarget : ∀ i, (e i).target = V)
    (heq : ∀ i, EqOn (e i) f (e i).source)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (e i).source (e j).source))
    (hexhaust : f ⁻¹' V ⊆ ⋃ i, (e i).source) {x : X} (hx : x ∈ V) :
    IsEvenlyCovered f x (f ⁻¹' {x}) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  have : Nonempty E := ⟨(e i₀).symm x⟩
  let : TopologicalSpace ι := ⊥
  have : DiscreteTopology ι := ⟨rfl⟩
  have hV : IsOpen V := htarget i₀ ▸ (e i₀).open_target
  have hopen (i : ι) {W : Set X} (hWV : W ⊆ V) :
      IsOpen W ↔ IsOpen (f ⁻¹' W ∩ (e i).source) := by
    have hWe : W ⊆ (e i).target := htarget i ▸ hWV
    have hset : f ⁻¹' W ∩ (e i).source = (e i).symm '' W := by
      ext z
      constructor
      · intro hz
        exact ⟨e i z, (heq i hz.2).symm ▸ hz.1, (e i).left_inv hz.2⟩
      · rintro ⟨y, hy, rfl⟩
        have hys := (e i).map_target (hWe hy)
        refine ⟨?_, hys⟩
        change f ((e i).symm y) ∈ W
        rwa [← heq i hys, (e i).right_inv (hWe hy)]
    rw [hset]
    exact ((e i).isOpen_symm_image_iff_of_subset_target hWe).symm
  have hinj (i : ι) : InjOn f (e i).source := by
    intro a ha b hb hab
    apply (e i).injOn ha hb
    rw [heq i ha, heq i hb, hab]
  have hsurj (i : ι) : SurjOn f (e i).source V := by
    intro y hy
    have hyt : y ∈ (e i).target := htarget i ▸ hy
    refine ⟨(e i).symm y, (e i).map_target hyt, ?_⟩
    rw [← heq i ((e i).map_target hyt), (e i).right_inv hyt]
  let t := hV.trivializationDiscrete (f := f) (fun i ↦ (e i).source) V
    hopen hinj hsurj hdisjoint hexhaust
  exact (IsEvenlyCovered.of_trivialization (t := t) hx).to_isEvenlyCovered_preimage

/-- The same sheet criterion for a map whose actual source is an open subset of the complex plane. -/
theorem isEvenlyCovered_on_open_subset_of_disjoint_charts
    {ι : Type*} [Nonempty ι] (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (e : ι → OpenPartialHomeomorph ℂ ℂ) (V : Set ℂ)
    (hsource : ∀ i, (e i).source ⊆ U)
    (htarget : ∀ i, (e i).target = V)
    (heq : ∀ i, EqOn (e i) f (e i).source)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (e i).source (e j).source))
    (hexhaust : U ∩ f ⁻¹' V ⊆ ⋃ i, (e i).source) {x : ℂ} (hx : x ∈ V) :
    IsEvenlyCovered (fun z : U ↦ f z.val) x
      ((fun z : U ↦ f z.val) ⁻¹' {x}) := by
  classical
  let D : TopologicalSpace.Opens ℂ := ⟨U, hU⟩
  let i₀ : ι := Classical.choice inferInstance
  have hxt : x ∈ (e i₀).target := htarget i₀ ▸ hx
  have hD : Nonempty D := ⟨⟨(e i₀).symm x, hsource i₀ ((e i₀).map_target hxt)⟩⟩
  let e' : ι → OpenPartialHomeomorph D ℂ := fun i ↦ (e i).subtypeRestr hD
  apply isEvenlyCovered_of_disjoint_charts (fun z : D ↦ f z.val) e' V
  · intro i
    ext y
    change (y ∈ (e i).target ∧ (e i).symm y ∈
      (D.openPartialHomeomorphSubtypeCoe hD).target) ↔ y ∈ V
    rw [D.openPartialHomeomorphSubtypeCoe_target]
    constructor
    · intro hy
      exact htarget i ▸ hy.1
    · intro hy
      have hyt : y ∈ (e i).target := htarget i ▸ hy
      exact ⟨hyt, hsource i ((e i).map_target hyt)⟩
  · intro i z hz
    have hzs : z.val ∈ (e i).source := by
      simpa only [e', OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hz
    exact heq i hzs
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    apply (Set.disjoint_left.mp (hdisjoint hij))
    · simpa only [e', OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hzi
    · simpa only [e', OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hzj
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hexhaust ⟨z.property, hz⟩)
    apply Set.mem_iUnion.mpr
    exact ⟨i, by simpa only [e', OpenPartialHomeomorph.subtypeRestr_source,
      Set.mem_preimage] using hi⟩
  · exact hx

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set

/-! The purely analytic final gluing interface. -/

/-- A family of compatible reflected word charts glues to one holomorphic map on the open disk and retains every word chart as a local inverse. -/
theorem exists_word_glued_reflection_map
    {ι : Type*} (charts : ι → OpenPartialHomeomorph ℂ ℂ)
    (hsource : ∀ i, (charts i).source ⊆ {z : ℂ | ‖z‖ < 1})
    (hcover : ∀ z, ‖z‖ < 1 → ∃ i, z ∈ (charts i).source)
    (hcompat : ∀ i j, EqOn (charts i) (charts j)
      ((charts i).source ∩ (charts j).source))
    (hhol : ∀ i, DifferentiableOn ℂ (charts i) (charts i).source)
    (hinv : ∀ i, DifferentiableOn ℂ (charts i).symm (charts i).target) :
    ∃ lam : ℂ → ℂ, DifferentiableOn ℂ lam {z : ℂ | ‖z‖ < 1} ∧
      (∀ i, EqOn (charts i) lam (charts i).source) ∧
      (∀ z, ‖z‖ < 1 → ∃ c : OpenPartialHomeomorph ℂ ℂ,
        z ∈ c.source ∧ c.source ⊆ {z : ℂ | ‖z‖ < 1} ∧
        EqOn c lam c.source ∧ DifferentiableOn ℂ c c.source ∧
        DifferentiableOn ℂ c.symm c.target) := by
  obtain ⟨lam, hlam, heq, hlocal⟩ := exists_glued_biholomorphic_charts charts
    {z : ℂ | ‖z‖ < 1} hsource hcover hcompat hhol hinv
  exact ⟨lam, hlam, heq, hlocal⟩

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set

/-- Agreement of continuous local charts on all tile interiors implies full agreement across the seams. -/
theorem charts_compatible_of_tile_interiors {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph ℂ ℂ) (tile : κ → Set ℂ)
    (tileMap : κ → ℂ → ℂ) (seam : ι → Set ℂ)
    (hpartition : ∀ i, (e i).source ⊆ (⋃ a, tile a) ∪ seam i)
    (hthin : ∀ i, interior (seam i) = ∅)
    (hformula : ∀ i a, EqOn (e i) (tileMap a) ((e i).source ∩ tile a)) :
    ∀ i j, EqOn (e i) (e j) ((e i).source ∩ (e j).source) := by
  intro i j
  let U := (e i).source ∩ (e j).source
  have hU : IsOpen U := (e i).open_source.inter (e j).open_source
  have hd : Dense (seam i)ᶜ := interior_eq_empty_iff_dense_compl.mp (hthin i)
  have heq : EqOn (e i) (e j) ((seam i)ᶜ ∩ U) := by
    intro z hz
    have ht : z ∈ ⋃ a, tile a := (hpartition i hz.2.1).resolve_right hz.1
    obtain ⟨a,ha⟩ := mem_iUnion.mp ht
    exact (hformula i a ⟨hz.2.1,ha⟩).trans (hformula j a ⟨hz.2.2,ha⟩).symm
  exact heq.of_subset_closure
    ((e i).continuousOn.mono (inter_subset_left : U ⊆ (e i).source))
    ((e j).continuousOn.mono (inter_subset_right : U ⊆ (e j).source))
    inter_subset_right (by simpa only [inter_comm U] using hd.open_subset_closure_inter hU)

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set

/-- Glued chart families with a common target in each color give a covering when the sheets of each color are disjoint and every omitted sheet point lies on a seam of a different color. -/
theorem covering_of_colored_chart_sheets
    {C : Type*} {I : C → Type*} [∀ c, Nonempty (I c)]
    (f : ℂ → ℂ) (U Ω : Set ℂ) (hU : IsOpen U)
    (E : (c : C) → I c → OpenPartialHomeomorph ℂ ℂ)
    (V : C → Set ℂ) (S J : C → Set ℂ)
    (hsource : ∀ c i, (E c i).source ⊆ U)
    (htarget : ∀ c i, (E c i).target = V c)
    (heq : ∀ c i, EqOn (E c i) f (E c i).source)
    (hdisjoint : ∀ c, Pairwise (fun i j ↦ Disjoint (E c i).source (E c j).source))
    (hmiss : ∀ c z, z ∈ U → (¬ ∃ i, z ∈ (E c i).source) →
      ∃ d, d ≠ c ∧ z ∈ S d)
    (hseam : ∀ c, MapsTo f (S c) (J c))
    (hseparate : ∀ c d, d ≠ c → Disjoint (J d) (V c))
    (hΩ : Ω = ⋃ c, V c)
    (hvalues : MapsTo f U Ω) :
    IsCoveringMapOn (fun z : U ↦ f z.val) Ω ∧
      range (fun z : U ↦ f z.val) = Ω := by
  classical
  have hcover : IsCoveringMapOn (fun z : U ↦ f z.val) Ω := by
    intro y hy
    rw [hΩ] at hy
    obtain ⟨c,hc⟩ := mem_iUnion.mp hy
    apply isEvenlyCovered_on_open_subset_of_disjoint_charts f U hU (E c) (V c)
      (hsource c) (htarget c) (heq c) (hdisjoint c) ?_ hc
    intro z hz
    by_contra hn
    have hnot : ¬ ∃ i, z ∈ (E c i).source := by
      simpa only [mem_iUnion] using hn
    obtain ⟨d,hd,hzS⟩ := hmiss c z hz.1 hnot
    exact Set.disjoint_left.mp (hseparate c d hd) (hseam d hzS) hz.2
  refine ⟨hcover, Set.Subset.antisymm ?_ ?_⟩
  · rintro y ⟨z,rfl⟩
    exact hvalues z.property
  · intro y hy
    rw [hΩ] at hy
    obtain ⟨c,hc⟩ := mem_iUnion.mp hy
    let i : I c := Classical.choice inferInstance
    have ht : y ∈ (E c i).target := (htarget c i).symm ▸ hc
    refine ⟨⟨(E c i).symm y,hsource c i ((E c i).map_target ht)⟩,?_⟩
    change f ((E c i).symm y) = y
    rw [← heq c i ((E c i).map_target ht), (E c i).right_inv ht]

end HolomorphicAnosov
