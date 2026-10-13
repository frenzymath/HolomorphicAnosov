import HolomorphicAnosov.Topology.CairnsClosedCellsCompact
import HolomorphicAnosov.Topology.CairnsCellHalfDiskExtension
import HolomorphicAnosov.Topology.CairnsHalfDiskImages

open Set Metric

namespace HolomorphicAnosov.Topology

/--
The core chart in Cairns's relative gluing argument.

Source statement: Cairns (1951), §4(D), equation (4.5), pp.865–866 states the
amalgamation corollary for two genuine Jordan boundaries and their disk cells.
The following half-disk proof expands that corollary; Cairns does not print
this construction, so its detailed argument is agent-written.

Proof. Restrict each supplied cell chart to its boundary. Boundary containment
and the sphere image equality identify each entire cᵢ homeomorphically with
the unit circle. The ball and sphere partition the closed disk, so Uᵢ and cᵢ
partition closure Uᵢ. Pull the proper embedded common arc B to each circle.
The closure of its complementary circle arc is an embedded interval with the
same endpoints p,q: remove a point off B, use an angular interval coordinate,
and use monotonicity of a continuous injective interval map for the given arc;
the complementary angular interval gives the other arc.

Parametrize B by the supplied b and map b(t) to the diameter point 2t−1.
Parametrize each complementary boundary arc, with endpoints p,q in this order,
onto the upper or lower unit semicircle. Closed-set pasting on the two boundary
arcs gives a continuous bijection cᵢ to the boundary of the corresponding
closed half-disk. The source is compact and the target Hausdorff, hence this
is a homeomorphism. Each closed half-disk has a radial homeomorphism to the
closed unit disk from any of its interior points; along each ray, divide the
radius by its unique boundary intersection distance. Convexity and nonempty
interior give positive continuous radial distance, including the two corners.
This homeomorphism carries its boundary to the sphere and its interior to the
open disk. Compose the prescribed boundary map with it and apply hextᵢ.
Undo the radial chart to obtain a homeomorphism from closure Uᵢ onto its
closed half-disk. Its boundary values are exactly the prescribed map. Those
boundary values are onto the target boundary, so bijectivity and the partitions
already established force Uᵢ to map exactly onto the open half-disk interior.

The two maps agree pointwise on B because both restrict to b(t)↦2t−1. Paste
them over the two closed subsets of their union. Equal images from opposite
half-disks lie on the diameter; the seam-preimage and agreement lemmas then
prove injectivity. Surjectivity follows by choosing the upper or lower chart
according to the imaginary-part sign. The union is compact and the disk is
Hausdorff, so this continuous bijection is a homeomorphism.
The two open half-disk interiors together with the open diameter are exactly
the open disk. The two outer semicircles are exactly the unit sphere. These
give the asserted R and C image identities. Distinct endpoints and properness
exclude degenerate diameter and whole-boundary cases. No ambient openness or
unproved planar separation result enters this relative chart construction.

The containment guards are essential: without them one could add an isolated
point of U₂ to c₁, making hext₁ vacuous while forcing R and C to overlap.
The parent supplies both guards from its closure decompositions, then obtains
ambient openness and the circle parametrization from the independent disk chart.
DAG node: topo.cairns_disk_cell_relative_chart_g20.
-/
theorem cairns_disk_cell_relative_chart
    (U₁ U₂ c₁ c₂ B : Set ℂ) (p q : ℂ)
    (hc₁ : c₁ ⊆ closure U₁) (hc₂ : c₂ ⊆ closure U₂)
    (hcell₁ : ∃ H : closure U₁ ≃ₜ closedBall (0 : ℂ) 1,
      H '' {z | (z : ℂ) ∈ U₁} = {w | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
      H '' {z | (z : ℂ) ∈ c₁} = {w | (w : ℂ) ∈ sphere (0 : ℂ) 1})
    (hcell₂ : ∃ H : closure U₂ ≃ₜ closedBall (0 : ℂ) 1,
      H '' {z | (z : ℂ) ∈ U₂} = {w | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
      H '' {z | (z : ℂ) ∈ c₂} = {w | (w : ℂ) ∈ sphere (0 : ℂ) 1})
    (hext₁ : ∀ h : c₁ ≃ₜ sphere (0 : ℂ) 1,
      ∃ H : closure U₁ ≃ₜ closedBall (0 : ℂ) 1,
        ∀ z : closure U₁, ∀ hz : (z : ℂ) ∈ c₁,
          (H z : ℂ) = (h ⟨(z : ℂ), hz⟩ : ℂ))
    (hext₂ : ∀ h : c₂ ≃ₜ sphere (0 : ℂ) 1,
      ∃ H : closure U₂ ≃ₜ closedBall (0 : ℂ) 1,
        ∀ z : closure U₂, ∀ hz : (z : ℂ) ∈ c₂,
          (H z : ℂ) = (h ⟨(z : ℂ), hz⟩ : ℂ))
    (hpq : p ≠ q)
    (harc : ∃ b : unitInterval → ℂ,
      Topology.IsEmbedding b ∧ range b = B ∧ b 0 = p ∧ b 1 = q)
    (hproper₁ : B ⊆ c₁ ∧ B ≠ c₁)
    (hproper₂ : B ⊆ c₂ ∧ B ≠ c₂)
    (_hboundaryIntersection : c₁ ∩ c₂ = B)
    (hcellIntersection : closure U₁ ∩ closure U₂ = B)
    (_hKclosed : IsClosed (closure U₁ ∪ closure U₂)) :
    let R : Set ℂ := U₁ ∪ U₂ ∪ (B \ {p, q})
    let C : Set ℂ := (c₁ ∪ c₂) \ (B \ {p, q})
    ∃ H₀ : ↥(closure U₁ ∪ closure U₂) ≃ₜ closedBall (0 : ℂ) 1,
      H₀ '' {z | (z : ℂ) ∈ R} =
        {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
      H₀ '' {z | (z : ℂ) ∈ C} =
        {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1} := by
  have hcellData (U c : Set ℂ) (hc : c ⊆ closure U)
      (hcell : ∃ H : closure U ≃ₜ closedBall (0 : ℂ) 1,
        H '' {z | (z : ℂ) ∈ U} = {w | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
        H '' {z | (z : ℂ) ∈ c} = {w | (w : ℂ) ∈ sphere (0 : ℂ) 1}) :
      Nonempty (c ≃ₜ sphere (0 : ℂ) 1) ∧ closure U = U ∪ c ∧ Disjoint U c := by
    obtain ⟨H, hU, hC⟩ := hcell
    have hUi (z : closure U) : (z : ℂ) ∈ U ↔ (H z : ℂ) ∈ ball (0 : ℂ) 1 := by
      have him : (fun w : closure U ↦ (H w : ℂ)) '' {w | (w : ℂ) ∈ U} =
          ball (0 : ℂ) 1 := by
        ext x
        simpa only [image_image, mem_ofPred_eq] using Set.ext_iff.mp hU x
      rw [← him]
      exact ⟨fun hz ↦ ⟨z, hz, rfl⟩,
        fun ⟨w, hw, he⟩ ↦ H.injective (Subtype.ext he) ▸ hw⟩
    have hCi (z : closure U) : (z : ℂ) ∈ c ↔ (H z : ℂ) ∈ sphere (0 : ℂ) 1 := by
      have him : (fun w : closure U ↦ (H w : ℂ)) '' {w | (w : ℂ) ∈ c} =
          sphere (0 : ℂ) 1 := by
        ext x
        simpa only [image_image, mem_ofPred_eq] using Set.ext_iff.mp hC x
      rw [← him]
      exact ⟨fun hz ↦ ⟨z, hz, rfl⟩,
        fun ⟨w, hw, he⟩ ↦ H.injective (Subtype.ext he) ▸ hw⟩
    let toSphere (z : c) : sphere (0 : ℂ) 1 :=
      ⟨H ⟨z, hc z.property⟩, (hCi _).mp z.property⟩
    let fromSphere (w : sphere (0 : ℂ) 1) : c :=
      ⟨H.symm ⟨w, sphere_subset_closedBall w.property⟩,
        (hCi _).mpr (by simpa only [H.apply_symm_apply] using w.property)⟩
    let e : c ≃ₜ sphere (0 : ℂ) 1 :=
      { toFun := toSphere
        invFun := fromSphere
        left_inv := by
          intro z
          apply Subtype.ext
          change (H.symm (H ⟨z, hc z.property⟩) : ℂ) = z
          simp
        right_inv := by
          intro w
          apply Subtype.ext
          change (H (H.symm ⟨w, sphere_subset_closedBall w.property⟩) : ℂ) = w
          simp
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact (H.continuous.comp
            (continuous_subtype_val.subtype_mk (fun z ↦ hc z.property))).subtype_val
        continuous_invFun := by
          apply Continuous.subtype_mk
          exact (H.symm.continuous.comp
            (continuous_subtype_val.subtype_mk
              (fun w : sphere (0 : ℂ) 1 ↦ sphere_subset_closedBall w.property))).subtype_val }
    refine ⟨⟨e⟩, ?_, ?_⟩
    · apply Subset.antisymm
      · intro z hz
        rcases lt_or_eq_of_le (mem_closedBall.mp (H ⟨z, hz⟩).property) with hlt | heq
        · exact Or.inl ((hUi ⟨z, hz⟩).mpr hlt)
        · exact Or.inr ((hCi ⟨z, hz⟩).mpr heq)
      · exact union_subset subset_closure hc
    · rw [Set.disjoint_left]
      intro z hzU hzc
      have hlt := (hUi ⟨z, subset_closure hzU⟩).mp hzU
      have heq := (hCi ⟨z, subset_closure hzU⟩).mp hzc
      exact (ne_of_lt hlt) heq
  obtain ⟨⟨e₁⟩, hclosure₁, hdisjoint₁⟩ := hcellData U₁ c₁ hc₁ hcell₁
  obtain ⟨⟨e₂⟩, hclosure₂, hdisjoint₂⟩ := hcellData U₂ c₂ hc₂ hcell₂
  have hcross₁ : Disjoint U₁ c₂ := by
    rw [Set.disjoint_left]
    intro z hzU hzc
    have hzB : z ∈ B := by
      rw [← hcellIntersection]
      exact ⟨subset_closure hzU, hc₂ hzc⟩
    exact Set.disjoint_left.mp hdisjoint₁ hzU (hproper₁.1 hzB)
  have hcross₂ : Disjoint U₂ c₁ := by
    rw [Set.disjoint_left]
    intro z hzU hzc
    have hzB : z ∈ B := by
      rw [← hcellIntersection]
      exact ⟨hc₁ hzc, subset_closure hzU⟩
    exact Set.disjoint_left.mp hdisjoint₂ hzU (hproper₂.1 hzB)
  have hseam : Disjoint (U₁ ∪ U₂) (c₁ ∪ c₂) :=
    (hdisjoint₁.union_right hcross₁).union_left (hcross₂.union_right hdisjoint₂)
  have hpartition : (closure U₁ ∪ closure U₂) =
      (U₁ ∪ U₂ ∪ (B \ {p, q})) ∪ ((c₁ ∪ c₂) \ (B \ {p, q})) := by
    rw [hclosure₁, hclosure₂]
    ext z
    have hb : z ∈ B → z ∈ c₁ ∧ z ∈ c₂ := fun hz ↦ ⟨hproper₁.1 hz, hproper₂.1 hz⟩
    simp only [mem_union, mem_sdiff]
    tauto
  have hpartitionDisjoint : Disjoint (U₁ ∪ U₂ ∪ (B \ {p, q}))
      ((c₁ ∪ c₂) \ (B \ {p, q})) := by
    apply Disjoint.union_left
    · exact hseam.mono_right sdiff_subset
    · exact disjoint_sdiff_right
  obtain ⟨b, hb, hrange, h0, h1⟩ := harc
  obtain ⟨Hupper, hUupper, hCupper, hBupper⟩ :=
    cairns_cell_halfdisk_extension true U₁ c₁ B p q hc₁ hcell₁ hext₁ hpq
      b hb hrange h0 h1 hproper₁
  obtain ⟨Hlower, hUlower, hClower, hBlower⟩ :=
    cairns_cell_halfdisk_extension false U₂ c₂ B p q hc₂ hcell₂ hext₂ hpq
      b hb hrange h0 h1 hproper₂
  have hpreUpper := cairns_halfdisk_seam_preimage U₁ B Hupper (hproper₁.1.trans hc₁) b hrange hBupper
  have hpreLower := cairns_halfdisk_seam_preimage U₂ B Hlower (hproper₂.1.trans hc₂) b hrange hBlower
  have hagree := cairns_halfdisk_agree_on_seam U₁ U₂ B Hupper Hlower
    (hproper₁.1.trans hc₁) (hproper₂.1.trans hc₂) b hrange hBupper hBlower
  have hcrossChart := cairns_halfdisk_cross_injective U₁ U₂ B Hupper Hlower
    (hproper₁.1.trans hc₁) (hproper₂.1.trans hc₂) hpreUpper hpreLower hagree
  classical
  let K := closure U₁ ∪ closure U₂
  let f : ℂ → ℂ := fun z ↦ if h : z ∈ closure U₁ then Hupper ⟨z, h⟩
    else if h : z ∈ closure U₂ then Hlower ⟨z, h⟩ else 0
  have hf₁ (z : closure U₁) : f z = (Hupper z : ℂ) := by simp [f, z.property]
  have hf₂ (z : closure U₂) : f z = (Hlower z : ℂ) := by
    by_cases hz : (z : ℂ) ∈ closure U₁
    · have hzB : (z : ℂ) ∈ B := hcellIntersection ▸ ⟨hz, z.property⟩
      simpa [f, hz] using hagree ⟨z, hzB⟩
    · simp [f, hz, z.property]
  have hfcont₁ : ContinuousOn f (closure U₁) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert Hupper.continuous.subtype_val using 1
    exact funext hf₁
  have hfcont₂ : ContinuousOn f (closure U₂) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert Hlower.continuous.subtype_val using 1
    exact funext hf₂
  have hfcont : ContinuousOn f K :=
    hfcont₁.union_of_isClosed hfcont₂ isClosed_closure isClosed_closure
  have hfmem (z : K) : f z ∈ closedBall (0 : ℂ) 1 := by
    rcases z.property with hz | hz
    · rw [hf₁ ⟨z, hz⟩]
      exact (Hupper ⟨z, hz⟩).property.1
    · rw [hf₂ ⟨z, hz⟩]
      exact (Hlower ⟨z, hz⟩).property.1
  let F : K → closedBall (0 : ℂ) 1 := fun z ↦ ⟨f z, hfmem z⟩
  have hFcont : Continuous F := hfcont.domRestrict.subtype_mk _
  have hFinj : Function.Injective F := by
    intro x y hxy
    have heq : f x = f y := congrArg Subtype.val hxy
    apply Subtype.ext
    rcases x.property with hx | hx <;> rcases y.property with hy | hy
    · rw [hf₁ ⟨x, hx⟩, hf₁ ⟨y, hy⟩] at heq
      exact congrArg (fun z : closure U₁ ↦ (z : ℂ)) (Hupper.injective (Subtype.ext heq))
    · rw [hf₁ ⟨x, hx⟩, hf₂ ⟨y, hy⟩] at heq
      exact hcrossChart ⟨x, hx⟩ ⟨y, hy⟩ heq
    · rw [hf₂ ⟨x, hx⟩, hf₁ ⟨y, hy⟩] at heq
      exact (hcrossChart ⟨y, hy⟩ ⟨x, hx⟩ heq.symm).symm
    · rw [hf₂ ⟨x, hx⟩, hf₂ ⟨y, hy⟩] at heq
      exact congrArg (fun z : closure U₂ ↦ (z : ℂ)) (Hlower.injective (Subtype.ext heq))
  have hFsurj : Function.Surjective F := by
    intro w
    by_cases hw : 0 ≤ (w : ℂ).im
    · let wu : cairnsClosedHalfDisk true := ⟨w, by
        exact ⟨w.property, hw⟩⟩
      let z := Hupper.symm wu
      refine ⟨⟨z, Or.inl z.property⟩, ?_⟩
      apply Subtype.ext
      change f z = w
      rw [hf₁ z]
      exact congrArg Subtype.val (Hupper.apply_symm_apply wu)
    · let wl : cairnsClosedHalfDisk false := ⟨w, by
        exact ⟨w.property, le_of_not_ge hw⟩⟩
      let z := Hlower.symm wl
      refine ⟨⟨z, Or.inr z.property⟩, ?_⟩
      apply Subtype.ext
      change f z = w
      rw [hf₂ z]
      exact congrArg Subtype.val (Hlower.apply_symm_apply wl)
  have hKcompact : IsCompact K :=
    (cairns_closed_cells_compact_closed _ _ hcell₁.choose hcell₂.choose).1
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  have hFhome : IsHomeomorph F := isHomeomorph_iff_continuous_bijective.mpr
    ⟨hFcont, hFinj, hFsurj⟩
  let H₀ : K ≃ₜ closedBall (0 : ℂ) 1 := hFhome.homeomorph F
  have hball₁ := cairns_halfdisk_ball_preimage true U₁ c₁ B p q Hupper
    (hproper₁.1.trans hc₁) hclosure₁ hUupper hCupper b hrange h0 h1 hBupper
  have hball₂ := cairns_halfdisk_ball_preimage false U₂ c₂ B p q Hlower
    (hproper₂.1.trans hc₂) hclosure₂ hUlower hClower b hrange h0 h1 hBlower
  have hR (z : K) : (H₀ z : ℂ) ∈ ball (0 : ℂ) 1 ↔
      (z : ℂ) ∈ U₁ ∪ U₂ ∪ (B \ {p, q}) := by
    change f z ∈ ball (0 : ℂ) 1 ↔ _
    constructor
    · intro hz
      rcases z.property with hz₁ | hz₂
      · rw [hf₁ ⟨z, hz₁⟩] at hz
        rcases (hball₁ ⟨z, hz₁⟩).mp hz with hU | hB
        · exact Or.inl (Or.inl hU)
        · exact Or.inr hB
      · rw [hf₂ ⟨z, hz₂⟩] at hz
        rcases (hball₂ ⟨z, hz₂⟩).mp hz with hU | hB
        · exact Or.inl (Or.inr hU)
        · exact Or.inr hB
    · rintro ((hz₁ | hz₂) | hzB)
      · rw [hf₁ ⟨z, subset_closure hz₁⟩]
        exact (hball₁ _).mpr (Or.inl hz₁)
      · rw [hf₂ ⟨z, subset_closure hz₂⟩]
        exact (hball₂ _).mpr (Or.inl hz₂)
      · rw [hf₁ ⟨z, hc₁ (hproper₁.1 hzB.1)⟩]
        exact (hball₁ _).mpr (Or.inr hzB)
  have hC (z : K) : (H₀ z : ℂ) ∈ sphere (0 : ℂ) 1 ↔
      (z : ℂ) ∈ (c₁ ∪ c₂) \ (B \ {p, q}) := by
    constructor
    · intro hzs
      have hzK : (z : ℂ) ∈
          (U₁ ∪ U₂ ∪ (B \ {p, q})) ∪ ((c₁ ∪ c₂) \ (B \ {p, q})) := by
        rw [← hpartition]
        exact z.property
      rcases hzK with hzR | hzC
      · exact ((ne_of_lt ((hR z).mpr hzR)) hzs).elim
      · exact hzC
    · intro hzC
      have hn : ¬ (H₀ z : ℂ) ∈ ball (0 : ℂ) 1 := by
        intro hzball
        exact Set.disjoint_left.mp hpartitionDisjoint ((hR z).mp hzball) hzC
      exact le_antisymm (H₀ z).property (le_of_not_gt hn)
  refine ⟨H₀, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hR z).mpr hz
    · intro hw
      refine ⟨H₀.symm w, (hR _).mp ?_, H₀.apply_symm_apply w⟩
      simpa only [H₀.apply_symm_apply, Set.mem_ofPred_eq] using hw
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hC z).mpr hz
    · intro hw
      refine ⟨H₀.symm w, (hC _).mp ?_, H₀.apply_symm_apply w⟩
      simpa only [H₀.apply_symm_apply, Set.mem_ofPred_eq] using hw

end HolomorphicAnosov.Topology

