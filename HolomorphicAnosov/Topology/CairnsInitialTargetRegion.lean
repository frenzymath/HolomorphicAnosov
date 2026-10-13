import HolomorphicAnosov.Topology.CairnsInitialLiteralHomeomorph
import HolomorphicAnosov.Topology.CairnsInitialRegionCell

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- The actual image of the initial region is the two literal target stars
plus their common open base. The pasted map agrees with each star extension
and maps the base affinely. Its openness follows from the independently proved
planar open-image theorem, and its closure is the union of the two closed
target stars. These facts normalize the initial carrier homeomorphism to the
precise stage interface of Cairns §4(B). -/
theorem cairns_initial_target_region
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (hab : Bornology.IsBounded a) (h : range σ ≃ₜ Circle) (d : InitialData σ a p q)
    (hchord : openSegment ℝ (σ p) (σ q) ⊆ a)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h)
    (hop₁ : IsOpen d.firstStar.sector) (hop₂ : IsOpen d.secondStar.sector)
    (hdisj : Disjoint d.firstStar.sector d.secondStar.sector) :
    let A := (d.stage h).region
    let K := (d.stage h).target
    let P : ℂ := h ⟨σ p,⟨p,rfl⟩⟩
    let Q : ℂ := h ⟨σ q,⟨q,rfl⟩⟩
    K.Nonempty ∧ IsOpen K ∧ K ⊆ Metric.ball (0 : ℂ) 1 ∧
      K = d.firstStar.targetStar h ∪ d.secondStar.targetStar h ∪ openSegment ℝ P Q ∧
      closure K = closure (d.firstStar.targetStar h) ∪ closure (d.secondStar.targetStar h) ∧
      ∃ H : ↥(closure A ∪ range σ) ≃ₜ
          ↥(closure K ∪ range (fun z : Circle ↦ (z : ℂ))),
        ∀ x, (H x : ℂ) = (d.stage h).map x := by
  intro A K P Q
  obtain ⟨hAne,hAopen,hAa,hAdisk,hAfrontCircle,hAfront,hAcl,hsource⟩ :=
    cairns_initial_region_cell hσ ha h d hchord h₁ h₂ hop₁ hop₂ hdisj
  obtain ⟨H,hH,hmap₁,hmap₂⟩ := cairns_initial_literal_homeomorph hσ ha hab h d h₁ h₂ hsource
  obtain ⟨H₁,he₁,hi₁,hbase₁,hne₁,hopen₁,hball₁,hfront₁,hcov₁⟩ :=
    cairns_geometric_star_literal_extension d.firstStar h h₁
  obtain ⟨H₂,he₂,hi₂,hbase₂,hne₂,hopen₂,hball₂,hfront₂,hcov₂⟩ :=
    cairns_geometric_star_literal_extension d.secondStar h h₂
  let f := (d.stage h).map
  have himageStar {g : CairnsCircleGap} (b : StarChoice σ a g)
      (H' : ↥(range σ ∪ closure b.sourceStar) ≃ₜ
        ↥(range (fun z : Circle ↦ (z : ℂ)) ∪ closure (b.targetStar h)))
      (he : ∀ x, (H' x : ℂ) = b.patchMap h x)
      (hi : ∀ x : ↥(range σ ∪ closure b.sourceStar),
        (x : ℂ) ∈ b.sourceStar ↔ (H' x : ℂ) ∈ b.targetStar h)
      (hf : ∀ z ∈ range σ ∪ closure b.sourceStar, f z = b.patchMap h z) :
      f '' b.sourceStar = b.targetStar h := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      have hxdom : x ∈ range σ ∪ closure b.sourceStar := Or.inr (subset_closure hx)
      rw [hf x hxdom,← he ⟨x,hxdom⟩]
      exact (hi ⟨x,hxdom⟩).mp hx
    · intro y hy
      obtain ⟨x,hx⟩ := H'.surjective ⟨y,Or.inr (subset_closure hy)⟩
      have hxstar : (x : ℂ) ∈ b.sourceStar := (hi x).mpr (by rw [hx];exact hy)
      refine ⟨x,hxstar,?_⟩
      rw [hf x x.property,← he x]
      exact congrArg Subtype.val hx
  have him₁ := himageStar d.firstStar H₁ he₁ hi₁ hmap₁
  have him₂ := himageStar d.secondStar H₂ he₂ hi₂ hmap₂
  have hbaseFormula (t : I) : f ((1-(t : ℝ)) • σ p + (t : ℝ) • σ q) =
      (1-(t : ℝ)) • P + (t : ℝ) • Q := by
    have hx : (1-(t : ℝ)) • σ p + (t : ℝ) • σ q ∈ segment ℝ (σ p) (σ q) :=
      ⟨1-t,t,sub_nonneg.mpr t.property.2,t.property.1,sub_add_cancel _ _,rfl⟩
    have hxcl : (1-(t : ℝ)) • σ p + (t : ℝ) • σ q ∈ closure d.firstStar.sourceStar := by
      have hh : _ ∈ closure d.firstStar.sourceStar ∩ closure d.secondStar.sourceStar := hsource.symm ▸ hx
      exact hh.1
    change (d.stage h).map _ = _
    rw [hmap₁ _ (Or.inr hxcl)]
    simpa only [d.first_eq,d.last_eq] using hbase₁ t
  have himBase : f '' openSegment ℝ (σ p) (σ q) = openSegment ℝ P Q := by
    rw [openSegment_eq_image,openSegment_eq_image]
    ext z
    constructor
    · rintro ⟨x,⟨t,ht,rfl⟩,rfl⟩
      exact ⟨t,ht,(hbaseFormula ⟨t,ht.1.le,ht.2.le⟩).symm⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨_,⟨t,ht,rfl⟩,hbaseFormula ⟨t,ht.1.le,ht.2.le⟩⟩
  have hK : K = d.firstStar.targetStar h ∪ d.secondStar.targetStar h ∪ openSegment ℝ P Q := by
    change f '' (d.firstStar.sourceStar ∪ d.secondStar.sourceStar ∪ openSegment ℝ (σ p) (σ q)) = _
    rw [image_union,image_union,him₁,him₂,himBase]
  let C := range σ ∪ (closure d.firstStar.sourceStar ∪ closure d.secondStar.sourceStar)
  have hAC : A ⊆ C := by
    intro x hx
    exact Or.inr (hAcl ▸ subset_closure hx)
  have hKimage : K = (fun x : C ↦ (H x : ℂ)) '' (Subtype.val ⁻¹' A) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hAC hx⟩,hx,hH _⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,(hH x).symm⟩
  have hKopen : IsOpen K := hKimage.symm ▸ carrier_homeomorph_open_image _ _ A H hAopen hAC
  have hpq : P ≠ Q := by
    intro he
    have hpqe : p = q := hσ.injective (congrArg Subtype.val (h.injective (Subtype.ext he)))
    have hh := (CairnsCircleGap.parameter_embedding_range d.firstGap).1.injective
      (show d.firstGap.parameter 0 = d.firstGap.parameter 1 from by
        rw [(CairnsCircleGap.parameter_embedding_range d.firstGap).2.2.1,
          (CairnsCircleGap.parameter_embedding_range d.firstGap).2.2.2,d.first_eq,d.last_eq,hpqe])
    exact zero_ne_one hh
  have hPball : P ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact (Circle.norm_coe _).le
  have hQball : Q ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact (Circle.norm_coe _).le
  have hKball : K ⊆ Metric.ball (0 : ℂ) 1 := by
    rw [hK]
    exact union_subset (union_subset hball₁ hball₂) (openSegment_subset_ball_of_ne hPball hQball hpq)
  have hbasecl : segment ℝ P Q ⊆ closure (d.firstStar.targetStar h) := by
    intro x hx
    apply frontier_subset_closure
    rw [hfront₁]
    left
    simpa only [d.first_eq,d.last_eq] using hx
  have hKcl : closure K = closure (d.firstStar.targetStar h) ∪ closure (d.secondStar.targetStar h) := by
    rw [hK]
    apply Subset.antisymm
    · apply closure_minimal _ (isClosed_closure.union isClosed_closure)
      rintro x ((hx | hx) | hx)
      · exact Or.inl (subset_closure hx)
      · exact Or.inr (subset_closure hx)
      · exact Or.inl (hbasecl (openSegment_subset_segment ℝ _ _ hx))
    · exact union_subset (closure_mono (fun x hx ↦ Or.inl (Or.inl hx)))
        (closure_mono (fun x hx ↦ Or.inl (Or.inr hx)))
  have hsrc : closure A ∪ range σ = C := by rw [hAcl];exact union_comm _ _
  have htgt : closure K ∪ range (fun z : Circle ↦ (z : ℂ)) =
      range (fun z : Circle ↦ (z : ℂ)) ∪
        (closure (d.firstStar.targetStar h) ∪ closure (d.secondStar.targetStar h)) := by
    rw [hKcl];exact union_comm _ _
  refine ⟨hAne.image _,hKopen,hKball,hK,hKcl,
    ((Homeomorph.setCongr hsrc).trans H).trans (Homeomorph.setCongr htgt).symm,?_⟩
  intro x
  exact hH ⟨x,hsrc.subset x.property⟩

end HolomorphicAnosov.Topology.Plane
