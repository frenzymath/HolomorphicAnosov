import HolomorphicAnosov.Topology.CairnsInitialTargetIntersection
import HolomorphicAnosov.Topology.CairnsPatchGluing
import HolomorphicAnosov.Topology.CairnsResidualSectorGeometry

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- Pasting the two actual initial radial patches gives a homeomorphism of
curve plus closed stars. Their source intersection is curve plus base and
their target intersection is circle plus image base. Both radial formulas
agree affinely on the base, with the reversed second parameter, and agree
with the prescribed map on the curve. Compact two-patch pasting therefore
identifies the literal initial total map with a genuine homeomorphism. -/
theorem cairns_initial_literal_homeomorph
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (hσ : Topology.IsEmbedding σ)
    (ha : ∃ x ∈ a, connectedComponentIn (range σ)ᶜ x = a)
    (hab : Bornology.IsBounded a) (h : range σ ≃ₜ Circle)
    (d : InitialData σ a p q)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h)
    (hsource : closure d.firstStar.sourceStar ∩ closure d.secondStar.sourceStar =
      segment ℝ (σ p) (σ q)) :
    ∃ H : ↥(range σ ∪ (closure d.firstStar.sourceStar ∪ closure d.secondStar.sourceStar)) ≃ₜ
      ↥(range (fun z : Circle ↦ (z : ℂ)) ∪
        (closure (d.firstStar.targetStar h) ∪ closure (d.secondStar.targetStar h))),
      (∀ x, (H x : ℂ) = (d.stage h).map x) ∧
      (∀ z ∈ range σ ∪ closure d.firstStar.sourceStar,
        (d.stage h).map z = d.firstStar.patchMap h z) ∧
      (∀ z ∈ range σ ∪ closure d.secondStar.sourceStar,
        (d.stage h).map z = d.secondStar.patchMap h z) := by
  classical
  let c := range σ
  let k := range (fun z : Circle ↦ (z : ℂ))
  let A₁ := c ∪ closure d.firstStar.sourceStar
  let A₂ := c ∪ closure d.secondStar.sourceStar
  let B₁ := k ∪ closure (d.firstStar.targetStar h)
  let B₂ := k ∪ closure (d.secondStar.targetStar h)
  let f := (d.stage h).map
  obtain ⟨H₁,he₁,hi₁,hbase₁,hrest₁⟩ := cairns_geometric_star_literal_extension d.firstStar h h₁
  obtain ⟨H₂,he₂,hi₂,hbase₂,hrest₂⟩ := cairns_geometric_star_literal_extension d.secondStar h h₂
  have heq₁ : ∀ z ∈ A₁, f z = d.firstStar.patchMap h z := by
    intro z hz
    by_cases hzc : z ∈ range σ
    · simp only [f,InitialData.stage,StarChoice.patchMap,dite_eq_left hzc]
    · have hzcl : z ∈ closure d.firstStar.sourceStar := hz.resolve_left hzc
      simp only [f,InitialData.stage,dite_eq_right hzc,ite_eq_left hzcl]
  have heq₂ : ∀ z ∈ A₂, f z = d.secondStar.patchMap h z := by
    intro z hz
    by_cases hzc : z ∈ range σ
    · simp only [f,InitialData.stage,StarChoice.patchMap,dite_eq_left hzc]
    · by_cases hzcl : z ∈ closure d.firstStar.sourceStar
      · have hz₂ : z ∈ closure d.secondStar.sourceStar := hz.resolve_left hzc
        have hzbase : z ∈ segment ℝ (σ p) (σ q) := hsource ▸ ⟨hzcl,hz₂⟩
        simpa only [f,InitialData.stage,dite_eq_right hzc,ite_eq_left hzcl] using
          cairns_initial_patch_agreement h d h₁ h₂ z (Or.inr hzbase)
      · simp only [f,InitialData.stage,dite_eq_right hzc,ite_eq_right hzcl]
  have hpatch (A B : Set ℂ) (H : A ≃ₜ B) (heq : ∀ x : A, (H x : ℂ) = f x) :
      ContinuousOn f A ∧ BijOn f A B := by
    constructor
    · apply continuousOn_iff_continuous_domRestrict.mpr
      have hh : A.domRestrict f = fun x : A ↦ (H x : ℂ) := funext (fun x ↦ (heq x).symm)
      rw [hh]
      exact continuous_subtype_val.comp H.continuous
    · refine ⟨?_,?_,?_⟩
      · intro x hx
        rw [← heq ⟨x,hx⟩]
        exact (H ⟨x,hx⟩).property
      · intro x hx y hy hh
        have he : H ⟨x,hx⟩ = H ⟨y,hy⟩ := by
          apply Subtype.ext
          rw [heq,heq,hh]
        exact congrArg Subtype.val (H.injective he)
      · intro y hy
        obtain ⟨x,hx⟩ := H.surjective ⟨y,hy⟩
        exact ⟨x,x.property,(heq x).symm.trans (congrArg Subtype.val hx)⟩
  have hp₁ := hpatch A₁ B₁ H₁ (fun x ↦ (he₁ x).trans (heq₁ x x.property).symm)
  have hp₂ := hpatch A₂ B₂ H₂ (fun x ↦ (he₂ x).trans (heq₂ x x.property).symm)
  have hcomp₁ : IsCompact A₁ := (isCompact_range hσ.continuous).union
    ((hab.subset (h₁.2.2.1.trans (cairns_star_sector_geometry hσ ha d.firstStar).2.2.2)).isCompact_closure)
  have hcomp₂ : IsCompact A₂ := (isCompact_range hσ.continuous).union
    ((hab.subset (h₂.2.2.1.trans (cairns_star_sector_geometry hσ ha d.secondStar).2.2.2)).isCompact_closure)
  have hAi : A₁ ∩ A₂ = c ∪ segment ℝ (σ p) (σ q) := by
    rw [show A₁ ∩ A₂ = c ∪ (closure d.firstStar.sourceStar ∩ closure d.secondStar.sourceStar) from
      (union_inter_distrib_left _ _ _).symm,hsource]
  have hBi : B₁ ∩ B₂ = k ∪ segment ℝ (h ⟨σ p,⟨p,rfl⟩⟩ : ℂ) (h ⟨σ q,⟨q,rfl⟩⟩ : ℂ) := by
    rw [show B₁ ∩ B₂ = k ∪ (closure (d.firstStar.targetStar h) ∩
      closure (d.secondStar.targetStar h)) from (union_inter_distrib_left _ _ _).symm,
      cairns_initial_target_closure_intersection hσ h d h₁ h₂]
  have hbaseA : segment ℝ (σ p) (σ q) ⊆ A₁ ∩ A₂ := by
    rw [hAi]
    exact subset_union_right
  have hbaseFormula (t : I) :
      f ((1-(t : ℝ)) • σ p + (t : ℝ) • σ q) =
        (1-(t : ℝ)) • (h ⟨σ p,⟨p,rfl⟩⟩ : ℂ) +
          (t : ℝ) • (h ⟨σ q,⟨q,rfl⟩⟩ : ℂ) := by
    have hzbase : (1-(t : ℝ)) • σ p + (t : ℝ) • σ q ∈ segment ℝ (σ p) (σ q) :=
      ⟨1-t,t,sub_nonneg.mpr t.property.2,t.property.1,sub_add_cancel _ _,rfl⟩
    rw [heq₁ _ (hbaseA hzbase).1]
    simpa only [d.first_eq,d.last_eq] using hbase₁ t
  have hinter : f '' (A₁ ∩ A₂) = B₁ ∩ B₂ := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨hp₁.2.mapsTo hz.1,hp₂.2.mapsTo hz.2⟩
    · rw [hBi]
      intro y hy
      rcases hy with hy | hy
      · obtain ⟨yc,rfl⟩ := hy
        let x : range σ := h.symm yc
        refine ⟨x,?_,?_⟩
        · rw [hAi]
          exact Or.inl x.property
        · simp only [f,InitialData.stage,dite_eq_left x.property]
          exact congrArg Subtype.val (h.apply_symm_apply yc)
      · rw [segment_eq_image] at hy
        obtain ⟨t,ht,rfl⟩ := hy
        refine ⟨(1-t) • σ p + t • σ q,
          hbaseA ⟨1-t,t,sub_nonneg.mpr ht.2,ht.1,sub_add_cancel _ _,rfl⟩,
          hbaseFormula ⟨t,ht⟩⟩
  obtain ⟨H,hH⟩ := compact_two_patch_homeomorph A₁ A₂ B₁ B₂ f
    hcomp₁ hcomp₂ hp₁.1 hp₂.1 hp₁.2 hp₂.2 hinter
  have hAs : A₁ ∪ A₂ = c ∪ (closure d.firstStar.sourceStar ∪ closure d.secondStar.sourceStar) := by
    ext z; simp only [A₁,A₂,mem_union]; tauto
  have hBs : B₁ ∪ B₂ = k ∪ (closure (d.firstStar.targetStar h) ∪ closure (d.secondStar.targetStar h)) := by
    ext z; simp only [B₁,B₂,mem_union]; tauto
  refine ⟨((Homeomorph.setCongr hAs).symm.trans H).trans (Homeomorph.setCongr hBs),?_,heq₁,heq₂⟩
  intro x
  exact hH ⟨x,hAs.symm ▸ x.property⟩

end HolomorphicAnosov.Topology.Plane
