import HolomorphicAnosov.Topology.PlanarSupportingFaceSegmentG2
import HolomorphicAnosov.Topology.TriangleVisibleSupportingFunctionalG2
import HolomorphicAnosov.Topology.ConvexTriangleBaseVisible

open Set
namespace HolomorphicAnosov

/-- Every noncontact visible hull point lies strictly between two contact points
on one entirely visible straight face. Source: Cairns (1951), §3(D,E), p.863;
Rockafellar (1970), §18, pp.163–165. A supporting functional strictly separates
the apex from the point. Its whole face is therefore visible. The compact planar
face is a segment with extreme endpoints, which belong to the hull generator.
Any endpoint in the adjoined base must be a base endpoint by visibility, hence
is again a contact. The given point is not a contact and is therefore strictly
between the endpoints. -/
theorem triangle_visible_contact_face_g2
    (C : Set ℂ) (M A B : ℂ)
    (hA : A ∈ C) (hB : B ∈ C)
    (hcompact : IsCompact (convexHull ℝ (C ∪ segment ℝ A B)))
    (hint : (interior (convexHull ℝ (C ∪ segment ℝ A B))).Nonempty)
    (hsub : convexHull ℝ (C ∪ segment ℝ A B) ⊆ convexHull ℝ {M,A,B})
    (hM : M ∉ convexHull ℝ (C ∪ segment ℝ A B))
    (hvA : IsVisible ℝ (convexHull ℝ (C ∪ segment ℝ A B)) M A)
    (hvB : IsVisible ℝ (convexHull ℝ (C ∪ segment ℝ A B)) M B)
    {q : ℂ} (hq : q ∈ convexHull ℝ (C ∪ segment ℝ A B))
    (hvq : IsVisible ℝ (convexHull ℝ (C ∪ segment ℝ A B)) M q)
    (hqC : q ∉ C) :
    ∃ U V : ℂ, U ∈ C ∧ V ∈ C ∧ q ∈ openSegment ℝ U V ∧
      segment ℝ U V ⊆ {z | z ∈ convexHull ℝ (C ∪ segment ℝ A B) ∧
        IsVisible ℝ (convexHull ℝ (C ∪ segment ℝ A B)) M z} := by
  let K := convexHull ℝ (C ∪ segment ℝ A B)
  have hconv : Convex ℝ K := convex_convexHull ℝ _
  have hAK : A ∈ K := subset_convexHull ℝ _ (Or.inl hA)
  have hBK : B ∈ K := subset_convexHull ℝ _ (Or.inl hB)
  have hqbase : q ∉ segment ℝ A B := by
    intro hb
    rcases convex_triangle_visible_base_endpoint hconv hint hsub hAK hBK hM hb hvq with rfl | rfl
    · exact hqC hA
    · exact hqC hB
  have hqint : q ∉ interior K := fun hi ↦ hM ((hvq.eq_of_mem_interior hi).symm ▸ hq)
  obtain ⟨f,hbound,hstrict⟩ := convex_triangle_visible_supporting_functional_g2
    hconv hint hsub hAK hBK hM hvA hvB hq hqint hqbase
  have hf : f ≠ 0 := by intro he; simp [he] at hstrict
  obtain ⟨U,V,hU,hV,hface⟩ := planar_supporting_face_segment_g2 K hcompact hconv f hf (f q)
    hbound ⟨q,hq,rfl⟩
  have hvisible : ∀ z ∈ {z ∈ K | f z=f q}, IsVisible ℝ K M z := by
    intro z hz
    have hMz : M ≠ z := (ne_of_mem_of_not_mem hz.1 hM).symm
    apply (isVisible_iff_lineMap hMz).mpr
    intro t ht htk
    have hle := hbound _ htk
    simp only [AffineMap.lineMap_apply_module,map_add,map_smul,smul_eq_mul,hz.2] at hle
    have hp := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hstrict)
    nlinarith
  have hcontact : ∀ z ∈ K.extremePoints ℝ, z ∈ {z ∈ K | f z=f q} → z ∈ C := by
    intro z hz hzf
    rcases extremePoints_convexHull_subset hz with hC | hb
    · exact hC
    · rcases convex_triangle_visible_base_endpoint hconv hint hsub hAK hBK hM hb
        (hvisible z hzf) with rfl | rfl
      · exact hA
      · exact hB
  have hUf : U ∈ {z ∈ K | f z=f q} := hface.symm ▸ left_mem_segment ℝ U V
  have hVf : V ∈ {z ∈ K | f z=f q} := hface.symm ▸ right_mem_segment ℝ U V
  have hUC := hcontact U hU hUf
  have hVC := hcontact V hV hVf
  refine ⟨U,V,hUC,hVC,?_,?_⟩
  · apply mem_openSegment_of_ne_left_right
      (show U ≠ q from fun he ↦ hqC (he ▸ hUC))
      (show V ≠ q from fun he ↦ hqC (he ▸ hVC))
    exact hface ▸ (show q ∈ {z ∈ K | f z=f q} from ⟨hq,rfl⟩)
  · intro z hz
    have hzf : z ∈ {z ∈ K | f z=f q} := hface.symm ▸ hz
    exact ⟨hzf.1,hvisible z hzf⟩

end HolomorphicAnosov
