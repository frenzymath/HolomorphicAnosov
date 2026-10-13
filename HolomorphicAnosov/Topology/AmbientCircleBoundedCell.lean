import HolomorphicAnosov.Topology.AmbientCircleRegions

noncomputable section
open Set Metric
namespace HolomorphicAnosov

/-- For an ambient image c of the unit circle and a bounded complementary component U, the boundary c lies in closure U. The closure admits a closed-disk homeomorphism carrying U to the open disk and c to the unit circle, and every prescribed boundary homeomorphism extends to such a closed-disk homeomorphism.

Source: Cairns (1951), preliminary 2(A), p.860; existing ambient-circle region and prescribed boundary extension theorem.

Proof: Apply ambient_circle_regions to obtain the two component sets Q and E and prescribed boundary extensions on Q. Since U is a component through a point outside c, it is either Q or E; boundedness rules out E. Thus U=Q and closure U=U∪c, with U and c disjoint. Restrict the given ambient homeomorphism to c and use this boundary correspondence in the extension theorem to obtain H. Its restriction sends c onto the entire unit circle because that correspondence is surjective. In the closed-disk subtype the complement of the sphere is the open disk. In closure U the complement of c is U. Bijectivity of H therefore gives the required open-disk image equality. The original prescribed-boundary assertion supplies every other boundary correspondence. -/
theorem ambientCircle_bounded_cell (c U : Set ℂ) (F : ℂ ≃ₜ ℂ)
    (hF : F '' c = sphere (0 : ℂ) 1) (u : ℂ) (hu : u ∉ c)
    (hU : U = connectedComponentIn cᶜ u) (hb : Bornology.IsBounded U) :
    c ⊆ closure U ∧
    (∃ H : closure U ≃ₜ closedBall (0 : ℂ) 1,
      H '' {z | (z : ℂ) ∈ U} = {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
      H '' {z | (z : ℂ) ∈ c} = {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1}) ∧
    (∀ h : c ≃ₜ sphere (0 : ℂ) 1,
      ∃ H : closure U ≃ₜ closedBall (0 : ℂ) 1,
        ∀ z : closure U, ∀ hz : (z : ℂ) ∈ c,
          (H z : ℂ) = (h ⟨(z : ℂ), hz⟩ : ℂ)) := by
  obtain ⟨Q, E, hQne, hEne, hne, hcover, hdisj, hcomp,
    hQconn, hEconn, hQo, hEo, hQb, hEb, hQf, hEf, hQcl, hext⟩ :=
    ambient_circle_regions c F hF
  have hmem : U ∈ ({Q, E} : Set (Set ℂ)) := by
    rw [← hcomp]
    exact ⟨u, hu, hU.symm⟩
  have hUQ : U = Q := by
    rcases Set.mem_insert_iff.mp hmem with h | h
    · exact h
    · exact False.elim (hEb (Set.mem_singleton_iff.mp h ▸ hb))
  subst Q
  have hcU : c ⊆ closure U := by rw [hQcl]; exact subset_union_right
  have hdis : Disjoint U c := by
    apply Set.disjoint_left.mpr
    intro z hz hzc
    have : z ∈ cᶜ := hcover ▸ Or.inl hz
    exact this hzc
  have hFc (z : ℂ) : z ∈ c ↔ F z ∈ sphere (0 : ℂ) 1 := by
    rw [← hF, F.injective.mem_set_image]
  let b : c ≃ₜ Circle := F.subtype hFc
  obtain ⟨H, hH⟩ := hext b
  have hC : H '' {z : closure U | (z : ℂ) ∈ c} =
      {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (H z : ℂ) ∈ sphere (0 : ℂ) 1
      rw [hH ⟨z, hz⟩ z.property]
      exact (b ⟨z, hz⟩).property
    · intro hw
      obtain ⟨z, hz⟩ := b.surjective ⟨w, hw⟩
      refine ⟨⟨z, hcU z.property⟩, z.property, ?_⟩
      apply Subtype.ext
      exact (hH z (hcU z.property)).trans (congrArg Subtype.val hz)
  have hR : H '' {z : closure U | (z : ℂ) ∈ U} =
      {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1} := by
    have hUc : {z : closure U | (z : ℂ) ∈ U} =
        ({z : closure U | (z : ℂ) ∈ c})ᶜ := by
      ext z
      have hz : (z : ℂ) ∈ U ∪ c := hQcl ▸ z.property
      exact ⟨fun hu hc ↦ Set.disjoint_left.mp hdis hu hc, fun hc ↦ hz.resolve_right hc⟩
    rw [hUc, H.image_compl, hC]
    ext w
    change ¬ (w : ℂ) ∈ sphere (0 : ℂ) 1 ↔ (w : ℂ) ∈ ball (0 : ℂ) 1
    have hw := w.property
    simp only [mem_sphere, mem_ball, mem_closedBall] at *
    exact ⟨fun h ↦ lt_of_le_of_ne hw h, fun h ↦ ne_of_lt h⟩
  refine ⟨hcU, ⟨H, hR, hC⟩, ?_⟩
  intro h
  obtain ⟨G, hG⟩ := hext h
  exact ⟨G, fun z hz ↦ hG ⟨z, hz⟩ z.property⟩
end HolomorphicAnosov
