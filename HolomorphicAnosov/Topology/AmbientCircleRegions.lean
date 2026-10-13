import HolomorphicAnosov.Topology.CircleComplementRegions
import HolomorphicAnosov.Topology.DiskPrescribedBoundaryExtension

/-!
# Complementary regions of an ambient image of the circle

Cairns (1951), §1 and §2(A), p.860, and Hirsch (1976), p.155.
DAG node: `topo.ambient_circle_regions_g6`.
-/

noncomputable section
open Set Metric

namespace HolomorphicAnosov

/-- Transport the two circular regions and prescribed boundary extension through an
ambient plane homeomorphism. Source: Cairns (1951), §1 and §2(A), printed p.860;
Hirsch, Differential Topology, p.155. Take the preimages of the open unit disk and
of the exterior of the closed disk. Homeomorphisms preserve components, openness,
frontiers and closures. The closed bounded region is the continuous image under
the inverse homeomorphism of the compact closed unit disk, hence compact and bounded.
If the exterior were bounded too, their union would bound the whole plane, a
contradiction. Restrict the ambient homeomorphism to the closed region, identify
its boundary with the circle, and apply prescribed disk boundary extension.
-/
theorem ambient_circle_regions (c : Set ℂ) (H : ℂ ≃ₜ ℂ)
    (hH : H '' c = sphere (0 : ℂ) 1) :
    ∃ Q E : Set ℂ,
      Q.Nonempty ∧ E.Nonempty ∧ Q ≠ E ∧ Q ∪ E = cᶜ ∧ Disjoint Q E ∧
      (fun z : ℂ ↦ connectedComponentIn cᶜ z) '' cᶜ = {Q, E} ∧
      IsConnected Q ∧ IsConnected E ∧ IsOpen Q ∧ IsOpen E ∧
      Bornology.IsBounded Q ∧ ¬Bornology.IsBounded E ∧
      frontier Q = c ∧ frontier E = c ∧ closure Q = Q ∪ c ∧
      (∀ b : c ≃ₜ Circle,
        ∃ F : closure Q ≃ₜ closedBall (0 : ℂ) 1,
          ∀ x : c, ∀ hx : x.val ∈ closure Q, (F ⟨x.val, hx⟩ : ℂ) = b x) := by
  obtain ⟨hQ, hE, hoQ, hoE, hu, hd, hcomponents, hfQ, hfE, hcQ⟩ :=
    circle_complement_regions
  let Q := H ⁻¹' ball (0 : ℂ) 1
  let E := H ⁻¹' (closedBall (0 : ℂ) 1)ᶜ
  have hc : H ⁻¹' sphere (0 : ℂ) 1 = c := by rw [← hH, H.preimage_image]
  have hQc : IsConnected Q := H.isConnected_preimage.mpr hQ
  have hEc : IsConnected E := H.isConnected_preimage.mpr hE
  have hun : Q ∪ E = cᶜ := by rw [← preimage_union, hu, preimage_compl, hc]
  have hdis : Disjoint Q E := hd.preimage H
  have hclosure : closure Q = H ⁻¹' closedBall (0 : ℂ) 1 := by
    change closure (H ⁻¹' ball (0 : ℂ) 1) = _
    rw [← H.preimage_closure, hcQ]
  have hcompact : IsCompact (H ⁻¹' closedBall (0 : ℂ) 1) :=
    H.symm.image_eq_preimage_symm (closedBall (0 : ℂ) 1) ▸
      (isCompact_closedBall (0 : ℂ) 1).image H.symm.continuous
  refine ⟨Q, E, hQc.nonempty, hEc.nonempty, ?_, hun, hdis, ?_, hQc, hEc,
    hoQ.preimage H.continuous, hoE.preimage H.continuous,
    hcompact.isBounded.subset (preimage_mono ball_subset_closedBall), ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    obtain ⟨z, hz⟩ := hQc.nonempty
    exact disjoint_left.mp hdis hz (heq ▸ hz)
  · have heq (z : ℂ) (hz : z ∈ cᶜ) :
        connectedComponentIn cᶜ z = H ⁻¹' connectedComponentIn (sphere (0 : ℂ) 1)ᶜ (H z) := by
      have him : H '' cᶜ = (sphere (0 : ℂ) 1)ᶜ := by rw [H.image_compl, hH]
      rw [← him, ← H.image_connectedComponentIn hz, H.preimage_image]
    ext A
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hm : connectedComponentIn (sphere (0 : ℂ) 1)ᶜ (H z) ∈
          ({ball (0 : ℂ) 1, (closedBall (0 : ℂ) 1)ᶜ} : Set (Set ℂ)) := by
        rw [← hcomponents]
        exact ⟨H z, by simpa [← hc] using hz, rfl⟩
      change connectedComponentIn cᶜ z ∈ ({Q, E} : Set (Set ℂ))
      rw [heq z hz]
      rcases hm with hm | hm
      · simp [hm, Q]
      · have hm' : connectedComponentIn (sphere (0 : ℂ) 1)ᶜ (H z) =
            (closedBall (0 : ℂ) 1)ᶜ := hm
        simp [hm', E]
    · intro hA
      have hm : ∃ B ∈ ({ball (0 : ℂ) 1, (closedBall (0 : ℂ) 1)ᶜ} : Set (Set ℂ)),
          A = H ⁻¹' B := by
        rcases hA with hA | hA
        · exact ⟨_, by simp, hA⟩
        · exact ⟨_, by simp, hA⟩
      obtain ⟨B, hB, rfl⟩ := hm
      rw [← hcomponents] at hB
      obtain ⟨w, hw, rfl⟩ := hB
      have hz : H.symm w ∈ cᶜ := by simpa [← hc] using hw
      exact ⟨H.symm w, hz, by simpa using heq (H.symm w) hz⟩
  · intro hbounded
    apply NormedSpace.unbounded_univ ℝ ℂ
    have hb := hcompact.isBounded.union hbounded
    have hall : (H ⁻¹' closedBall (0 : ℂ) 1) ∪ E = univ := by
      simp [E]
    rwa [hall] at hb
  · change frontier (H ⁻¹' ball (0 : ℂ) 1) = c
    rw [← H.preimage_frontier, hfQ, hc]
  · change frontier (H ⁻¹' (closedBall (0 : ℂ) 1)ᶜ) = c
    rw [← H.preimage_frontier, hfE, hc]
  · rw [hclosure, ← hc, ← preimage_union]
    congr 1
    ext z
    simp only [mem_closedBall, mem_union, mem_ball, mem_sphere]
    exact le_iff_lt_or_eq
  · intro b
    have hcsub : c ⊆ closure Q := by
      rw [hclosure, ← hc]
      exact preimage_mono sphere_subset_closedBall
    let F₀ : closure Q ≃ₜ closedBall (0 : ℂ) 1 :=
      H.subtype (fun z ↦ by
        rw [hclosure]; rfl)
    apply disk_prescribed_boundary_extension c (closure Q) hcsub F₀ ?_ b
    intro x
    change x.val ∈ c ↔ ‖H x.val‖ = 1
    rw [← hc]
    simp

end HolomorphicAnosov
