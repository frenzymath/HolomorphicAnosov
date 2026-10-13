import HolomorphicAnosov.Topology.CairnsRoundDiskCrosscutSeparation
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.Defs

/-!
# Transport of round-disk crosscut separation by an ambient homeomorphism

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
Lemma 5.1, p.866, and the homeomorphism transport used in the final §5 construction.
-/

open Set Metric
open scoped ComplexConjugate
namespace HolomorphicAnosov

/-- An ambient plane homeomorphism carrying a region to the disk and its marked
boundary to the circle transports the complete crosscut separation statement.

Source: Cairns (1951), Lemma 5.1 p.866, specialized through an already supplied
ambient homeomorphism; Mathlib homeomorphism preservation of connected components
and frontiers supplies the transport.

Proof: compose the embedded arc with the ambient homeomorphism and corestrict to
the closed disk. The closure image identity proves the corestriction is defined.
The endpoint and interior assumptions make it a genuine round-disk crosscut.
Apply the round-disk theorem and pull its two components back. A homeomorphism
preserves nonemptiness, openness, connectedness, disjointness and unions. It also
preserves relative connected components and ambient frontiers. Its injectivity
identifies the pulled-back cut image with the original arc, and the pulled-back
circle half-arcs are exactly the displayed signed chord predicates. Thus all the
component and frontier assertions hold with the same labels. -/
theorem cairns_crosscut_ambient_transport
    (H : ℂ ≃ₜ ℂ) (Q c : Set ℂ)
    (hQ : H '' Q = ball (0 : ℂ) 1) (hc : H '' c = sphere (0 : ℂ) 1)
    (η : unitInterval → closure Q) (hη : Topology.IsEmbedding η)
    (h0 : (η 0 : ℂ) ∈ c) (h1 : (η 1 : ℂ) ∈ c) (h01 : η 0 ≠ η 1)
    (hinterior : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      (η t : ℂ) ∈ Q) :
    let δ : unitInterval → ℂ := fun t ↦ (η t : ℂ)
    let K : Set ℂ := range δ
    let Kopen : Set ℂ := δ '' {t : unitInterval | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
    let Ω : Set ℂ := Q \ Kopen
    let A : Fin 2 → Set ℂ := fun i ↦
      {z | z ∈ c ∧
        if i = 0 then (conj (H (δ 1) - H (δ 0)) * (H z - H (δ 0))).im ≤ 0
        else 0 ≤ (conj (H (δ 1) - H (δ 0)) * (H z - H (δ 0))).im}
    ∃ V : Fin 2 → Set ℂ,
      (∀ i, (V i).Nonempty ∧ IsOpen (V i) ∧ IsConnected (V i)) ∧
      Disjoint (V 0) (V 1) ∧ (⋃ i, V i) = Ω ∧
      (fun z : ℂ ↦ connectedComponentIn Ω z) '' Ω = range V ∧
      (∀ i, frontier (V i) = K ∪ A i) := by
  let δ : unitInterval → ℂ := fun t ↦ (η t : ℂ)
  have hcl : H '' closure Q = closedBall (0 : ℂ) 1 := by
    rw [H.image_closure, hQ, closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  have hgmem (t : unitInterval) : H (δ t) ∈ closedBall (0 : ℂ) 1 := by
    rw [← hcl]
    exact ⟨δ t, (η t).property, rfl⟩
  let g : unitInterval → closedBall (0 : ℂ) 1 := fun t ↦ ⟨H (δ t), hgmem t⟩
  have hg : Topology.IsEmbedding g :=
    (H.isEmbedding.comp (Topology.IsEmbedding.subtypeVal.comp hη)).codRestrict _ hgmem
  have hg0 : (g 0 : ℂ) ∈ sphere (0 : ℂ) 1 := hc ▸ ⟨δ 0, h0, rfl⟩
  have hg1 : (g 1 : ℂ) ∈ sphere (0 : ℂ) 1 := hc ▸ ⟨δ 1, h1, rfl⟩
  have hg01 : g 0 ≠ g 1 := by
    intro heq
    apply h01
    apply Subtype.ext
    exact H.injective (congrArg Subtype.val heq)
  have hgin (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
      (g t : ℂ) ∈ ball (0 : ℂ) 1 := hQ ▸ ⟨δ t, hinterior t ht0 ht1, rfl⟩
  obtain ⟨V, hV, hdis, hcover, hcomp, hfront, _⟩ :=
    cairns_round_disk_crosscut_separation g hg hg0 hg1 hg01 hgin
  let I : Set unitInterval := {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}
  let Ω : Set ℂ := Q \ δ '' I
  let Ω' : Set ℂ := ball (0 : ℂ) 1 \ (fun t ↦ H (δ t)) '' I
  have hΩ : H '' Ω = Ω' := by
    dsimp [Ω, Ω']
    rw [Set.image_sdiff H.injective, hQ, Set.image_image]
  have hpreΩ : H ⁻¹' Ω' = Ω := by rw [← hΩ, H.preimage_image]
  change ∃ W : Fin 2 → Set ℂ, _
  refine ⟨fun i ↦ H ⁻¹' V i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, (hV i).2.2.preimage H.continuous, H.isConnected_preimage.mpr (hV i).2.1⟩
    obtain ⟨z, hz⟩ := (hV i).1
    exact ⟨H.symm z, by simpa using hz⟩
  · exact hdis.preimage H
  · change (⋃ i, H ⁻¹' V i) = Ω
    rw [← Set.preimage_iUnion]
    exact (congrArg (fun s ↦ H ⁻¹' s) hcover).trans hpreΩ
  · change (fun z ↦ connectedComponentIn Ω z) '' Ω = range (fun i ↦ H ⁻¹' V i)
    have ht (z : ℂ) (hz : z ∈ Ω) :
        H ⁻¹' connectedComponentIn Ω' (H z) = connectedComponentIn Ω z := by
      rw [← hΩ, ← H.image_connectedComponentIn hz, H.preimage_image]
    ext C
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hmem : connectedComponentIn Ω' (H z) ∈ range V := by
        rw [← hcomp]
        exact ⟨H z, (show H z ∈ Ω' from hΩ ▸ ⟨z, hz, rfl⟩), rfl⟩
      obtain ⟨i, hi⟩ := hmem
      exact ⟨i, by
        change H ⁻¹' V i = connectedComponentIn Ω z
        rw [hi, ht z hz]⟩
    · rintro ⟨i, rfl⟩
      have hmem : V i ∈ (fun z ↦ connectedComponentIn Ω' z) '' Ω' := by
        rw [hcomp]
        exact ⟨i, rfl⟩
      obtain ⟨z, hz, heq⟩ := hmem
      have hz' : H.symm z ∈ Ω := by
        rw [← hpreΩ]
        simpa using hz
      refine ⟨H.symm z, hz', ?_⟩
      change connectedComponentIn Ω (H.symm z) = H ⁻¹' V i
      change connectedComponentIn Ω' z = V i at heq
      rw [← ht _ hz', H.apply_symm_apply, heq]
  · intro i
    rw [← H.preimage_frontier, hfront i, Set.preimage_union]
    congr 1
    · ext z
      simp only [mem_preimage, mem_range]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t, H.injective ht⟩
      · rintro ⟨t, rfl⟩
        exact ⟨t, rfl⟩
    · ext z
      have hmem : H z ∈ sphere (0 : ℂ) 1 ↔ z ∈ c := by
        rw [← hc]
        exact H.injective.mem_set_image
      simp only [mem_preimage, mem_ofPred_eq, g, δ]
      rw [hmem]

end HolomorphicAnosov
