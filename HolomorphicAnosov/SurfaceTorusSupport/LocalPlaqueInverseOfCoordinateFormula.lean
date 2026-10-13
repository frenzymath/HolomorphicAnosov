import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set Filter Topology _root_.Topology

namespace HolomorphicAnosov

/-- An intrinsic plaque coordinate formula gives a continuous inverse on an open horizontal ambient
slice around the marked point. (Ghys, §5, pp. 598–599) -/
theorem local_plaque_inverse_of_coordinate_formula
    {L M P Q : Type*} [TopologicalSpace L] [TopologicalSpace M]
    [TopologicalSpace P] [TopologicalSpace Q]
    (j : L → M) (b : OpenPartialHomeomorph M (P × Q))
    (c : OpenPartialHomeomorph L P) (a : L) (q : Q)
    (hlocal : ∀ᶠ z in 𝓝 a,
      z ∈ c.source ∧ j z ∈ b.source ∧ b (j z) = (c z, q)) :
    ∃ V : Set P, IsOpen V ∧ c a ∈ V ∧ V ⊆ c.target ∧
      ContinuousOn c.symm V ∧
      ∀ p ∈ V, (p, q) ∈ b.target ∧ j (c.symm p) = b.symm (p, q) := by
  obtain ⟨W, hWsub, hW, haW⟩ := mem_nhds_iff.mp hlocal
  have hWc : W ⊆ c.source := fun z hz ↦ (hWsub hz).1
  refine ⟨c '' W, c.isOpen_image_of_subset_source hW hWc, ⟨a, haW, rfl⟩,
    ?_, ?_, ?_⟩
  · rintro p ⟨z, hz, rfl⟩
    exact c.map_source (hWc hz)
  · exact c.continuousOn_symm.mono (by
      rintro p ⟨z, hz, rfl⟩
      exact c.map_source (hWc hz))
  · rintro p ⟨z, hz, rfl⟩
    obtain ⟨hzc, hjz, heq⟩ := hWsub hz
    rw [c.left_inv hzc]
    constructor
    · rw [← heq]
      exact b.map_source hjz
    · rw [← heq, b.left_inv hjz]


end HolomorphicAnosov
