import Mathlib.Topology.OpenPartialHomeomorph.Constructions

namespace HolomorphicAnosov.Ghys

open Set

/-- A product box with open image transports partial coordinates on its factors to an ambient
partial coordinate chart. (HPS, §7 pp.115–116) -/
theorem projective_box_product_coordinates
    {M S T X Y : Type*} [TopologicalSpace M] [TopologicalSpace S]
    [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty S] [Nonempty T]
    (U : Set M) (hU : IsOpen U) (e : (S × T) ≃ₜ U)
    (c : OpenPartialHomeomorph S X) (d : OpenPartialHomeomorph T Y) :
    ∃ b : OpenPartialHomeomorph M (X × Y),
      b.source = (fun z : S × T => (e z).val) '' (c.source ×ˢ d.source) ∧
      b.target = c.target ×ˢ d.target ∧
      ∀ s t, b (e (s, t)).val = (c s, d t) := by
  let j : S × T → M := fun z => (e z).val
  have hj : Topology.IsOpenEmbedding j :=
    hU.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let B := hj.toOpenPartialHomeomorph j
  refine ⟨B.symm.trans (c.prod d), ?_, ?_, ?_⟩
  · simp only [OpenPartialHomeomorph.trans_source'', OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.symm_symm]
    simp only [B, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      univ_inter, OpenPartialHomeomorph.prod_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    rfl
  · simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      B, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ,
      inter_univ, OpenPartialHomeomorph.prod_target]
  · intro s t
    change (c.prod d) (B.symm (j (s, t))) = _
    rw [show B.symm (j (s, t)) = (s, t) from hj.toOpenPartialHomeomorph_left_inv j]
    rfl

end HolomorphicAnosov.Ghys
