import Mathlib.Analysis.SpecialFunctions.Complex.Circle
namespace HolomorphicAnosov.Topology
open Set
/-- Split an embedded circle at two distinct marked image points into its two directed arcs. -/
theorem circle_split_two_arcs {E : Type*} [TopologicalSpace E] [T2Space E]
    (j : Circle → E) (hj : Topology.IsEmbedding j)
    (a b : E) (ha : a ∈ range j) (hb : b ∈ range j) (hab : a ≠ b) :
    ∃ u v : Circle, j u = a ∧ j v = b ∧ u ≠ v ∧
      ∃ e₂ e₃ : unitInterval → E,
        Topology.IsEmbedding e₂ ∧ Topology.IsEmbedding e₃ ∧
        e₂ 0 = a ∧ e₂ 1 = b ∧ e₃ 0 = b ∧ e₃ 1 = a ∧
        range e₂ ∪ range e₃ = range j ∧
        range e₂ ∩ range e₃ = {a, b} := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have huv : u ≠ v := by
    intro huv
    apply hab
    rw [← hv, huv]
  let e₂ : unitInterval → E := j ∘ Circle.path u v
  let e₃ : unitInterval → E := j ∘ Circle.path v u
  have he₂ : Topology.IsEmbedding e₂ := by
    exact hj.comp ((Circle.path u v).continuous.isClosedEmbedding
      (Circle.path_injective_of_ne huv)).isEmbedding
  have he₃ : Topology.IsEmbedding e₃ := by
    exact hj.comp ((Circle.path v u).continuous.isClosedEmbedding
      (Circle.path_injective_of_ne huv.symm)).isEmbedding
  have h0₂ : e₂ 0 = j u := by
    simp [e₂, Circle.path]
  have h1₂ : e₂ 1 = j v := by
    simp [e₂, Circle.path]
  have h0₃ : e₃ 0 = j v := by
    simp [e₃, Circle.path]
  have h1₃ : e₃ 1 = j u := by
    simp [e₃, Circle.path]
  have hun : range e₂ ∪ range e₃ = range j := by
    rw [range_comp, range_comp, ← image_union, Circle.range_path_union_range_path huv]
    simp
  have hint : range e₂ ∩ range e₃ = {j u, j v} := by
    rw [range_comp, range_comp, ← image_inter hj.injective,
      Circle.range_path_inter_range_path huv]
    exact Set.image_pair j u v
  refine ⟨u, v, rfl, hv, huv, e₂, e₃, he₂, he₃, ?_, ?_, ?_, ?_, hun, ?_⟩
  · exact h0₂.trans rfl
  · rw [h1₂, hv]
  · rw [h0₃, hv]
  · exact h1₃.trans rfl
  · simp [hint, hv]
end HolomorphicAnosov.Topology
