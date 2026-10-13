import HolomorphicAnosov.Linear.HyperbolicDecayAux40

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Complementarity of the full complex forward- and inverse-decay spaces implies complementarity of
the corresponding real decay spaces. (Alves, Thm 5.5, p. 17) -/
theorem real_isCompl_of_complex_full_decay
    (A : V ≃L[ℝ] V) (S U : Submodule ℝ V)
    (Sc Uc : Submodule ℂ (CoordinateSpace (V := V)))
    (hS : ∀ v, v ∈ S ↔ Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0))
    (hU : ∀ v, v ∈ U ↔ Tendsto (fun n : ℕ ↦ (A.symm ^ n) v) atTop (𝓝 0))
    (hSc : ∀ w, w ∈ Sc ↔ Tendsto (fun n : ℕ ↦ (complexified A ^ n) w) atTop (𝓝 0))
    (hUc : ∀ w, w ∈ Uc ↔ Tendsto (fun n : ℕ ↦ ((complexified A).symm ^ n) w)
      atTop (𝓝 0))
    (hc : IsCompl Sc Uc) : IsCompl S U := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro v hv
    have hs : coordinateEmbedding v ∈ Sc :=
      (hSc _).2 ((embedding_decay_iff A v).2 ((hS v).1 hv.1))
    have hu : coordinateEmbedding v ∈ Uc := by
      apply (hUc _).2
      simpa only [complexified_symm] using
        (embedding_decay_iff A.symm v).2 ((hU v).1 hv.2)
    have hz : coordinateEmbedding v = 0 := hc.disjoint.le_bot ⟨hs, hu⟩
    have hz' := congrArg coordinateRealPart hz
    simpa only [coordinateRealPart_embedding, map_zero, Submodule.mem_bot] using hz'
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨w, hw, _⟩ := Submodule.existsUnique_add_of_isCompl_prod hc (coordinateEmbedding v)
    rw [Submodule.mem_sup]
    refine ⟨coordinateRealPart (w.1 : CoordinateSpace), ?_,
      coordinateRealPart (w.2 : CoordinateSpace), ?_, ?_⟩
    · exact (hS _).2 (realPart_decay A _ ((hSc _).1 w.1.property))
    · apply (hU _).2
      apply realPart_decay A.symm
      simpa only [complexified_symm] using (hUc _).1 w.2.property
    · have hsum := congrArg coordinateRealPart hw
      simpa only [map_add, coordinateRealPart_embedding] using hsum

end RealDecayDescent

end
end HolomorphicAnosov
