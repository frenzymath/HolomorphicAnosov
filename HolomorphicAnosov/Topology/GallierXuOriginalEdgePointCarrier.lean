import HolomorphicAnosov.Topology.GallierXuOriginalEdgePoint

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- An original edge parameter belongs to the native carrier whenever its endpoint
edge is a face of the complex. -/
lemma originalEdgePoint_mem_carrier {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) {u v : Fin N}
    (hedge : ({u, v} : Finset (Fin N)) ∈ K.faces) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    originalEdgePoint u v t ∈ carrier K := by
  have hsimplex : (∀ w, 0 ≤ originalEdgePoint u v t w) ∧
      ∑ w, originalEdgePoint u v t w = 1 := by
    constructor
    · intro w
      simp only [originalEdgePoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr ht.2) (by simp [Pi.single_apply]; split <;> positivity))
        (mul_nonneg ht.1 (by simp [Pi.single_apply]; split <;> positivity))
    · simp [originalEdgePoint, Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul,
        ← Finset.mul_sum]
  refine ⟨hsimplex, {u, v}, hedge, ?_⟩
  intro w hw
  simp only [originalEdgePoint, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
  have hwu : w ≠ u := by
    intro h; exact hw (by simp [h])
  have hwv : w ≠ v := by
    intro h; exact hw (by simp [h])
  by_cases huv : u ≤ v
  · simp [min_eq_left huv, max_eq_right huv, hwu, hwv]
  · have hvu : v ≤ u := le_of_not_ge huv
    simp [min_eq_right hvu, max_eq_left hvu, hwu, hwv]

end HolomorphicAnosov.Topology.GallierXu
