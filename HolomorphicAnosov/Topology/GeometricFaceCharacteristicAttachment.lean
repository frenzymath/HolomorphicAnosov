import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.CWComplex.Classical.Finite

/-! Hatcher, Algebraic Topology, §2.1 pp.104,107 and Proposition A.2 p.521: the boundary and covering conditions for characteristic maps indexed by the nonempty faces of a geometric simplicial complex. -/

namespace HolomorphicAnosov
open Set Topology _root_.Topology Metric

/-- A characteristic family whose closed-disk image is each geometric face and whose sphere image is its proper nonempty subfaces satisfies the classical CW lower-skeleton attachment and closed-cell covering conditions on the original simplicial carrier. -/
theorem geometric_face_characteristic_attachment (N : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (χ : ∀ n : ℕ,
      {s : Finset (EuclideanSpace ℝ (Fin N)) // s ∈ P.faces ∧ s.card = n + 1} →
      (Fin n → ℝ) → ↥P.space)
    (hclosed : ∀ n s, χ n s '' closedBall 0 1 =
      {x : ↥P.space | x.1 ∈ convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin N)))})
    (hboundary : ∀ n s, χ n s '' sphere 0 1 =
      {x : ↥P.space | ∃ t : Finset (EuclideanSpace ℝ (Fin N)),
        t.Nonempty ∧ t ⊂ s.1 ∧
          x.1 ∈ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin N)))}) :
    (∀ n s, MapsTo (χ n s) (sphere 0 1)
      (⋃ (m < n) (t : {t : Finset (EuclideanSpace ℝ (Fin N)) //
        t ∈ P.faces ∧ t.card = m + 1}), χ m t '' closedBall 0 1)) ∧
    (⋃ n, ⋃ s, χ n s '' closedBall 0 1) = univ := by
  classical
  constructor
  · intro n s x hx
    have hmem : χ n s x ∈ χ n s '' sphere 0 1 := ⟨x, hx, rfl⟩
    rw [hboundary] at hmem
    obtain ⟨t, ht, hts, hxt⟩ := hmem
    have hpos : 0 < t.card := Finset.card_pos.mpr ht
    have hdim : t.card - 1 + 1 = t.card := by omega
    have hlt : t.card - 1 < n := by
      have hcard := Finset.card_lt_card hts
      have hs := s.2.2
      omega
    let j : {v : Finset (EuclideanSpace ℝ (Fin N)) //
        v ∈ P.faces ∧ v.card = (t.card - 1) + 1} :=
      ⟨t, P.down_closed s.2.1 hts.le ht, hdim.symm⟩
    apply mem_iUnion.mpr
    refine ⟨t.card - 1, mem_iUnion.mpr ⟨hlt, mem_iUnion.mpr ⟨j, ?_⟩⟩⟩
    rw [hclosed]
    exact hxt
  · apply eq_univ_of_forall
    intro x
    obtain ⟨s, hs, hxs⟩ := P.mem_space_iff.mp x.2
    have hpos : 0 < s.card := Finset.card_pos.mpr (P.nonempty_of_mem_faces hs)
    let j : {v : Finset (EuclideanSpace ℝ (Fin N)) //
        v ∈ P.faces ∧ v.card = (s.card - 1) + 1} := ⟨s, hs, by omega⟩
    apply mem_iUnion.mpr
    refine ⟨s.card - 1, mem_iUnion.mpr ⟨j, ?_⟩⟩
    rw [hclosed]
    exact hxs

end HolomorphicAnosov
