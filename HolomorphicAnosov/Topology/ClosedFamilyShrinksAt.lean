import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Tactic.Linarith

/-!
# Shrinking of a closed family with finitely many large members

This is the finite-exception metric argument used in Hatcher's dyadic complement
construction, Algebraic Topology, proof of Theorem A.7, pp.525–526.
-/

namespace HolomorphicAnosov

/-- A closed family avoiding a point shrinks there if its pairwise distance bounds
have only finitely many large members meeting a fixed neighborhood of the point.

Source: Hatcher, proof of Theorem A.7, pp.525–526, shrinking cells in the complement.
This explicit metric proof expands the source's shrinking assertion. For ε>0,
consider the finitely many members meeting the radius-R ball whose size is at least
ε/2. Their closed union avoids c, so a sufficiently small ball about c avoids it.
Choose δ also at most R and ε/2. A member meeting the δ-ball is not exceptional,
so its size is below ε/2. The triangle inequality from a witnessing point gives
distance below ε for every point of that member. Empty members, an empty index
type, and nonpositive unused size bounds cause no exceptional cases. -/
theorem closed_family_shrinks_at
    {X ι : Type*} [MetricSpace X] (A : ι → Set X) (size : ι → ℝ) (c : X)
    (hclosed : ∀ i, IsClosed (A i)) (havoid : ∀ i, c ∉ A i)
    (hsize : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y ≤ size i)
    (R : ℝ) (hR : 0 < R)
    (hfinite : ∀ η : ℝ, 0 < η →
      {i | (∃ x ∈ A i, dist x c < R) ∧ η ≤ size i}.Finite) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ i, (∃ x ∈ A i, dist x c < δ) → ∀ y ∈ A i, dist y c < ε := by
  intro ε hε
  let F : Set ι := {i | (∃ x ∈ A i, dist x c < R) ∧ ε / 2 ≤ size i}
  have hF : F.Finite := hfinite (ε / 2) (half_pos hε)
  have hU : IsOpen (⋃ i ∈ F, A i)ᶜ := (hF.isClosed_biUnion fun i _ ↦ hclosed i).isOpen_compl
  have hc : c ∈ (⋃ i ∈ F, A i)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun i _ ↦ havoid i
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU c hc
  let δ := min r (min R (ε / 2))
  refine ⟨δ, lt_min hr (lt_min hR (half_pos hε)), ?_⟩
  intro i hi y hy
  obtain ⟨x, hx, hxc⟩ := hi
  have hxr : dist x c < r := hxc.trans_le (min_le_left _ _)
  have hxR : dist x c < R := hxc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hxε : dist x c < ε / 2 :=
    hxc.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : size i < ε / 2 := by
    by_contra hn
    have hiF : i ∈ F := ⟨⟨x, hx, hxR⟩, le_of_not_gt hn⟩
    exact (hball (show x ∈ Metric.ball c r from hxr)) (Set.mem_iUnion₂.mpr ⟨i, hiF, hx⟩)
  calc
    dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
    _ ≤ size i + dist x c := add_le_add (hsize i y hy x hx) le_rfl
    _ < ε := by linarith

end HolomorphicAnosov

