import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic

/-!
Elementary intersection and finite-prefix union identities for the developing-map
induction. (Ghys, Lemma 5.2, pp. 599–600)
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- Two nonempty open sets whose union is connected have nonempty intersection.
(Ghys, Lemma 5.2, pp. 599–600) -/
theorem source_overlap_of_connected_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hconn : IsConnected (A ∪ B)) :
    (A ∩ B).Nonempty := by
  by_contra h
  have hd : Disjoint A B := Set.disjoint_iff_inter_eq_empty.mpr
    (Set.not_nonempty_iff_eq_empty.mp h)
  have hsub := hconn.isPreconnected.subset_left_of_subset_union hA hB hd
    (Set.Subset.refl _) (by
      obtain ⟨x, hx⟩ := hAne
      exact ⟨x, Or.inl hx, hx⟩)
  obtain ⟨y, hy⟩ := hBne
  exact Set.disjoint_left.mp hd (hsub (Or.inr hy)) hy

/-- The union of the first `n + 1` sets is the union of the first `n` sets with `s n`.
(Ghys, Lemma 5.2, p. 599) -/
theorem prefix_succ {X : Type*} (s : ℕ → Set X) (n : ℕ) :
    (⋃ i ∈ Finset.range (n + 1), s i) = (⋃ i ∈ Finset.range n, s i) ∪ s n := by
  ext x
  simp only [mem_iUnion, Finset.mem_range, mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hin | rfl
    · exact Or.inl ⟨i, hin, hx⟩
    · exact Or.inr hx
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
    · exact ⟨n, Nat.lt_succ_self n, hx⟩


end HolomorphicAnosov.Ghys
