import Mathlib.Topology.GDelta.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Finite closed quadrant selection and atom coverage

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970), pp.735–736,
the definition of Z and B(z), and the finiteness and coverage argument of Lemma 21.
DAG node: `topo.finite_closed_quadrant_atoms_g18`.
-/

namespace HolomorphicAnosov.Topology

open Set

/-- Off the boundaries of finitely many closed quadrants, every relevant family
has a unique interior quadrant. Their selected finite intersections are open
neighborhoods, have only finitely many different closures, and those closures cover X.

Source: Bowen (1970), pp.735–736, the paragraph preceding Lemma 20 and Lemma 21.
Each closed quadrant has nowhere-dense boundary, so removing the finite union gives
a dense open set Z. Coverage and avoidance of boundaries give an interior quadrant;
disjoint interiors give uniqueness. Finite intersections of the selected open unions
are open and contain their indexing point. Their values are determined by the finite
Boolean membership profile for V and for the quadrant interiors. Thus their closures
have finite range. The union of closures indexed by Z is closed and contains the dense
set Z, hence is the whole space. Empty index sets and the empty space are allowed.
This theorem does not assert disjoint atom interiors: that further conclusion uses
Bowen's separate neighbor-profile argument in Lemma 20(b).
-/
theorem finite_closed_quadrant_atoms {X ι κ : Type*} [TopologicalSpace X]
    [Finite ι] [Finite κ] (K : ι → κ → Set X) (V : ι → Set X)
    (hclosed : ∀ i a, IsClosed (K i a))
    (hdisjoint : ∀ i, Pairwise fun a b ↦ Disjoint (interior (K i a)) (interior (K i b)))
    (hcover : ∀ i, V i ⊆ ⋃ a, K i a) :
    let Z := (⋃ i, ⋃ a, frontier (K i a))ᶜ
    let O := fun z ↦ ⋂ i, ⋂ (_ : z ∈ V i),
      ⋃ a, ⋃ (_ : z ∈ interior (K i a)), interior (K i a)
    IsOpen Z ∧ Dense Z ∧
      (∀ z ∈ Z, ∀ i, z ∈ V i → ∃! a, z ∈ interior (K i a)) ∧
      (∀ z ∈ Z, IsOpen (O z) ∧ z ∈ O z) ∧
      (Set.range fun z ↦ closure (O z)).Finite ∧
      (⋃ z ∈ Z, closure (O z)) = Set.univ := by
  classical
  dsimp only
  let Z := (⋃ i, ⋃ a, frontier (K i a))ᶜ
  let O := fun z ↦ ⋂ i, ⋂ (_ : z ∈ V i),
    ⋃ a, ⋃ (_ : z ∈ interior (K i a)), interior (K i a)
  have hfront : IsClosed (⋃ i, ⋃ a, frontier (K i a)) :=
    isClosed_iUnion_of_finite fun _ ↦ isClosed_iUnion_of_finite fun _ ↦ isClosed_frontier
  have hnowhere : IsNowhereDense (⋃ i, ⋃ a, frontier (K i a)) := by
    apply IsNowhereDense.iUnion
    intro i
    apply IsNowhereDense.iUnion
    intro a
    rw [isClosed_frontier.isNowhereDense_iff]
    exact interior_frontier (hclosed i a)
  have hZ : IsOpen Z ∧ Dense Z :=
    isClosed_isNowhereDense_iff_compl.mp ⟨hfront, hnowhere⟩
  have hchoice : ∀ z ∈ Z, ∀ i, z ∈ V i → ∃! a, z ∈ interior (K i a) := by
    intro z hz i hi
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcover i hi)
    have hai : z ∈ interior (K i a) := by
      apply (mem_interior_iff_notMem_frontier ha).mpr
      intro hf
      exact hz (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨a, hf⟩⟩)
    refine ⟨a, hai, ?_⟩
    intro b hb
    by_contra hba
    exact Set.disjoint_left.mp (hdisjoint i hba) hb hai
  have hO : ∀ z ∈ Z, IsOpen (O z) ∧ z ∈ O z := by
    intro z hz
    constructor
    · exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦
        isOpen_iUnion fun a ↦ isOpen_iUnion fun _ ↦ isOpen_interior
    · apply Set.mem_iInter.mpr
      intro i
      apply Set.mem_iInter.mpr
      intro hi
      obtain ⟨a, ha, _⟩ := hchoice z hz i hi
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, ha⟩⟩
  let coded : (Set ι × Set (ι × κ)) → Set X := fun p ↦
    closure (⋂ i, ⋂ (_ : i ∈ p.1), ⋃ a, ⋃ (_ : (i, a) ∈ p.2), interior (K i a))
  have hfinite : (Set.range fun z ↦ closure (O z)).Finite := by
    apply (Set.finite_range coded).subset
    rintro _ ⟨z, rfl⟩
    exact ⟨({i | z ∈ V i}, {p | z ∈ interior (K p.1 p.2)}), rfl⟩
  refine ⟨hZ.1, hZ.2, hchoice, hO, hfinite, ?_⟩
  apply Set.eq_univ_of_univ_subset
  rw [← hZ.2.closure_eq]
  apply closure_minimal
  · intro z hz
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, subset_closure (hO z hz).2⟩⟩
  · simpa only [Set.sUnion_image] using
      (hfinite.subset (Set.image_subset_range (fun z ↦ closure (O z)) Z)).isClosed_sUnion
        (by rintro _ ⟨z, _, rfl⟩; exact isClosed_closure)

end HolomorphicAnosov.Topology
