import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Connected.LocallyConnected

/-!
# The neighborhoods in Conway's Janiszewski proof

Source: Conway, Functions of One Complex Variable II (1995), Chapter 14,
Lemma 5.4, printed p.49, first paragraph of the proof. The source chooses the
component G containing the intersection and disjoint neighborhoods of the two
compact remainders. The generic topological formulation below retains exactly
those constructions; normality replaces the source's metric separation argument.
-/

open Set
namespace HolomorphicAnosov.Topology

/-- The intersection of two compact sets, if connected and nonempty, lies in one
open component outside two closed forbidden sets that respectively miss them.
The remainders outside that component have disjoint open neighborhoods, each
missing its own forbidden set. Their union with the component contains both
compact sets and misses the intersection of the forbidden sets.

Source: Conway II, Chapter 14 Lemma 5.4, p.49.
Proof: Choose a point a in the intersection. Its connectedness puts the full
intersection in G, the component of the complement of the forbidden union at a.
Local connectedness makes G open. The compact remainders K₁\G and K₂\G are
disjoint closed sets; normality gives disjoint open neighborhoods. Intersect each
neighborhood with the complement of its respective closed forbidden set. The
result still contains its remainder. The assertions about the union follow by
splitting membership in G; every piece misses at least one forbidden set.
The compact remainders may be empty, and the original compact sets need not be
connected individually for this step. -/
theorem janiszewski_neighborhoods
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    [LocallyConnectedSpace X]
    (K₁ K₂ P₁ P₂ : Set X)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hinter : IsConnected (K₁ ∩ K₂))
    (hP₁ : IsClosed P₁) (hP₂ : IsClosed P₂)
    (havoid₁ : Disjoint K₁ P₁) (havoid₂ : Disjoint K₂ P₂) :
    ∃ a ∈ K₁ ∩ K₂,
      let G := connectedComponentIn (P₁ ∪ P₂)ᶜ a
      ∃ V₁ V₂ : Set X,
        IsOpen G ∧ IsConnected G ∧ K₁ ∩ K₂ ⊆ G ∧
        IsOpen V₁ ∧ IsOpen V₂ ∧ Disjoint V₁ V₂ ∧
        K₁ \ G ⊆ V₁ ∧ K₂ \ G ⊆ V₂ ∧
        V₁ ⊆ P₁ᶜ ∧ V₂ ⊆ P₂ᶜ ∧
        K₁ ∪ K₂ ⊆ G ∪ V₁ ∪ V₂ ∧
        G ∪ V₁ ∪ V₂ ⊆ (P₁ ∩ P₂)ᶜ := by
  obtain ⟨a, ha⟩ := hinter.nonempty
  let G := connectedComponentIn (P₁ ∪ P₂)ᶜ a
  have hinterP : K₁ ∩ K₂ ⊆ (P₁ ∪ P₂)ᶜ := by
    intro x hx hp
    rcases hp with hp | hp
    · exact Set.disjoint_left.mp havoid₁ hx.1 hp
    · exact Set.disjoint_left.mp havoid₂ hx.2 hp
  have hG : IsOpen G := (hP₁.union hP₂).isOpen_compl.connectedComponentIn
  have hcG : IsConnected G := isConnected_connectedComponentIn_iff.mpr (hinterP ha)
  have hsub : K₁ ∩ K₂ ⊆ G :=
    hinter.isPreconnected.subset_connectedComponentIn ha hinterP
  have hdis : Disjoint (K₁ \ G) (K₂ \ G) := by
    apply Set.disjoint_left.mpr
    intro z hz₁ hz₂
    exact hz₁.2 (hsub ⟨hz₁.1, hz₂.1⟩)
  obtain ⟨W₁, W₂, ho₁, ho₂, hs₁, hs₂, hd⟩ :=
    normal_separation (hK₁.diff hG).isClosed (hK₂.diff hG).isClosed hdis
  let V₁ := W₁ ∩ P₁ᶜ
  let V₂ := W₂ ∩ P₂ᶜ
  have hv₁ : K₁ \ G ⊆ V₁ := fun z hz ↦
    ⟨hs₁ hz, fun hp ↦ Set.disjoint_left.mp havoid₁ hz.1 hp⟩
  have hv₂ : K₂ \ G ⊆ V₂ := fun z hz ↦
    ⟨hs₂ hz, fun hp ↦ Set.disjoint_left.mp havoid₂ hz.1 hp⟩
  refine ⟨a, ha, V₁, V₂, hG, hcG, hsub, ho₁.inter hP₁.isOpen_compl,
    ho₂.inter hP₂.isOpen_compl, hd.mono inter_subset_left inter_subset_left,
    hv₁, hv₂, inter_subset_right, inter_subset_right, ?_, ?_⟩
  · intro z hz
    by_cases hzG : z ∈ G
    · exact Or.inl (Or.inl hzG)
    · rcases hz with hz | hz
      · exact Or.inl (Or.inr (hv₁ ⟨hz, hzG⟩))
      · exact Or.inr (hv₂ ⟨hz, hzG⟩)
  · rintro z ((hz | hz) | hz) hp
    · exact connectedComponentIn_subset (P₁ ∪ P₂)ᶜ a hz (Or.inl hp.1)
    · exact hz.2 hp.1
    · exact hz.2 hp.2

end HolomorphicAnosov.Topology
