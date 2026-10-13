import Mathlib.Topology.Connected.Basic

open Set

namespace HolomorphicAnosov

/-- If two disjoint open regions cover the complement of their common frontier,
and a neighborhood of a common frontier point has exactly two preconnected local
sides, those sides belong to different regions.

Agent-written detail of Cairns (1951), Theorem 2.1, p.860, the local side argument used for a
transverse polygon crossing. Each preconnected side lies in one of the two open
regions. Every neighborhood of the frontier point meets each region. Thus both
sides cannot lie in the same region, leaving precisely the two opposite labelings.
This argument is purely topological and applies to any supplied local sides. -/
theorem two_local_sides_separation {X : Type*} [TopologicalSpace X]
    {c Q E U P N : Set X} {x : X}
    (hQ : IsOpen Q) (hE : IsOpen E) (hdis : Disjoint Q E)
    (hcover : Q ∪ E = cᶜ)
    (hxQ : x ∈ closure Q) (hxE : x ∈ closure E)
    (hU : IsOpen U) (hxU : x ∈ U)
    (hP : IsPreconnected P) (hN : IsPreconnected N)
    (hsides : U \ c = P ∪ N) :
    (P ⊆ Q ∧ N ⊆ E) ∨ (P ⊆ E ∧ N ⊆ Q) := by
  have hPc : P ⊆ Q ∪ E := by
    rw [hcover]
    intro z hz
    exact ((hsides.symm ▸ Or.inl hz : z ∈ U \ c)).2
  have hNc : N ⊆ Q ∪ E := by
    rw [hcover]
    intro z hz
    exact ((hsides.symm ▸ Or.inr hz : z ∈ U \ c)).2
  obtain ⟨q, hqU, hqQ⟩ := mem_closure_iff.mp hxQ U hU hxU
  obtain ⟨e, heU, heE⟩ := mem_closure_iff.mp hxE U hU hxU
  have hq : q ∈ P ∪ N := by
    rw [← hsides]
    exact ⟨hqU, (show q ∈ cᶜ from hcover ▸ Or.inl hqQ)⟩
  have he : e ∈ P ∪ N := by
    rw [← hsides]
    exact ⟨heU, (show e ∈ cᶜ from hcover ▸ Or.inr heE)⟩
  rcases hP.subset_or_subset hQ hE hdis hPc with hp | hp <;>
    rcases hN.subset_or_subset hQ hE hdis hNc with hn | hn
  · exact (disjoint_left.mp hdis (he.elim (fun h ↦ hp h) (fun h ↦ hn h)) heE).elim
  · exact Or.inl ⟨hp, hn⟩
  · exact Or.inr ⟨hp, hn⟩
  · exact (disjoint_left.mp hdis hqQ (hq.elim (fun h ↦ hp h) (fun h ↦ hn h))).elim

end HolomorphicAnosov

