import HolomorphicAnosov.Topology.SimplyConnectedOfCoverConnectors

namespace HolomorphicAnosov

open Set

/-- Hatcher Lemma 1.15 for two open sets. Choose connecting paths in the
intersection whenever an endpoint belongs to both sets, and in its unique cover
member otherwise. The finite connector-cancellation theorem then applies. -/
theorem sphere_simply_connected_of_two_sets
    {X : Type*} [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hAsc : IsSimplyConnected A)
    (hBsc : IsSimplyConnected B) (hAB : IsPathConnected (A ∩ B))
    (hcover : A ∪ B = univ) : SimplyConnectedSpace X := by
  classical
  obtain ⟨b, hbA, hbB⟩ := hAB.nonempty
  have hr : ∀ x : X, ∃ r : Path b x,
      (x ∈ A → ∀ t, r t ∈ A) ∧ (x ∈ B → ∀ t, r t ∈ B) := by
    intro x
    by_cases hxA : x ∈ A
    · by_cases hxB : x ∈ B
      · obtain ⟨r, hr⟩ := hAB.joinedIn b ⟨hbA, hbB⟩ x ⟨hxA, hxB⟩
        exact ⟨r, fun _ t ↦ (hr t).1, fun _ t ↦ (hr t).2⟩
      · obtain ⟨r, hr⟩ := hAsc.isPathConnected.joinedIn b hbA x hxA
        exact ⟨r, fun _ ↦ hr, fun h ↦ (hxB h).elim⟩
    · have hxB : x ∈ B := (hcover ▸ (mem_univ x) : x ∈ A ∪ B).resolve_left hxA
      obtain ⟨r, hr⟩ := hBsc.isPathConnected.joinedIn b hbB x hxB
      exact ⟨r, fun h ↦ (hxA h).elim, fun _ ↦ hr⟩
  choose r hrA hrB using hr
  refine sphere_simply_connected_of_cover_connectors (fun i : Bool ↦ if i then A else B)
    (by intro i; cases i <;> assumption)
    (by intro i; cases i <;> assumption) ?_ b r ?_
  · intro x
    have hx : x ∈ A ∪ B := hcover ▸ mem_univ x
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · intro i x hx
    cases i
    · exact hrB x hx
    · exact hrA x hx

end HolomorphicAnosov

