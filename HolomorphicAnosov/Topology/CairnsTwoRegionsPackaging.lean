import HolomorphicAnosov.Topology.ConnectedComponentsTwoOpenRegions
import Mathlib.Analysis.Complex.Basic

/-! Packaging for the final component step in Cairns §5. -/

namespace HolomorphicAnosov

open Set

/-- Two disjoint connected open regions with common frontier and complementary
union are exactly the two complementary components; the bounded one has the
usual closure identity. -/
theorem cairns_two_regions_component_package
    {c Q E : Set ℂ}
    (hQ : IsConnected Q) (hE : IsConnected E)
    (hQo : IsOpen Q) (hEo : IsOpen E)
    (hQb : Bornology.IsBounded Q) (hEb : ¬ Bornology.IsBounded E)
    (hcover : Q ∪ E = cᶜ) (hdisj : Disjoint Q E)
    (hQfront : frontier Q = c) (hEfront : frontier E = c) :
    Q.Nonempty ∧ E.Nonempty ∧ Q ≠ E ∧
      Q ∪ E = cᶜ ∧ Disjoint Q E ∧
      (fun z : ℂ ↦ connectedComponentIn cᶜ z) '' cᶜ = {Q, E} ∧
      closure Q = Q ∪ c := by
  have hne : Q ≠ E := by
    intro heq
    exact hEb (heq ▸ hQb)
  have hcover' : Q ∪ E = (frontier E)ᶜ := by
    rw [hEfront]
    exact hcover
  have hcomponents :
      (fun z : ℂ ↦ connectedComponentIn cᶜ z) '' cᶜ = {Q, E} := by
    calc
      (fun z : ℂ ↦ connectedComponentIn cᶜ z) '' cᶜ =
          (fun z : ℂ ↦ connectedComponentIn (frontier E)ᶜ z) '' (frontier E)ᶜ := by
            rw [hEfront]
      _ = {Q, E} := by
        rw [← hcover']
        exact connectedComponentsIn_two_open_regions hQ hE hQo hEo hdisj
  exact ⟨hQ.nonempty, hE.nonempty, hne, hcover, hdisj, hcomponents,
    by rw [closure_eq_self_union_frontier, hQfront]⟩

end HolomorphicAnosov

