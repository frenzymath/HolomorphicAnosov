import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsRefinement

/-- The literal successor map restricts to each radial patch once it agrees
with the old map on the old carrier and distinct closed patches overlap only
there. Outside the old carrier the patch containing the point is unique,
so the choice made in `StepData.next` selects exactly that patch.
Source: Cairns §4(C), affine compatibility on old chords. -/
theorem cairns_successor_map_eq_patch
    {σ : Circle → ℂ} {a : Set ℂ} {s : Stage}
    (d : StepData σ a s) (h : range σ ≃ₜ Circle)
    (hoverlap : ∀ i j, i ≠ j →
      closure (d.star i).sourceStar ∩ closure (d.star j).sourceStar ⊆
        closure s.region ∪ range σ)
    (hagrees : ∀ i z, z ∈ closure (d.star i).sourceStar →
      z ∈ closure s.region ∪ range σ → s.map z = (d.star i).patchMap h z) :
    ∀ i z, z ∈ closure (d.star i).sourceStar →
      (d.next h).map z = (d.star i).patchMap h z := by
  classical
  intro i z hz
  by_cases hold : z ∈ closure s.region ∪ range σ
  · change (if z ∈ closure s.region ∪ range σ then s.map z else _) = _
    rw [ite_eq_left hold]
    exact hagrees i z hz hold
  · have hex : ∃ j, z ∈ closure (d.star j).sourceStar := ⟨i,hz⟩
    have heq : Classical.choose hex = i := by
      by_contra hne
      exact hold (hoverlap _ _ hne ⟨Classical.choose_spec hex,hz⟩)
    cases heq
    simp only [StepData.next, ite_eq_right hold, dite_eq_left hex]

end HolomorphicAnosov.Topology.Plane

