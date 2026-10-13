import HolomorphicAnosov.Topology.ManningBowenInitialCoverUniformSaturation
import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData

namespace HolomorphicAnosov.Dynamics.Bowen

open Set

/-- Bowen's passage from an open bracket-closed itinerary set to its closed
rectangle, used at the end of Lemma 23 (1970), p.738. The closure pair set stays
inside the given closed bracket domain, so continuity there suffices; no global
continuity of the totalized bracket is asserted. -/
theorem bracket_closed_closure
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData f γ lam)
    {V : Set X}
    (hcore : ∀ x ∈ closure V, ∀ y ∈ closure V, dist x y ≤ H.closeRadius)
    (hV : ∀ x ∈ V, ∀ y ∈ V, H.bracket x y ∈ V) :
    ∀ x ∈ closure V, ∀ y ∈ closure V, H.bracket x y ∈ closure V := by
  have hc : ContinuousOn (fun p : X × X ↦ H.bracket p.1 p.2) (closure (V ×ˢ V)) := by
    apply H.bracket_continuous.mono
    rw [closure_prod_eq]
    intro p hp
    exact hcore p.1 hp.1 p.2 hp.2
  have hm : MapsTo (fun p : X × X ↦ H.bracket p.1 p.2) (V ×ˢ V) V :=
    fun p hp ↦ hV p.1 hp.1 p.2 hp.2
  have hmc := hm.closure_of_continuousWithinAt (fun p hp ↦ (hc p hp).mono subset_closure)
  intro x hx y hy
  apply hmc (x := (x, y))
  rw [closure_prod_eq]
  exact ⟨hx, hy⟩

end HolomorphicAnosov.Dynamics.Bowen
