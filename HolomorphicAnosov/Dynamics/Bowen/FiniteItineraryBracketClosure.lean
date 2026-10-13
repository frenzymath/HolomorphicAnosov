import HolomorphicAnosov.Dynamics.Bowen.BracketFinitePrefixRadius
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.homeomorph_pow_apply
import HolomorphicAnosov.Dynamics.Bowen.BracketClosedClosure

namespace HolomorphicAnosov.Dynamics.Bowen
open Set
open HolomorphicAnosov.Bowen.RectangleSlicesPreparation

/-- The bracket part of Bowen's finite-itinerary refinement (Lemma 23, p.738).

There is one positive radius such that finite joins of smaller closed rectangles
are bracket closed, provided the interiors of the input rectangles are bracket
closed. This last hypothesis is the product-interior consequence of Bowen
Lemmas 8–9; it is explicit here and is not inferred from closed-set bracket
closure alone. The word length is positive so time zero bounds every pair in
the closure by the original bracket-continuity radius.

Proof: choose the common finite-prefix covariance radius. The closure of each
itinerary interior is contained in each closed itinerary constraint. Two points
in an itinerary interior therefore have close orbit pairs at every prefix time.
Covariance carries their bracket at each time to the bracket of the two orbit
points. Interior bracket closure puts that point back in the itinerary interior.
At time zero the closed constraint bounds every pair in its closure by the
original continuity radius. The continuous closed-domain bracket then preserves
the closure. Empty rectangles and empty itinerary sets cause no exception.
DAG node: `dynamics.bowen_finite_itinerary_bracket_closure_g17`. -/
theorem finiteItineraryBracketClosure
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData f γ lam) :
    ∃ r : ℝ, 0 < r ∧ r ≤ H.closeRadius ∧
      ∀ (N m : ℕ), 0 < m → ∀ P : Fin N → Set X,
        (∀ i, IsClosed (P i)) →
        (∀ i, ∀ x ∈ P i, ∀ y ∈ P i, dist x y ≤ r) →
        (∀ i, ∀ x ∈ interior (P i), ∀ y ∈ interior (P i),
          H.bracket x y ∈ interior (P i)) →
        ∀ w : Fin m → Fin N,
          let V := ⋂ k : Fin m, (⇑(f ^ k.val) : X → X) ⁻¹' interior (P (w k))
          ∀ x ∈ closure V, ∀ y ∈ closure V, H.bracket x y ∈ closure V := by
  obtain ⟨r, hr, hrcore, hcov⟩ := exists_bracket_finite_prefix_radius f γ lam H
  refine ⟨r, hr, hrcore, ?_⟩
  intro N m hm P hclosed hsmall hbracket w
  let V := ⋂ k : Fin m, (⇑(f ^ k.val) : X → X) ⁻¹' interior (P (w k))
  have hsubset (k : Fin m) : closure V ⊆ (⇑(f ^ k.val) : X → X) ⁻¹' P (w k) := by
    apply closure_minimal _ ((hclosed (w k)).preimage (f ^ k.val).continuous)
    intro x hx
    exact (interior_subset (s := P (w k))) (mem_iInter.mp hx k)
  apply bracket_closed_closure f γ lam H
  · intro x hx y hy
    have hx0 := hsubset ⟨0, hm⟩ hx
    have hy0 := hsubset ⟨0, hm⟩ hy
    exact (hsmall (w ⟨0, hm⟩) x hx0 y hy0).trans hrcore
  · intro x hx y hy
    apply mem_iInter.mpr
    intro k
    have hxy : ∀ j ≤ k.val,
        dist ((f : X → X)^[j] x) ((f : X → X)^[j] y) ≤ r := by
      intro j hj
      have hjm : j < m := hj.trans_lt k.isLt
      simpa only [homeomorph_pow_apply] using hsmall (w ⟨j, hjm⟩) _ (interior_subset (mem_iInter.mp hx ⟨j, hjm⟩))
        _ (interior_subset (mem_iInter.mp hy ⟨j, hjm⟩))
    change (f ^ k.val) (H.bracket x y) ∈ interior (P (w k))
    rw [homeomorph_pow_apply]
    rw [hcov k.val x y hxy]
    simpa only [homeomorph_pow_apply] using
      hbracket (w k) _ (mem_iInter.mp hx k) _ (mem_iInter.mp hy k)

end HolomorphicAnosov.Dynamics.Bowen
