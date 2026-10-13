import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.QuotientRelativeHomotopyDescent

open Set
open scoped Topology _root_.Topology unitInterval
namespace HolomorphicAnosov.Topology

/-- An extended contraction preserving the collapsed subset and fixing its root
constructs an inverse to the collapse map up to homotopies fixing the basepoints.

Source: Hatcher, Proposition 0.17, pp.15–16. The endpoint is constant on the
collapsed subset, so it descends to r. The entire homotopy composed with the
collapse map descends because it preserves that subset. Its endpoints are the
identity and q∘r, and it fixes the collapsed point. The original homotopy has
endpoint r∘q and fixes the original root. All maps are literal quotient lifts.
No contraction or homotopy extension is inferred from these hypotheses. -/
theorem exists_based_collapse_homotopy_inverse
    {X : Type*} [TopologicalSpace X] (A : Set X) (a : X) (ha : a ∈ A)
    (endpoint : C(X, X))
    (H : ContinuousMap.HomotopyRel (ContinuousMap.id X) endpoint {a})
    (hpres : ∀ t x, x ∈ A → H (t, x) ∈ A)
    (hend : ∀ x ∈ A, endpoint x = a) :
    ∃ r : C(GoodPair.Collapsed A, X),
      r (GoodPair.collapse A a) = a ∧
      r.comp (GoodPair.collapse A) = endpoint ∧
      Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id X)
        (r.comp (GoodPair.collapse A)) {a}) ∧
      Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id (GoodPair.Collapsed A))
        ((GoodPair.collapse A).comp r) {GoodPair.collapse A a}) := by
  have hcompat : ∀ x y, (GoodPair.collapseSetoid A).r x y → endpoint x = endpoint y := by
    intro x y hxy
    rcases hxy with rfl | ⟨hx, hy⟩
    · rfl
    · rw [hend x hx, hend y hy]
  let r : C(GoodPair.Collapsed A, X) :=
    ⟨Quotient.lift endpoint hcompat, endpoint.continuous.quotient_lift hcompat⟩
  have hr : r.comp (GoodPair.collapse A) = endpoint := by
    ext x
    rfl
  refine ⟨r, hend a ha, hr, ?_, ?_⟩
  · rw [hr]
    exact ⟨H⟩
  · let Q := GoodPair.collapse A
    let K : C(unitInterval × X, GoodPair.Collapsed A) :=
      ⟨fun p => Q (H p), Q.continuous.comp H.continuous⟩
    obtain ⟨G, _⟩ := HolomorphicAnosov.exists_quotient_relative_homotopy
      Q (isQuotientMap_quotient_mk' (s := GoodPair.collapseSetoid A))
      (ContinuousMap.id (GoodPair.Collapsed A)) (Q.comp r) {Q a} K
      (fun x => by change Q (H (0,x)) = Q x; exact congrArg Q (H.apply_zero x))
      (fun x => by change Q (H (1,x)) = Q (endpoint x); exact congrArg Q (H.apply_one x))
      (by
        intro t x y hxy
        change Q (H (t,x)) = Q (H (t,y))
        rcases Quotient.eq.mp hxy with rfl | ⟨hx, hy⟩
        · rfl
        · exact Quotient.eq.mpr (Or.inr ⟨hpres t x hx, hpres t y hy⟩))
      (by
        intro t x hx
        change Q (H (t,x)) = Q x
        have hxA : x ∈ A := by
          have hxa : Q x = Q a := hx
          rcases Quotient.eq.mp hxa with h | h
          · exact h ▸ ha
          · exact h.1
        exact Quotient.eq.mpr (Or.inr ⟨hpres t x hxA, hxA⟩))
    exact ⟨G⟩

end HolomorphicAnosov.Topology
