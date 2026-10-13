import HolomorphicAnosov.Topology.CWGraphCollapsePresentation
namespace HolomorphicAnosov
open _root_.Topology
/-- Quotient presentation data used by compact weak-wedge loop extraction.
This projects the quotient map, root-fibre, and interior uniqueness clauses of
the proved CW graph collapse presentation.
Source: Hatcher, Algebraic Topology, graph quotient p.83 and Proposition 1A.2
pp.84--85.
-/
theorem graph_spanning_tree_loop_quotient_presentation_data_g3
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)]
    (hdim : ∀ n : ℕ, 1 < n → IsEmpty (RelCWComplex.cell (Set.univ : Set X) n))
    (T : RelCWComplex.Subcomplex (Set.univ : Set X))
    (hT0 : T.I 0 = Set.univ) (a : (T : Set X)) :
    let E := {e : RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1}
    let D := Metric.closedBall (0 : Fin 1 → ℝ) 1
    let π : Unit ⊕ (Σ _ : E, D) → GoodPair.Collapsed (T : Set X) :=
      Sum.elim (fun _ => GoodPair.collapse (T : Set X) a.val)
        (fun p => GoodPair.collapse (T : Set X) (RelCWComplex.map 1 p.1.val p.2.val))
    IsQuotientMap π ∧
      (∀ (e : E) (z : D), π (.inr ⟨e, z⟩) = π (.inl Unit.unit) ↔ ‖z.val‖ = 1) ∧
      (∀ (e f : E) (z w : D), ‖z.val‖ < 1 → ‖w.val‖ < 1 →
        (π (.inr ⟨e, z⟩) = π (.inr ⟨f, w⟩) ↔ e = f ∧ z = w)) := by
  dsimp
  obtain ⟨hπ, hfib, hinterior, _⟩ := cw_graph_collapse_presentation hdim T hT0 a
  exact ⟨hπ, hfib, hinterior⟩
end HolomorphicAnosov
