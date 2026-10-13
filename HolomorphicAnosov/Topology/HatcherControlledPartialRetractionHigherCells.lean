import HolomorphicAnosov.Topology.HatcherControlledPartialRetractionCellSelection
import HolomorphicAnosov.Topology.HatcherControlledPartialRetractionLocalControl

/-!
# Higher-cell stage of Hatcher's controlled partial retraction

DAG node: `topo.hatcher_controlled_partial_retraction_higher_cells_g2`.

This is the source-backed cell-selection/gluing stage isolated from the nearest-point
and centered-ball adapters in `HatcherControlledPartialRetraction`.  Hatcher,
*Algebraic Topology*, Theorem A.7, printed pp.525–526, constructs a downward-closed
subcomplex by extending each attaching sphere into the compact target with image
diameter controlled by the infimum of all extensions.  Local finiteness of the
closed cells makes the glued map continuous, and shrinking cells near the compact
set gives the displayed neighborhood estimate.  The extension theorem handles the
constant-boundary zero-diameter case separately.

The implementation is intentionally a named source-backed admission while the
higher-cell dependent CW gluing is formalized.  The parent theorem supplies the
same exact assumptions and invokes this declaration without changing its statement.
-/

namespace HolomorphicAnosov

/-- Higher-cell CW selection, controlled gluing, and neighborhood coverage in
Hatcher's Theorem A.7.  The proof is postponed at this abstraction boundary
because the selected dependent cell family and locally finite gluing still need
to be assembled from the existing dyadic CW provider. -/
theorem hatcher_controlled_partial_retraction_higher_cells
    (N : ℕ) (hN : 0 < N) (C : Set (EuclideanSpace ℝ (Fin N)))
    (hC : IsCompact C) (hne : C.Nonempty) (hsub : ¬ C.Subsingleton)
    (hlocal : ∀ (c : C) (O : Set C), IsOpen O → c ∈ O →
      ∃ V : Set C, IsOpen V ∧ c ∈ V ∧
        ∃ hVO : V ⊆ O, (ContinuousMap.inclusion hVO).Nullhomotopic) :
    ∃ (Z : Set (EuclideanSpace ℝ (Fin N))) (r : EuclideanSpace ℝ (Fin N) → C),
      ContinuousOn r Z ∧ (∀ c : C, r c = c) ∧
      ∀ c : C, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        Metric.ball c.val δ ⊆ Z ∪ C ∧
        ∀ z ∈ Z, dist z c.val < δ → dist (r z).val c.val < ε := by
  obtain ⟨Z, r, hcont, hfix, hopen⟩ :=
    hatcher_controlled_partial_retraction_cell_selection N hN C hC hne hsub hlocal
  refine ⟨Z, r, hcont, hfix, ?_⟩
  exact hatcher_controlled_partial_retraction_local_control N C Z r hcont hfix hopen


end HolomorphicAnosov
