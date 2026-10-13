import HolomorphicAnosov.Analysis.Complex.FiniteComplexGridCover
import Mathlib.Topology.Separation.Regular

/-!
# Compact neighborhoods and the exposed grid boundary

Conway source input: Functions of One Complex Variable, second edition (1978),
VIII Proposition 1.1, pp.195–196, finite rectangular-grid selection and
shared-edge cancellation. The regular-closed neighborhood, arbitrary-open-U
and empty-K specialization, and exposed-cell formulation below are an
agent-written expansion using the Mathlib compact-neighborhood theorem.
-/

namespace HolomorphicAnosov.Analysis.Complex

open Set

/-- A compact set inside an open complex set has a compact regular closed
neighborhood covered by exactly the finite grid squares that meet it. A shared
point of a selected and an unselected closed cell is outside that neighborhood.
In particular, every exposed closed side, including its endpoints, avoids it.

Conway VIII Proposition 1.1 supplies the finite grid selection and
shared-edge cancellation. The following regular-closed neighborhood and
exposed-cell formulation is an agent-written expansion: choose an open
neighborhood V of K with compact closure contained in U. Put L = closure V.
Since V is open, V is contained in interior L; taking closures gives
L = closure (interior L). Apply the finite grid cover theorem to L. If a
point of L belonged to any unselected closed cell, that cell would meet L and
hence be selected, a contradiction. A shared point is in U because its
selected cell is in U. This argument includes empty K, arbitrary open U,
grid vertices, and all selected/unselected cell pairs; adjacency need not be
assumed. -/
theorem conway_regular_closed_grid_cover
    (U K : Set ℂ) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (L : Set ℂ) (δ : ℝ) (S : Finset (ℤ × ℤ)),
      IsCompact L ∧ K ⊆ interior L ∧ closure (interior L) = L ∧ L ⊆ U ∧
      0 < δ ∧
      (∀ q, q ∈ S ↔ ∃ z ∈ L, z ∈ complexGridSquare δ q) ∧
      (∀ z ∈ L, ∃ q ∈ S, z ∈ complexGridSquare δ q) ∧
      (∀ q ∈ S, complexGridSquare δ q ⊆ U) ∧
      (∀ q ∈ S, ∀ r ∉ S,
        complexGridSquare δ q ∩ complexGridSquare δ r ⊆ U \ L) := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  have hVi : V ⊆ interior (closure V) :=
    hV.subset_interior_iff.mpr subset_closure
  have hregular : closure (interior (closure V)) = closure V :=
    subset_antisymm isClosed_closure.closure_interior_subset (closure_mono hVi)
  obtain ⟨δ, S, hδ, hselect, hcover, hinside⟩ :=
    exists_finite_complex_grid_cover U (closure V) hU hVc hVU
  refine ⟨closure V, δ, S, hVc, hKV.trans hVi, hregular, hVU,
    hδ, hselect, hcover, hinside, ?_⟩
  intro q hq r hr z hz
  exact ⟨hinside q hq hz.1, fun hzL ↦ hr ((hselect r).mpr ⟨z, hzL, hz.2⟩)⟩

end HolomorphicAnosov.Analysis.Complex
