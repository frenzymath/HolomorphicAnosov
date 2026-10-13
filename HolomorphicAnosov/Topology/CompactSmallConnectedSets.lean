import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Small compact connected sets joining nearby points

Conway, *Functions of One Complex Variable II*, Chapter 14, Definition 5.1 and Proposition 5.2, p.48, and Theorem 5.5,
p.50, uses small connected boundary sets between nearby endpoints. The following
compact locally connected metric-space lemma supplies this step, including coincident
endpoints. Its proof uses the connected neighborhood basis and the Lebesgue number lemma.
-/

open Set Metric Topology _root_.Topology

namespace HolomorphicAnosov.Topology

/-- In a compact locally connected metric space, sufficiently close pairs lie in
a common compact connected set of any prescribed positive diameter bound.

Proof: choose an open connected neighborhood of each point inside its radius
`ε / 2` ball. The Lebesgue number lemma gives one positive radius such that every
ball of that radius is contained in one chosen neighborhood. A pair closer than
that radius lies in its closure. This closure is compact and connected, and is
contained in a closed radius `ε / 2` ball, so its diameter is at most `ε`.
This expands the implication (c) → (a) of Conway Chapter 14, Proposition 5.2,
p.48, whose proof is left to the reader. Compactness follows on taking closures;
Theorem 5.5, p.50 uses the resulting small compact connected sets. -/
theorem compact_small_connected_sets
    {X : Type*} [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : X, dist x y < δ →
      ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ y ∈ K ∧ diam K ≤ ε := by
  have hnb (x : X) : ∃ V : Set X,
      V ⊆ ball x (ε / 2) ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance x _
      (ball_mem_nhds x (half_pos hε))
  choose V hVsub hVopen hxV hVconn using hnb
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric
    (s := (univ : Set X)) isCompact_univ hVopen
    (fun x _ ↦ mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨δ, hδ, fun x y hxy ↦ ?_⟩
  obtain ⟨z, hz⟩ := hcover x (mem_univ x)
  refine ⟨closure (V z), isClosed_closure.isCompact, (hVconn z).closure,
    subset_closure (hz (mem_ball_self hδ)),
    subset_closure (hz (by simpa [dist_comm] using hxy)), ?_⟩
  have hclosed : closure (V z) ⊆ closedBall z (ε / 2) :=
    closure_minimal ((hVsub z).trans ball_subset_closedBall) isClosed_closedBall
  simpa only [mul_div_cancel₀ ε (two_ne_zero : (2 : ℝ) ≠ 0)] using
    diam_le_of_subset_closedBall (half_pos hε).le hclosed

end HolomorphicAnosov.Topology
