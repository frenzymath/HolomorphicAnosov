import HolomorphicAnosov.Topology.Homology.ContractibleSingularHomology
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Positive connecting map for a closed ball

Hatcher, Algebraic Topology, Corollary 2.11 pp.112–113 and the relative exact
sequence pp.116–118. The closed ball contracts, so the two positive ambient
homology groups adjacent to the connecting map vanish.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Metric

namespace HolomorphicAnosov.Topology

/-- For any nonempty closed ball and any subspace of that ball, the actual
relative connecting map from degree q+2 to degree q+1 is an isomorphism, with
arbitrary module coefficients. In particular, the degree-two map for the boundary
of a plane disk is the disk-to-boundary comparison used by the degree calculation.

Source: Hatcher, Corollary 2.11 pp.112–113 and the pair exact sequence pp.116–118.
A nonnegative-radius closed ball contracts to its center by straight segments.
Its positive singular homology vanishes. The two ambient groups adjoining the
connecting map are in degrees q+2 and q+1, so exactness makes that map invertible.
The radius-zero singleton and empty subspace cases are included; there is no
claim about the map into ordinary degree-zero homology. -/
theorem closedBall_relative_connecting_isIso
    {R : Type} [Ring R] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) (r : ℝ) (hr : 0 ≤ r) (A : Set (closedBall c r))
    (M : ModuleCat R) (q : ℕ) :
    IsIso ((singularSubspacePair (TopCat.of (closedBall c r)) A).homologyδ
      M (q + 2) (q + 1)) := by
  let P := singularSubspacePair (TopCat.of (closedBall c r)) A
  let : ContractibleSpace (closedBall c r) := Metric.contractibleSpace_closedBall hr
  have hz (n : ℕ) (hn : n ≠ 0) :
      IsZero ((TopCat.toSSet.obj (TopCat.of (closedBall c r))).homology M n) :=
    singular_homology_isZero_of_contractible (TopCat.of (closedBall c r)) M n hn
  change IsIso ((P.shortExact_chainComplexShortComplex M).δ (q + 2) (q + 1) _)
  exact (P.shortExact_chainComplexShortComplex M).isIso_δ
    (q + 2) (q + 1) (by simp) (hz (q + 2) (by omega)) (hz (q + 1) (by omega))


end HolomorphicAnosov.Topology
