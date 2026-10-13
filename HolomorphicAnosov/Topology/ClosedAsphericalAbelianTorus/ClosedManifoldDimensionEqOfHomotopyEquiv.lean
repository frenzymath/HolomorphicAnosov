import HolomorphicAnosov.Topology.Homology.ClosedManifoldMod2TopHomology
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.HomotopyEquivMod2HomologyIso
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

/-- Closed-manifold dimension is determined by the highest nonzero mod-two
singular homology degree. This applies also in dimension zero and does not
require orientability. Source: Hatcher 3.26 and the homotopy invariance above. -/
theorem closed_manifold_dimension_eq_of_homotopyEquiv
    (n r : ℕ) (M P : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    [TopologicalSpace P] [T2Space P] [SecondCountableTopology P]
    [ChartedSpace (EuclideanSpace ℝ (Fin r)) P]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin r))) ∞ P]
    [CompactSpace P] [ConnectedSpace P] [Nonempty P]
    (e : ContinuousMap.HomotopyEquiv M P) : n = r := by
  obtain ⟨hnonM, hzeroM⟩ := closed_manifold_mod2_top_homology n M
  obtain ⟨hnonP, hzeroP⟩ := closed_manifold_mod2_top_homology r P
  have hnle : n ≤ r := by
    by_contra hnr
    have := hzeroP n (Nat.lt_of_not_ge hnr)
    have := hnonM
    let E := (homotopyEquiv_mod2_homology_iso e n).toLinearEquiv
    have := E.toEquiv.injective.subsingleton
    exact not_nontrivial_iff_subsingleton.mpr this hnonM
  have hrle : r ≤ n := by
    by_contra hrn
    have := hzeroM r (Nat.lt_of_not_ge hrn)
    have := hnonP
    let E := (homotopyEquiv_mod2_homology_iso e.symm r).toLinearEquiv
    have := E.toEquiv.injective.subsingleton
    exact not_nontrivial_iff_subsingleton.mpr this hnonP
  exact Nat.le_antisymm hnle hrle

end HolomorphicAnosov
