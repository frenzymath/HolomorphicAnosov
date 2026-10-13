import HolomorphicAnosov.Topology.Cubical.FullSkeletonCarrier
import HolomorphicAnosov.Topology.Homology.ContractibleSingularHomology
import Mathlib.Analysis.Convex.Contractible

open CategoryTheory

namespace HolomorphicAnosov.Cubical

/-- The top-degree rational singular homology of the full cubical skeleton is zero.
Source: Hatcher Lemma 2.34 pp.137–138 and Corollary 2.11 pp.111–112.
The full skeleton is the outer closed cube. Its coordinate interval is convex
and nonempty, so its straight-line contraction makes it contractible. Apply
positive-degree homology vanishing, using the positive ambient dimension. -/
theorem top_skeleton_homology_subsingleton {N : ℕ} (hN : 1 ≤ N)
    (K : FiniteRectilinearSubdivision N) :
    Subsingleton ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) N).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (K.skeleton N))) : Type) := by
  rw [full_skeleton_eq_cube_carrier]
  have hc : Convex ℝ K.cube.carrier := convex_Icc _ _
  have hn : K.cube.carrier.Nonempty := ⟨K.cube.lower, le_rfl, K.cube.lower_le_upper⟩
  let : ContractibleSpace K.cube.carrier := hc.contractibleSpace hn
  exact ModuleCat.subsingleton_of_isZero
    (singular_homology_isZero_of_contractible (TopCat.of K.cube.carrier)
      (ModuleCat.of ℚ ℚ) N (by omega))

end HolomorphicAnosov.Cubical
