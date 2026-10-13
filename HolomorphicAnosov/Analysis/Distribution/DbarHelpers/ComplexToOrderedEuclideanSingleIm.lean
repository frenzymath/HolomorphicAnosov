import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanIm
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanRe
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.Constructions.SumProd

/-!
# complexToOrderedEuclidean_single_im

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_complex_to_ordered_euclidean_single_im_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The imaginary unit vector in complex coordinate j maps to the Euclidean unit vector in the second
block at j.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: Use coordinate extensionality and the sum-index equivalence. The first block
is zero and the imaginary-coordinate formula in the second block is one at j and zero elsewhere.
-/
theorem complexToOrderedEuclidean_single_im (n : ℕ) (j : Fin n) :
    complexToOrderedEuclidean n (Pi.single j Complex.I) =
      EuclideanSpace.single (finSumFinEquiv (Sum.inr j)) 1 := by
  ext k
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with k | k
  · rw [complexToOrderedEuclidean_re]
    have hn : Fin.castAdd n k ≠ j.addNat n := by
      intro he; have := congrArg Fin.val he; simp at this; omega
    simp [Pi.single_apply, hn, apply_ite]
  · rw [complexToOrderedEuclidean_im]
    by_cases h : k = j
    · subst k; simp
    · simp [h]


end HolomorphicAnosov.Analysis.Distribution
