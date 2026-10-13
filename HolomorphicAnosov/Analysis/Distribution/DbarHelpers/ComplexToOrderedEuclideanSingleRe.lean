import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanIm
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanRe
import Mathlib.Analysis.Distribution.TestFunction

/-!
# complexToOrderedEuclidean_single_re

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_complex_to_ordered_euclidean_single_re_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The real unit vector in complex coordinate j maps to the Euclidean unit vector in the first block
at j.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: Use coordinate extensionality and the sum-index equivalence. In the first
block the real-coordinate formula is one at j and zero elsewhere; the imaginary block is zero.
These are the native Euclidean unit-vector coordinates.
-/
theorem complexToOrderedEuclidean_single_re (n : ℕ) (j : Fin n) :
    complexToOrderedEuclidean n (Pi.single j 1) =
      EuclideanSpace.single (finSumFinEquiv (Sum.inl j)) 1 := by
  ext k
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  rcases k with k | k
  · rw [complexToOrderedEuclidean_re]
    by_cases h : k = j
    · subst k; simp
    · simp [h]
  · rw [complexToOrderedEuclidean_im]
    have hn : k.addNat n ≠ Fin.castAdd n j := by
      intro he; have := congrArg Fin.val he; simp at this; omega
    simp [Pi.single_apply, hn, apply_ite]


end HolomorphicAnosov.Analysis.Distribution
