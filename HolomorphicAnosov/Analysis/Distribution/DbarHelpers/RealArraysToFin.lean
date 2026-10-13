import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Complex.Basic

/-!
# The real continuous linear equivalence from a pair of real n-tuples to real 2n-tuples
concatenates the two blocks in the Fin-sum order.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20, real and imaginary coordinates; block ordering uses native Mathlib finite-index equivalences. DAG node: `analysis.dbar_helper_real_arrays_to_fin_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The real continuous linear equivalence from a pair of real n-tuples to real 2n-tuples concatenates
the two blocks in the Fin-sum order.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20, real and imaginary coordinates; block ordering uses native Mathlib finite-index equivalences.

Proof/construction: Compose the inverse of the native sum-indexed product equivalence with the
reindexing equivalence from Fin n plus Fin n to Fin (n+n).
-/
noncomputable def realArraysToFin (n : ℕ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) ≃L[ℝ] (Fin (n+n) → ℝ) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin n) (Fin n) (fun _ ↦ ℝ)).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (n+n) ↦ ℝ) finSumFinEquiv)


end HolomorphicAnosov.Analysis.Distribution
