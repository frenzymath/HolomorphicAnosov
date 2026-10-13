import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Complex.Basic

/-!
# The real continuous linear equivalence from complex n-tuples to a pair of real n-tuples lists
all real parts first and all imaginary parts second; its inverse combines the two real entries
into a complex number.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20, real and imaginary coordinates; block ordering uses native Mathlib finite-index equivalences. DAG node: `analysis.dbar_helper_complex_to_real_arrays_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The real continuous linear equivalence from complex n-tuples to a pair of real n-tuples lists all
real parts first and all imaginary parts second; its inverse combines the two real entries into a
complex number.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20, real and imaginary coordinates; block ordering uses native Mathlib finite-index equivalences.

Proof/construction: The coordinate formulas preserve real addition and scalar multiplication.
Combining real and imaginary parts gives both inverse identities; finite dimensionality supplies
continuity.
-/
noncomputable def complexToRealArrays (n : ℕ) :
    (Fin n → ℂ) ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z ↦ (fun j ↦ (z j).re, fun j ↦ (z j).im)
      invFun := fun p j ↦ ⟨p.1 j, p.2 j⟩
      left_inv := fun z ↦ by ext j; rfl
      right_inv := fun p ↦ by rfl
      map_add' := fun z w ↦ by rfl
      map_smul' := fun c z ↦ by ext j <;> simp }


end HolomorphicAnosov.Analysis.Distribution
