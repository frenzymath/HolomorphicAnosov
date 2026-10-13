import HolomorphicAnosov.Topology.DoldGradedTraceContraction
import HolomorphicAnosov.Topology.FiniteFixedPointIndexSum
import HolomorphicAnosov.Topology.FunctorialTraceConjugacy
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Trace

/-!
# Dold's signed tensor / geometric trace bridge

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts* (1965), equations (3.2)--(3.4), pp.4--5.  The signed dual tensor
attached to the degree-k homology endomorphism contracts to its alternating
trace.  This algebraic bridge is separated from Dold's geometric diagonal and
support-operator calculation.

DAG node: `topo.dold_geometric_trace_bridge_g10`.
-/

noncomputable section
open CategoryTheory TensorProduct
open scoped TensorProduct BigOperators
namespace HolomorphicAnosov.FixedPointIndexInterface
universe u

/-- The signed tensor contraction equals the alternating graded trace.

The finite-dimensional hypotheses are retained degreewise.  The source proof
uses the canonical tensor/dual linear equivalence, the sign
`(-1)^(k*k)`, and the parity identity `k+k*k` even.  The geometric support
operator is deliberately absent from this bridge; it is the separate Dold
obligation in the parent theorem.
-/
theorem dold_geometric_trace_bridge
    {Y : Type u} [TopologicalSpace Y]
    (d : ℕ)
    (H : ℕ → TopCat.{u} ⥤ ModuleCat.{u} ℚ)
    (g : C(Y, Y))
    (hH : ∀ k, FiniteDimensional ℚ ((H k).obj (TopCat.of Y) : Type u))
    (a : ∀ k, Module.Dual ℚ ((H k).obj (TopCat.of Y) : Type u) ⊗[ℚ]
      ((H k).obj (TopCat.of Y) : Type u))
    (ha : ∀ k, a k = (-1 : ℚ)^(k*k) •
      (dualTensorHomEquiv ℚ ((H k).obj (TopCat.of Y) : Type u)
        ((H k).obj (TopCat.of Y) : Type u)).symm
        ((H k).map (TopCat.ofHom g)).hom) :
    (∑ k ∈ Finset.range (d + 1),
      contractLeft ℚ ((H k).obj (TopCat.of Y) : Type u) (a k)) =
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℚ)^k * LinearMap.trace ℚ ((H k).obj (TopCat.of Y) : Type u)
          ((H k).map (TopCat.ofHom g)).hom := by
  have h := dold_alternating_trace_eq_contraction_sum
    (V := fun k ↦ ((H k).obj (TopCat.of Y) : Type u))
    (s := Finset.range (d + 1)) a
    (fun k ↦ ((H k).map (TopCat.ofHom g)).hom) (fun k hk ↦ by
      rw [ha k]
      simp only [map_smul]
      rw [smul_smul, ← pow_add]
      have heven : Even (k * k + (k * k)) := by
        exact ⟨k * k, by omega⟩
      rw [heven.neg_one_pow]
      simp)
  exact h.symm

end HolomorphicAnosov.FixedPointIndexInterface
