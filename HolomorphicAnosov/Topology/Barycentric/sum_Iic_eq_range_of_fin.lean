import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Module

/-!
# Reindexing a barycentric prefix sum

DAG node: `topo.barycentric_sum_iic_eq_range_of_fin_g16`.
Source: Hatcher, *Algebraic Topology*, Proposition 2.21(1), pp.119–121,
and Exercise 24, p.133, for the barycentric-subdivision context. The displayed
identity is auxiliary finite-sum algebra, using Mathlib's finite interval
image and sum reindexing identities. The exact declaration and construction
are retained from the current canonical module.
-/

namespace HolomorphicAnosov.BarycentricGeometry

open Set

universe u

/-- The sum over the prefix interval of a finite tuple equals the natural-index
prefix sum of its extension by zero. Source: auxiliary finite-sum algebra in
the barycentric-subdivision construction of Hatcher, Proposition 2.21(1),
pp.119–121, and Exercise 24, p.133; `Fin.map_valEmbedding_Iic` and
`Nat.range_succ_eq_Iic` provide the exact index-set identification in Mathlib.

Complete proof: extend w to a natural-indexed function z, using w at indices
less than m and zero elsewhere. At every finite index j, z(j.val)=w(j).
Reindex the sum over Iic k along the injective map `Fin.valEmbedding`.
Its image is the natural interval Iic k.val, which is the range of k.val+1.
Unfold z to obtain the displayed dependent conditional. The case k=0 gives
the first entry alone. If m=0 no k exists, so no extra nonemptiness premise is
required. The original real-module hypotheses and arbitrary universe remain.
-/
theorem sum_Iic_eq_range_of_fin
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} (w : Fin m → E) (k : Fin m) :
    (∑ j ∈ Finset.Iic k, w j) =
      ∑ j ∈ Finset.range (k.val + 1),
        if h : j < m then w ⟨j, h⟩ else 0 := by
  let z : ℕ → E := fun j ↦ if h : j < m then w ⟨j, h⟩ else 0
  calc
    (∑ j ∈ Finset.Iic k, w j) = ∑ j ∈ Finset.Iic k, z j.val := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [z]
    _ = ∑ j ∈ (Finset.Iic k).map Fin.valEmbedding, z j := by
      simp [Finset.sum_map, Fin.valEmbedding]
    _ = ∑ j ∈ Finset.range (k.val + 1), z j := by
      rw [Fin.map_valEmbedding_Iic, Nat.range_succ_eq_Iic]
    _ = _ := rfl

end HolomorphicAnosov.BarycentricGeometry

