import HolomorphicAnosov.Topology.Homology.UniqueNonzeroLocalClass

/-!
# CanonicalNonzeroLocalFamily

DAG node: `topo.def_mod2_canonical_nonzero_local_family`.
Source: Hatcher, Algebraic Topology, pp.234–237; geometric chart constructions use
Mathlib open partial homeomorphisms and Euclidean balls.
-/

noncomputable section

namespace HolomorphicAnosov

universe u

open Set CategoryTheory HatcherCompactSupport

/-- Choice of the canonical nonzero element in every local mod-two group. 

Source: Hatcher, Algebraic Topology, pp.234–235, sections of the local homology covering and canonical mod-two orientation.
-/
def canonicalNonzeroLocalFamily {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ∀ x : M, HatcherCompactSupport.SupportHomology ({x} : Set M) n :=
  fun x ↦ (uniqueNonzeroLocalClass x).exists.choose

/-- The chosen local generator is nonzero, by its defining choice specification.
Source: Hatcher, Algebraic Topology, pp.234–235. -/
theorem canonicalNonzeroLocalFamily_ne_zero {n : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    canonicalNonzeroLocalFamily (n := n) x ≠ 0 :=
  (uniqueNonzeroLocalClass x).exists.choose_spec

end HolomorphicAnosov

