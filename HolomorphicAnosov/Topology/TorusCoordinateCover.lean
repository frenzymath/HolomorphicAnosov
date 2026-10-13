import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Coordinate quotient cover of the real torus

The coordinatewise quotient from real coordinate space to the period-one real torus
is an additive quotient covering map.  Its kernel is the finite integer lattice.
-/

namespace HolomorphicAnosov.Topology

noncomputable section
open scoped _root_.Topology

/-- The exact coordinatewise real quotient projection, as an additive homomorphism. -/
def coordinateProjection (n : ℕ) : (Fin n → ℝ) →+ UnitAddTorus (Fin n) where
  toFun v i := (v i : UnitAddCircle)
  map_zero' := by ext; simp
  map_add' v w := by ext; simp

/-- Exact native coordinate quotient cover; the discrete kernel is the actual integer lattice.

Source: Hatcher, *Algebraic Topology*, Theorem 1.7 and proof, pp.29–31;
Proposition 1.12 and Example 1.13, p.34. The implementation uses the same
Mathlib discrete-kernel proof as the original `TorusStandardWinding` helper:
the coordinate quotient is open, its kernel is the integer span of the standard
basis, and that span is discrete. The general quotient-homomorphism theorem
then gives the additive quotient covering. This also applies to the empty
coordinate space when `n = 0`.
-/
theorem coordinateProjection_cover (n : ℕ) :
    IsAddQuotientCoveringMap (coordinateProjection n) (coordinateProjection n).ker := by
  have hopen : IsOpenQuotientMap (coordinateProjection n) :=
    IsOpenQuotientMap.piMap (fun _ : Fin n ↦
      (QuotientAddGroup.isOpenQuotientMap_mk :
        IsOpenQuotientMap (fun x : ℝ ↦ (x : UnitAddCircle))))
  have hker : (coordinateProjection n).ker =
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup := by
    ext v
    change coordinateProjection n v = 0 ↔
      v ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))
    rw [(Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ v]
    rw [funext_iff]
    change (∀ i, (v i : UnitAddCircle) = 0) ↔
      ∀ i, ((Pi.basisFun ℝ (Fin n)).repr v) i ∈ Set.range (algebraMap ℤ ℝ)
    simp [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  have hd : DiscreteTopology (coordinateProjection n).ker := by
    rw [hker]
    exact ZSpan.discreteTopology_pi_basisFun
  exact hopen.isQuotientMap
    |>.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hd.isDiscrete


end
end HolomorphicAnosov.Topology
