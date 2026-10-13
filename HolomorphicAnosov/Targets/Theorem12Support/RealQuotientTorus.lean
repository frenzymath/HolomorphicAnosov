import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! The coordinate lattice quotient is homeomorphic to the product of unit circles. Coordinate
reduction intertwines real integer-matrix actions with integral toral maps. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Function Set
namespace HolomorphicAnosov.Theorem12RealQuotientTorus

/-- The integer span of the standard basis of `Fin n → ℝ`. -/
abbrev coordinateLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

/-- The additive map reducing each real coordinate modulo one. -/
def coordinateProjection (n : ℕ) : (Fin n → ℝ) →+ UnitAddTorus (Fin n) where
  toFun v i := (v i : UnitAddCircle)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Coordinate reduction modulo one is an open quotient map. -/
theorem coordinateProjection_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (coordinateProjection n) :=
  IsOpenQuotientMap.piMap (fun _ : Fin n ↦
    (QuotientAddGroup.isOpenQuotientMap_mk :
      IsOpenQuotientMap (fun x : ℝ ↦ (x : UnitAddCircle))))

/-- The kernel of coordinate reduction is the integer span of the standard basis. -/
theorem coordinateProjection_ker (n : ℕ) :
    (coordinateProjection n).ker = (coordinateLattice n).toAddSubgroup := by
  ext v
  change coordinateProjection n v = 0 ↔ v ∈ coordinateLattice n
  rw [(Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ v]
  rw [funext_iff]
  change (∀ i, (v i : UnitAddCircle) = 0) ↔
    ∀ i, ((Pi.basisFun ℝ (Fin n)).repr v) i ∈ Set.range (algebraMap ℤ ℝ)
  simp [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]

/-- The additive map from the coordinate lattice quotient to the product of unit circles induced by
coordinate reduction. -/
def quotientProjection (n : ℕ) :
    (Fin n → ℝ) ⧸ (coordinateLattice n).toAddSubgroup →+ UnitAddTorus (Fin n) :=
  QuotientAddGroup.lift (coordinateLattice n).toAddSubgroup (coordinateProjection n)
    (le_of_eq (coordinateProjection_ker n).symm)

@[simp] theorem quotientProjection_mk (n : ℕ) (v : Fin n → ℝ) :
    quotientProjection n (QuotientAddGroup.mk v) = coordinateProjection n v := rfl

/-- The induced coordinate reduction on the lattice quotient is injective. -/
theorem quotientProjection_injective (n : ℕ) : Injective (quotientProjection n) := by
  intro x y
  induction x using QuotientAddGroup.induction_on with
  | H v =>
    induction y using QuotientAddGroup.induction_on with
    | H w =>
      intro heq
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      rw [← coordinateProjection_ker]
      exact (coordinateProjection n).mem_ker.mpr (by simpa using sub_eq_zero.mpr heq)

/-- The induced coordinate reduction on the lattice quotient is surjective. -/
theorem quotientProjection_surjective (n : ℕ) : Surjective (quotientProjection n) := by
  intro x
  obtain ⟨v, hv⟩ := (coordinateProjection_isOpenQuotientMap n).surjective x
  exact ⟨QuotientAddGroup.mk v, hv⟩

/-- The induced coordinate reduction on the lattice quotient is continuous. -/
theorem quotientProjection_continuous (n : ℕ) : Continuous (quotientProjection n) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coordinateLattice n).toAddSubgroup).continuous_iff.mpr
  exact (coordinateProjection_isOpenQuotientMap n).continuous

/-- The induced coordinate reduction on the lattice quotient is open. -/
theorem quotientProjection_isOpenMap (n : ℕ) : IsOpenMap (quotientProjection n) :=
  IsOpenMap.of_comp QuotientAddGroup.continuous_mk QuotientAddGroup.mk_surjective
    (coordinateProjection_isOpenQuotientMap n).isOpenMap

/-- The homeomorphism from the coordinate lattice quotient to the product of unit circles induced by
coordinate reduction. -/
def quotientTorusHomeomorph (n : ℕ) :
    ((Fin n → ℝ) ⧸ (coordinateLattice n).toAddSubgroup) ≃ₜ UnitAddTorus (Fin n) :=
  (Equiv.ofBijective (quotientProjection n)
    ⟨quotientProjection_injective n, quotientProjection_surjective n⟩).toHomeomorphOfContinuousOpen
      (quotientProjection_continuous n) (quotientProjection_isOpenMap n)

@[simp] theorem quotientTorusHomeomorph_mk (n : ℕ) (v : Fin n → ℝ) :
    quotientTorusHomeomorph n (QuotientAddGroup.mk v) = fun i ↦ (v i : UnitAddCircle) := rfl

/-- The real matrix obtained by casting the entries of an invertible integer matrix. -/
def realMatrix {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j ↦ (A i j : ℝ)

/-- Coordinate reduction intertwines multiplication by the real matrix with the integral toral map. -/
theorem coordinateProjection_mulVec {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) (v : Fin n → ℝ) :
    coordinateProjection n ((realMatrix A).mulVecLin v) =
      integralToralMap A (coordinateProjection n v) := by
  ext i
  change ((∑ j : Fin n, (A i j : ℝ) * v j : ℝ) : UnitAddCircle) =
    ∑ j : Fin n, A i j • (v j : UnitAddCircle)
  change (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
    (∑ j : Fin n, (A i j : ℝ) * v j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show (A i j : ℝ) * v j = A i j • v j by simp [zsmul_eq_mul]]
  exact QuotientAddGroup.mk_zsmul (AddSubgroup.zmultiples (1 : ℝ)) (v j) (A i j)

/-- The quotient torus homeomorphism intertwines the real integer-matrix action on representatives
with the integral toral map. -/
theorem quotientTorusHomeomorph_matrix {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ) (v : Fin n → ℝ) :
    quotientTorusHomeomorph n (QuotientAddGroup.mk ((realMatrix A).mulVecLin v)) =
      integralToralMap A (quotientTorusHomeomorph n (QuotientAddGroup.mk v)) :=
  coordinateProjection_mulVec A v

end HolomorphicAnosov.Theorem12RealQuotientTorus
