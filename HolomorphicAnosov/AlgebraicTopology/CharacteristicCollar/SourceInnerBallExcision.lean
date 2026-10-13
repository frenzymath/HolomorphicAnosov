import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellDisk
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions
import HolomorphicAnosov.Topology.SingularHomologyExcision.SourceEquivOfSmall
import Mathlib.Topology.CWComplex.Classical.Basic

/-! Hatcher, Algebraic Topology, Proposition 2.21 and excision pp.123–124,
used on the characteristic disk-union cover of Proposition 3.17 p.217.
The forward map is the literal inclusion of the inner-ball intersection pair.
No relative cohomology excision theorem is used. -/

open CategoryTheory Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison

/-- The source-side inner-ball inclusion is a chain homotopy equivalence over
any commutative coefficient ring, also after ordinary product with any space.

Source: Hatcher pp.123–124 and p.217. The outer collars and inner balls are
open in the disjoint disk union and cover it because one half is less than
three quarters. Their product inverse images under the first projection have
the same properties. Apply the explicit native small-chain retraction and
its supported homotopy, then the intersection-to-small-quotient isomorphism
and the canonical subspace pair identifications. These constructions identify
the forward chain map exactly with the original topological pair inclusion.
The proof includes dimension zero, an empty cell family, and empty products. -/
theorem sourceInnerBall_chain_excision
    (X : Type u) [TopologicalSpace X] [CWComplex (univ : Set X)]
    (R : Type u) [CommRing R] (m : ℕ) :
    let D := Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m
    let A : Set D := {z | (1 / 2 : ℝ) < ‖z.2.down.1‖}
    let B : Set D := {z | ‖z.2.down.1‖ < (3 / 4 : ℝ)}
    (∃ e : HomotopyEquiv
        ((singularExcisionSource (TopCat.of D) A B).chainComplex (ModuleCat.of R R))
        ((singularSubspacePair (TopCat.of D) A).chainComplex (ModuleCat.of R R)),
      e.hom = SSetPair.chainComplexMap
        (singularExcisionInclusion (TopCat.of D) A B) (ModuleCat.of R R)) ∧
    ∀ (Y : Type u) (_ : TopologicalSpace Y),
      ∃ e : HomotopyEquiv
          ((singularExcisionSource (TopCat.of (D × Y))
            (Prod.fst ⁻¹' A) (Prod.fst ⁻¹' B)).chainComplex (ModuleCat.of R R))
          ((singularSubspacePair (TopCat.of (D × Y))
            (Prod.fst ⁻¹' A)).chainComplex (ModuleCat.of R R)),
        e.hom = SSetPair.chainComplexMap
          (singularExcisionInclusion (TopCat.of (D × Y))
            (Prod.fst ⁻¹' A) (Prod.fst ⁻¹' B)) (ModuleCat.of R R) := by
  dsimp only
  let D := Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m
  let A : Set D := {z | (1 / 2 : ℝ) < ‖z.2.down.1‖}
  let B : Set D := {z | ‖z.2.down.1‖ < (3 / 4 : ℝ)}
  have hA : IsOpen A := by
    rw [isOpen_sigma_iff]
    intro i
    exact isOpen_lt continuous_const ((continuous_subtype_val.comp continuous_uliftDown).norm)
  have hB : IsOpen B := by
    rw [isOpen_sigma_iff]
    intro i
    exact isOpen_lt ((continuous_subtype_val.comp continuous_uliftDown).norm) continuous_const
  have hAB : A ∪ B = univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases h : (1 / 2 : ℝ) < ‖z.2.down.1‖
    · exact Or.inl h
    · exact Or.inr (by dsimp [B]; linarith)
  have hcover : interior A ∪ interior B = univ := by
    rw [hA.interior_eq, hB.interior_eq, hAB]
  constructor
  · exact excision_source_equiv_of_small (TopCat.of D) A B (ModuleCat.of R R)
      (NativeBarycentricOperators.smallRelativeHomotopyEquiv
        (TopCat.of D) A B hcover (ModuleCat.of R R)) rfl
  · intro Y _
    have hprod : interior (Prod.fst ⁻¹' A : Set (D × Y)) ∪
        interior (Prod.fst ⁻¹' B) = univ := by
      rw [(hA.preimage continuous_fst).interior_eq,
        (hB.preimage continuous_fst).interior_eq, ← preimage_union, hAB, preimage_univ]
    exact excision_source_equiv_of_small (TopCat.of (D × Y))
      (Prod.fst ⁻¹' A) (Prod.fst ⁻¹' B) (ModuleCat.of R R)
      (NativeBarycentricOperators.smallRelativeHomotopyEquiv (TopCat.of (D × Y))
        (Prod.fst ⁻¹' A) (Prod.fst ⁻¹' B) hprod (ModuleCat.of R R)) rfl

end HolomorphicAnosov.CharacteristicCellComparison
