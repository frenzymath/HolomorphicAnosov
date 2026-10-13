import Mathlib.Data.Finset.Sort
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateProjection
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.ZeroTorusProfile

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The zero-coordinate base of the native coordinate monomial induction.
This is the exact n=0 branch of the coordinate-basis target: the point profile
supplies the unit basis in degree zero and zero modules in positive degrees.
Source: Hatcher pp.197--201, with the native point profile above. -/
theorem coordinate_cup_monomial_basis_zero
    (a : SingularCochain.cycles ℚ
      (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1)
    (cup : ∀ p q : ℕ,
      SingularCochain.cohomology ℚ (TopCat.of (UnitAddTorus (Fin 0))) p →ₗ[ℚ]
      SingularCochain.cohomology ℚ (TopCat.of (UnitAddTorus (Fin 0))) q →ₗ[ℚ]
      SingularCochain.cohomology ℚ (TopCat.of (UnitAddTorus (Fin 0))) (p + q))
    (one : SingularCochain.cohomology ℚ (TopCat.of (UnitAddTorus (Fin 0))) 0)
    (hu : ∃ hu : SingularCochain.oneCochain ℚ
        (TopCat.of (UnitAddTorus (Fin 0))) ∈
        SingularCochain.cycles ℚ
          (SingularCochain.complex ℚ (TopCat.of (UnitAddTorus (Fin 0)))) 0,
      one = SingularCochain.cocycleClass ℚ
        (SingularCochain.complex ℚ (TopCat.of (UnitAddTorus (Fin 0)))) 0
        ⟨SingularCochain.oneCochain ℚ (TopCat.of (UnitAddTorus (Fin 0))), hu⟩) :
    let X : TopCat := TopCat.of (UnitAddTorus (Fin 0))
    let α := fun i : Fin 0 ↦
      (SingularCochain.cohomologyPullback ℚ
        (coordinateProjection 0 i) 1)
        (SingularCochain.cocycleClass ℚ
          (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a)
    let monomial : ∀ l : List (Fin 0),
        SingularCochain.cohomology ℚ X l.length :=
      fun l ↦ List.rec (motive := fun l ↦
        SingularCochain.cohomology ℚ X l.length) one
        (fun i l v ↦ cast (congrArg
          (fun d ↦ (SingularCochain.cohomology ℚ X d : Type))
          (Nat.add_comm 1 l.length))
          (cup 1 l.length (α i) v)) l
    ∀ k : ℕ,
      ∃ B : Module.Basis {S : Finset (Fin 0) // S.card = k} ℚ
          (SingularCochain.cohomology ℚ X k),
        ∀ S, B S = cast (congrArg
          (fun d ↦ (SingularCochain.cohomology ℚ X d : Type))
          ((S.val.length_sort (· ≤ ·)).trans S.property))
          (monomial (S.val.sort (· ≤ ·))) := by
  dsimp only
  intro k
  by_cases hk : k = 0
  · subst k
    obtain ⟨B, hB⟩ := (zero_torus_profile one hu).1
    refine ⟨B, ?_⟩
    intro S
    have hS : S.val = ∅ := by
      ext i
      exact Fin.elim0 i
    have hS' : S = ⟨∅, rfl⟩ := by
      apply Subtype.ext
      exact hS
    rw [hS']
    rw [hB]
    have hsort : (∅ : Finset (Fin 0)).sort (· ≤ ·) = [] := Finset.sort_empty _
    apply eq_of_heq
    apply HEq.trans ?_ (cast_heq _ _).symm
    rw [hsort]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hzero := (zero_torus_profile one hu).2 k hkpos
    have := hzero
    have : IsEmpty {S : Finset (Fin 0) // S.card = k} :=
      ⟨fun S ↦ by
        have hS : S.val = ∅ := by
          ext i
          exact Fin.elim0 i
        have hcard : (0 : ℕ) = k := by
          simpa [hS] using S.property
        exact hk hcard.symm⟩
    refine ⟨Module.Basis.empty _, ?_⟩
    intro S
    exact isEmptyElim S

end HolomorphicAnosov.TorusRationalCupBasisKronecker
