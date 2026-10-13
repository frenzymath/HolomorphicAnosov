import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.LowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarDeformationZero
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarDeformationOne
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.ContinuousSkeletonCollarDeformation

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For every finite Hausdorff CW space and degree m, its skeleton collar strongly deformation retracts onto its lower skeleton: there is a continuous retraction and a homotopy inside the collar from its identity to inclusion followed by retraction, fixing the lower skeleton throughout.

Proof: The lower skeleton is contained in the collar and is fixed at all times. Every other point has a characteristic collar representative, whose deformed representative still lies in its disk collar, so the deformation remains in the target collar. Evaluate the jointly continuous formula at time one and restrict its codomain to the lower skeleton to obtain the continuous retraction. Restrict the full deformation codomain to the collar, giving the required homotopy. The endpoint laws and pointwise fixation supply its identity, retraction and relative conditions.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem skeletonCollar_strongDeformationRetraction
    [CWComplex.Finite (univ : Set X)] (m : ℕ) :
    ∃ hAU : lowerSkeleton X m ⊆ skeletonCollar X m,
      ∃ r : C(↥(skeletonCollar X m), ↥(lowerSkeleton X m)),
        (∀ a : ↥(lowerSkeleton X m), r ⟨a.1, hAU a.2⟩ = a) ∧
        Nonempty ((ContinuousMap.id ↥(skeletonCollar X m)).HomotopyRel
          ((ContinuousMap.inclusion hAU).comp r)
          {x : ↥(skeletonCollar X m) | x.1 ∈ lowerSkeleton X m}) := by
  classical
  have hAU : lowerSkeleton X m ⊆ skeletonCollar X m := fun _ h ↦ Or.inl h
  have hfixed (t : unitInterval) (x : ↥(skeletonCollar X m))
      (hx : x.1 ∈ lowerSkeleton X m) : skeletonCollarDeformation X m t x = x.1 := by
    simp only [skeletonCollarDeformation, dite_eq_left hx]
  have hmem (t : unitInterval) (x : ↥(skeletonCollar X m)) :
      skeletonCollarDeformation X m t x ∈ skeletonCollar X m := by
    by_cases hx : x.1 ∈ lowerSkeleton X m
    · rw [hfixed t x hx]
      exact hAU hx
    · let z := Classical.choose (x.2.resolve_left hx)
      simp only [skeletonCollarDeformation, dite_eq_right hx]
      exact Or.inr ⟨⟨z.1, collarDeformation m (t, z.2)⟩, rfl⟩
  let r : C(↥(skeletonCollar X m), ↥(lowerSkeleton X m)) :=
    ⟨fun x ↦ ⟨skeletonCollarDeformation X m 1 x, skeletonCollarDeformation_one X m x⟩,
      ((continuous_skeletonCollarDeformation X m).comp
        (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  refine ⟨hAU, r, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    exact hfixed 1 ⟨a.1, hAU a.2⟩ a.2
  · refine ⟨{ toFun := fun tx ↦ ⟨skeletonCollarDeformation X m tx.1 tx.2,
          hmem tx.1 tx.2⟩
              continuous_toFun := (continuous_skeletonCollarDeformation X m).subtype_mk _
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro x
      apply Subtype.ext
      exact skeletonCollarDeformation_zero X m x
    · intro x
      rfl
    · intro t x hx
      apply Subtype.ext
      exact hfixed t x hx

end HolomorphicAnosov.CharacteristicCellComparison
