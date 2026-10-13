import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic
import HolomorphicAnosov.Topology.CWComplex.PairExtensionOfRetraction
import HolomorphicAnosov.Topology.CWComplex.RadialScaleBounds
import HolomorphicAnosov.Topology.CWComplex.RadialHeightBounds
import HolomorphicAnosov.Topology.CWComplex.RadialNormBound
import HolomorphicAnosov.Topology.CWComplex.RadialProjection
import HolomorphicAnosov.Topology.CWComplex.ContinuousRadialProjection
import HolomorphicAnosov.Topology.CWComplex.RadialBottom
import HolomorphicAnosov.Topology.CWComplex.RadialSide
import HolomorphicAnosov.Topology.CWComplex.RadialBoundaryTarget
import HolomorphicAnosov.Topology.CWComplex.RadialCharacteristicFrontier
import HolomorphicAnosov.Topology.CWComplex.RadialCharacteristicTarget
import HolomorphicAnosov.Topology.CWComplex.CompatibleSkeleta
import HolomorphicAnosov.Topology.CWComplex.SubtypeGlueCharacteristicDoublePrisms
import HolomorphicAnosov.Topology.CWComplex.CellBoundaryNeSameDimInterior
import HolomorphicAnosov.Topology.CWComplex.RadialSameDimCompatible
import HolomorphicAnosov.Topology.CWComplex.PrismDeformation
import HolomorphicAnosov.Topology.CWComplex.ContinuousPrismDeformation
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationZero
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationOne
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationFixed
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationBottom
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationSide
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationSameDimCompatible
import HolomorphicAnosov.Topology.CWComplex.CellInLowerSkeletonBoundary
import HolomorphicAnosov.Topology.CWComplex.CellInSubcomplexBoundary
import HolomorphicAnosov.Topology.CWComplex.PrismDeformationLowerCellCompatible
import HolomorphicAnosov.Topology.CWComplex.SelectedCellStage
import HolomorphicAnosov.Topology.CWComplex.SelectedCellStageProperties
import HolomorphicAnosov.Topology.CWComplex.GlueTwoClosed
import HolomorphicAnosov.Topology.CWComplex.ExtendLowerRetraction
import HolomorphicAnosov.Topology.CWComplex.RetractionSkeletalStep

namespace HolomorphicAnosov

universe u v

/-- Compatible endpoint retractions on all finite skeleta, obtained by the
cell-by-cell construction of Hatcher's Proposition 0.16, p.15. Start with the
unique map on the empty negative skeleton and apply the selected-cell step for
the zero skeleton. Dependent natural-number recursion then chooses each next
extension of the actual preceding map. Thus adjacent compatibility is retained;
induction gives compatibility for every pair of nested skeleta. -/
theorem cw_compatible_skeletal_retractions
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set X)) :
    ∃ R : ∀ n : ℕ, C(unitInterval ×
        (Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X),
        {p : unitInterval × X | p.1 = 0 ∨ p.2 ∈ (B : Set X)}),
      (∀ n x, (R n (0, x)).val = (0, x.val)) ∧
      (∀ n t x, x.val ∈ (B : Set X) → (R n (t, x)).val = (t, x.val)) ∧
      (∀ (m n : ℕ) (hmn : m ≤ n) (t : unitInterval)
        (x : (Topology.CWComplex.skeleton (Set.univ : Set X) (m : ℕ∞) : Set X)),
        R m (t, x) = R n (t, ⟨x.val, Topology.CWComplex.skeleton_mono
          (by exact_mod_cast hmn) x.property⟩)) := by
  classical
  let C₀ : Set (unitInterval × X) := {p | p.1 = 0 ∨ p.2 ∈ (B : Set X)}
  let S : ℕ → Set X := fun n ↦
    Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)
  let L₀ : Set X := Topology.CWComplex.skeletonLT (Set.univ : Set X) 0
  have hempty (x : L₀) : False := by
    have hx := x.property
    change x.val ∈ (Topology.CWComplex.skeletonLT (Set.univ : Set X) 0 : Set X) at hx
    rw [Topology.CWComplex.skeletonLT_zero_eq_empty] at hx
    exact hx
  let emptyRetraction : C(unitInterval × L₀, C₀) :=
    ⟨fun q ↦ (hempty q.2).elim, by
      rw [continuous_iff_continuousAt]
      intro q
      exact (hempty q.2).elim⟩
  obtain ⟨R₀, hR₀bottom, hR₀side, _⟩ := cw_retraction_skeletal_step B 0 emptyRetraction
    (fun x ↦ (hempty x).elim) (fun _ x _ ↦ (hempty x).elim)
  let Stage (n : ℕ) := {R : C(unitInterval × S n, C₀) //
    (∀ x, (R (0, x)).val = (0, x.val)) ∧
    (∀ t x, x.val ∈ (B : Set X) → (R (t, x)).val = (t, x.val))}
  have hnext (n : ℕ) (R : Stage n) : ∃ T : Stage (n + 1),
      ∀ (t : unitInterval) (x : S n) (hx : x.val ∈ S (n + 1)),
        T.val (t, ⟨x.val, hx⟩) = R.val (t, x) := by
    have hstep := cw_retraction_skeletal_step B (n + 1)
    have hSk : (Topology.CWComplex.skeletonLT (Set.univ : Set X)
        ((n + 1 : ℕ) : ℕ∞) : Set X) = S n := by
      simp only [S, Topology.RelCWComplex.skeleton, Nat.cast_add, Nat.cast_one]
    rw [hSk] at hstep
    obtain ⟨T, hTbottom, hTside, hTcompat⟩ := hstep R.val R.property.1 R.property.2
    exact ⟨⟨T, hTbottom, hTside⟩, hTcompat⟩
  let next : ∀ n, Stage n → Stage (n + 1) := fun n R ↦ (hnext n R).choose
  let stages : ∀ n, Stage n := Nat.rec ⟨R₀, hR₀bottom, hR₀side⟩ next
  have hmono (m n : ℕ) (hmn : m ≤ n) : S m ⊆ S n :=
    Topology.CWComplex.skeleton_mono (by exact_mod_cast hmn)
  have hsucc (n : ℕ) (t : unitInterval) (x : S n) :
      (stages (n + 1)).val
          (t, ⟨x.val, hmono n (n + 1) (Nat.le_succ n) x.property⟩) =
        (stages n).val (t, x) := by
    exact (hnext n (stages n)).choose_spec t x _
  have hcompat : ∀ (m n : ℕ) (hmn : m ≤ n) (t : unitInterval) (x : S m),
      (stages n).val (t, ⟨x.val, hmono m n hmn x.property⟩) =
        (stages m).val (t, x) := by
    intro m n
    induction n with
    | zero =>
      intro hmn t x
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      rfl
    | succ n ih =>
      intro hmn t x
      by_cases hmn' : m ≤ n
      · exact (hsucc n t ⟨x.val, hmono m n hmn' x.property⟩).trans (ih hmn' t x)
      · have hm : m = n + 1 := by omega
        subst m
        rfl
  refine ⟨fun n ↦ (stages n).val, ?_, ?_, ?_⟩
  · intro n
    exact (stages n).property.1
  · intro n
    exact (stages n).property.2
  · intro m n hmn t x
    exact (hcompat m n hmn t x).symm

end HolomorphicAnosov
