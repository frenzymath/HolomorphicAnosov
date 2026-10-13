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

namespace HolomorphicAnosov

universe u v

/-- Fixedness and endpoint properties of the selected-cell stage in Hatcher's
Proposition 0.16, p.15. Every point has an original closed-cell representative.
On active representatives the local deformation stays in the same closed cell,
starts at the identity, and fixes the bottom. A representative lying in `B` or
the lower skeleton is on its sphere, so it too is fixed. At the endpoint the
radial image is on the bottom or sphere, and the characteristic sphere maps into
the lower skeleton. Inactive representatives are already in `B` or a lower cell.
This concerns one stage only; it does not concatenate stages or assert HEP. -/
theorem cw_selected_cell_stage_properties
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) :
    let S := Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)
    ∃ H : C(unitInterval × (unitInterval × (S : Set X)), unitInterval × X),
      (∀ (s t : unitInterval) (x : (S : Set X)), (H (s, (t, x))).2 ∈ (S : Set X)) ∧
      (∀ (t : unitInterval) (x : (S : Set X)), H (0, (t, x)) = (t, x.val)) ∧
      (∀ (s : unitInterval) (x : (S : Set X)), H (s, (0, x)) = (0, x.val)) ∧
      (∀ (s t : unitInterval) (x : (S : Set X)),
        x.val ∈ (B : Set X) ∨ x.val ∈
          (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) →
        H (s, (t, x)) = (t, x.val)) ∧
      (∀ (t : unitInterval) (x : (S : Set X)), H (1, (t, x)) ∈
        (({0} : Set unitInterval) ×ˢ (S : Set X)) ∪
          ((Set.univ : Set unitInterval) ×ˢ
            ((Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) ∪
              ((B : Set X) ∩ (S : Set X))))) := by
  classical
  let S := Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)
  change ∃ H : C(unitInterval × (unitInterval × (S : Set X)), unitInterval × X), _
  obtain ⟨H, hH⟩ := cw_selected_cell_stage B n
  let χ (m : ℕ) (i : S.I m) (z : Metric.closedBall (0 : Fin m → ℝ) 1) :
      (S : Set X) := ⟨Topology.RelCWComplex.map m i.val z.val,
        S.closedCell_subset_of_mem i.property ⟨z.val, z.property, rfl⟩⟩
  have hrep (x : (S : Set X)) : ∃ (m : ℕ) (i : S.I m)
      (z : Metric.closedBall (0 : Fin m → ℝ) 1), χ m i z = x := by
    have hx : x.val ∈ ⋃ (m : ℕ) (i : S.I m),
        Topology.CWComplex.closedCell m i.val := by
      rw [Topology.CWComplex.Subcomplex.union_closedCell S]
      exact x.property
    obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
    exact ⟨m, i, ⟨z, hz⟩, Subtype.ext hzx⟩
  have hdim (m : ℕ) (i : S.I m) : m ≤ n := by
    have hi := i.property
    change i.val ∈ (Topology.RelCWComplex.skeletonLT
      (Set.univ : Set X) ((n : ℕ∞) + 1)).I m at hi
    have hi : (m : ℕ∞) < (n : ℕ∞) + 1 := by
      simpa only [Topology.RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] using hi
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt] at hi
    exact Nat.lt_succ_iff.mp hi
  have hstay (s t : unitInterval) (x : (S : Set X)) :
      (H (s, (t, x))).2 ∈ (S : Set X) := by
    obtain ⟨m, i, z, rfl⟩ := hrep x
    by_cases hi : m = n ∧ i.val ∉ B.I m
    · rw [(hH m i s t z).1 hi]
      exact S.closedCell_subset_of_mem i.property
        ⟨(cw_prism_deform (s, (z, t))).1.val,
          (cw_prism_deform (s, (z, t))).1.property, rfl⟩
    · rw [(hH m i s t z).2 hi]
      exact (χ m i z).property
  refine ⟨H, hstay, ?_, ?_, ?_, ?_⟩
  · intro t x
    obtain ⟨m, i, z, rfl⟩ := hrep x
    by_cases hi : m = n ∧ i.val ∉ B.I m
    · rw [(hH m i 0 t z).1 hi, cw_prism_deform_zero]
    · exact (hH m i 0 t z).2 hi
  · intro s x
    obtain ⟨m, i, z, rfl⟩ := hrep x
    by_cases hi : m = n ∧ i.val ∉ B.I m
    · rw [(hH m i s 0 z).1 hi, cw_prism_deform_bottom]
    · exact (hH m i s 0 z).2 hi
  · intro s t x hfixed
    obtain ⟨m, i, z, rfl⟩ := hrep x
    by_cases hi : m = n ∧ i.val ∉ B.I m
    · have hz : ‖z.val‖ = 1 := by
        rcases hfixed with hB | hlower
        · exact cw_cell_in_subcomplex_is_boundary B m i.val hi.2 z hB
        · change Topology.RelCWComplex.map m i.val z.val ∈
            (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X)
            at hlower
          rw [← hi.1] at hlower
          exact cw_cell_in_lower_skeleton_is_boundary m i.val z hlower
      rw [(hH m i s t z).1 hi, cw_prism_deform_side s z t hz]
    · exact (hH m i s t z).2 hi
  · intro t x
    have hrange := hstay 1 t x
    obtain ⟨m, i, z, rfl⟩ := hrep x
    by_cases hi : m = n ∧ i.val ∉ B.I m
    · have he := (hH m i 1 t z).1 hi
      rw [cw_prism_deform_one] at he
      rw [he] at hrange ⊢
      rcases cw_prism_radial_in_bottom_or_side (z, t) with hbottom | hside
      · exact Or.inl ⟨hbottom, hrange⟩
      · refine Or.inr ⟨Set.mem_univ _, Or.inl ?_⟩
        apply Topology.CWComplex.skeletonLT_mono
          (show (m : ℕ∞) ≤ (n : ℕ∞) by exact_mod_cast hi.1.le)
        apply Topology.CWComplex.cellFrontier_subset_skeletonLT m i.val
        exact ⟨(cw_prism_radial (z, t)).1.val,
          by simpa only [Metric.mem_sphere, dist_zero_right] using hside, rfl⟩
    · rw [(hH m i 1 t z).2 hi] at hrange ⊢
      refine Or.inr ⟨Set.mem_univ _, ?_⟩
      by_cases hm : m = n
      · have hiB : i.val ∈ B.I m := by
          by_contra hnot
          exact hi ⟨hm, hnot⟩
        exact Or.inr ⟨B.closedCell_subset_of_mem hiB ⟨z.val, z.property, rfl⟩, hrange⟩
      · have hmn : m < n := lt_of_le_of_ne (hdim m i) hm
        refine Or.inl ?_
        apply Topology.CWComplex.skeletonLT_mono
          (show (m : ℕ∞) + 1 ≤ (n : ℕ∞) by exact_mod_cast Nat.succ_le_of_lt hmn)
        exact Topology.CWComplex.closedCell_subset_skeletonLT m i.val
          ⟨z.val, z.property, rfl⟩

end HolomorphicAnosov
