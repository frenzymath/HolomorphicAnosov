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

namespace HolomorphicAnosov

universe u v

/-- The selected-cell stage of Hatcher's Proposition 0.16, p.15. On the original
`n`-skeleton, deform precisely the `n`-cells outside `B` and fix all other cells.
The two displayed formulas characterize the descended map into the ambient
cylinder; range and endpoint retraction properties are separate assertions.

For descent, two active representatives agree by same-dimensional compatibility.
An active representative meeting a lower cell is on its sphere. If it meets a
cell selected by `B`, disjointness of its open cell from `B` likewise puts it on
its sphere. The local deformation fixes that sphere in both cases. Identity
branches agree directly. The characteristic double-prism descent theorem then
supplies joint continuity without assuming boundary injectivity. -/
theorem cw_selected_cell_stage
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (n : ℕ) :
    let S := Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)
    ∃ H : C(unitInterval × (unitInterval × (S : Set X)), unitInterval × X),
      ∀ (m : ℕ) (i : S.I m) (s t : unitInterval)
        (z : Metric.closedBall (0 : Fin m → ℝ) 1),
        let x : (S : Set X) := ⟨Topology.RelCWComplex.map m i.val z.val,
          S.closedCell_subset_of_mem i.property ⟨z.val, z.property, rfl⟩⟩
        (m = n ∧ i.val ∉ B.I m →
          H (s, (t, x)) = ((cw_prism_deform (s, (z, t))).2,
            Topology.RelCWComplex.map m i.val (cw_prism_deform (s, (z, t))).1.val)) ∧
        (¬(m = n ∧ i.val ∉ B.I m) →
          H (s, (t, x)) = (t, Topology.RelCWComplex.map m i.val z.val)) := by
  classical
  let S := Topology.CWComplex.skeleton (Set.univ : Set X) (n : ℕ∞)
  change ∃ H : C(unitInterval × (unitInterval × (S : Set X)), unitInterval × X), _
  have hdim (m : ℕ) (i : S.I m) : m ≤ n := by
    have hi := i.property
    change i.val ∈ (Topology.RelCWComplex.skeletonLT
      (Set.univ : Set X) ((n : ℕ∞) + 1)).I m at hi
    have hi : (m : ℕ∞) < (n : ℕ∞) + 1 := by
      simpa only [Topology.RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] using hi
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt] at hi
    exact Nat.lt_succ_iff.mp hi
  let P (m : ℕ) (i : S.I m) :
      C(unitInterval × (unitInterval × Metric.closedBall (0 : Fin m → ℝ) 1),
        unitInterval × X) :=
    if m = n ∧ i.val ∉ B.I m then
      ⟨fun q ↦ ((cw_prism_deform (q.1, (q.2.2, q.2.1))).2,
          Topology.RelCWComplex.map m i.val
            (cw_prism_deform (q.1, (q.2.2, q.2.1))).1.val), by
        have hswap : Continuous (fun q : unitInterval ×
            (unitInterval × Metric.closedBall (0 : Fin m → ℝ) 1) ↦
            (q.1, (q.2.2, q.2.1))) :=
          continuous_fst.prodMk ((continuous_snd.comp continuous_snd).prodMk
            (continuous_fst.comp continuous_snd))
        have hr := continuous_cw_prism_deform.comp hswap
        exact (continuous_snd.comp hr).prodMk
          (((Topology.RelCWComplex.continuousOn m i.val).domRestrict).comp
            (continuous_fst.comp hr))⟩
    else
      ⟨fun q ↦ (q.2.1, Topology.RelCWComplex.map m i.val q.2.2.val),
        (continuous_fst.comp continuous_snd).prodMk
          (((Topology.RelCWComplex.continuousOn m i.val).domRestrict).comp
            (continuous_snd.comp continuous_snd))⟩
  have hactive_inactive
      (m l : ℕ) (i : S.I m) (j : S.I l)
      (s t : unitInterval)
      (z : Metric.closedBall (0 : Fin m → ℝ) 1)
      (w : Metric.closedBall (0 : Fin l → ℝ) 1)
      (hi : m = n ∧ i.val ∉ B.I m)
      (hj : ¬(l = n ∧ j.val ∉ B.I l))
      (heq : Topology.RelCWComplex.map m i.val z.val =
        Topology.RelCWComplex.map l j.val w.val) :
      ((cw_prism_deform (s, (z, t))).2,
        Topology.RelCWComplex.map m i.val (cw_prism_deform (s, (z, t))).1.val) =
      (t, Topology.RelCWComplex.map l j.val w.val) := by
    obtain ⟨hm, hi⟩ := hi
    subst m
    by_cases hl : l = n
    · subst l
      have hjB : j.val ∈ B.I n := by
        by_contra hnot
        exact hj ⟨rfl, hnot⟩
      have hzB : Topology.RelCWComplex.map n i.val z.val ∈ (B : Set X) := by
        rw [heq]
        exact B.closedCell_subset_of_mem hjB ⟨w.val, w.property, rfl⟩
      have hz := cw_cell_in_subcomplex_is_boundary B n i.val hi z hzB
      rw [cw_prism_deform_side s z t hz]
      exact Prod.ext rfl heq
    · have hln : l < n := lt_of_le_of_ne (hdim l j) hl
      have hcast : (l : ℕ∞) + 1 ≤ (n : ℕ∞) := by
        exact_mod_cast Nat.succ_le_of_lt hln
      have hzlower : Topology.RelCWComplex.map n i.val z.val ∈
          (Topology.CWComplex.skeletonLT (Set.univ : Set X) (n : ℕ∞) : Set X) := by
        rw [heq]
        exact Topology.CWComplex.skeletonLT_mono hcast
          (Topology.CWComplex.closedCell_subset_skeletonLT l j.val
            ⟨w.val, w.property, rfl⟩)
      exact congrArg Prod.swap
        (cw_prism_deform_lower_cell_compatible n l i.val j.val z w s t hzlower heq)
  have hcompat : ∀ (m : ℕ) (i : Topology.RelCWComplex.cell (S : Set X) m)
      (l : ℕ) (j : Topology.RelCWComplex.cell (S : Set X) l)
      (s t : unitInterval) (z : Metric.closedBall (0 : Fin m → ℝ) 1)
      (w : Metric.closedBall (0 : Fin l → ℝ) 1),
      Topology.RelCWComplex.map m i z.val = Topology.RelCWComplex.map l j w.val →
      P m i (s, (t, z)) = P l j (s, (t, w)) := by
    intro m i l j s t z w heq
    change Topology.RelCWComplex.map m i.val z.val =
      Topology.RelCWComplex.map l j.val w.val at heq
    by_cases hi : m = n ∧ i.val ∉ B.I m
    · by_cases hj : l = n ∧ j.val ∉ B.I l
      · simp only [P, ite_eq_left hi, ite_eq_left hj, ContinuousMap.coe_mk]
        have hml : m = l := hi.1.trans hj.1.symm
        subst l
        exact congrArg Prod.swap
          (cw_prism_deform_same_dim_compatible m i.val j.val z w s t heq)
      · simpa only [P, ite_eq_left hi, ite_eq_right hj, ContinuousMap.coe_mk] using
          hactive_inactive m l i j s t z w hi hj heq
    · by_cases hj : l = n ∧ j.val ∉ B.I l
      · simpa only [P, ite_eq_right hi, ite_eq_left hj, ContinuousMap.coe_mk] using
          (hactive_inactive l m j i s t w z hj hi heq.symm).symm
      · simp only [P, ite_eq_right hi, ite_eq_right hj, ContinuousMap.coe_mk]
        exact Prod.ext rfl heq
  obtain ⟨H, hH⟩ := cw_subtype_glue_characteristic_double_prisms (S : Set X) P hcompat
  refine ⟨H, ?_⟩
  intro m i s t z
  constructor
  · intro hi
    simpa only [P, ite_eq_left hi, ContinuousMap.coe_mk,
      Topology.CWComplex.Subcomplex.map_def] using hH m i s t z
  · intro hi
    simpa only [P, ite_eq_right hi, ContinuousMap.coe_mk,
      Topology.CWComplex.Subcomplex.map_def] using hH m i s t z

end HolomorphicAnosov
