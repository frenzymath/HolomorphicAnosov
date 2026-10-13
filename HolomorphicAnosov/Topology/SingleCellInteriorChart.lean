import HolomorphicAnosov.Topology.PushoutSumQuotient
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open CategoryTheory CategoryTheory.Limits
open Topology _root_.Topology

namespace HolomorphicAnosov
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The open cell of a pushout attachment is Euclidean space, with the origin
corresponding to the disk centre. Source: the characteristic-map description
of a cell attachment used in Hatcher, Algebraic Topology, Proposition 1.26,
pp.50–51. The boundary range is the norm-one locus. Identify its complement
with the open unit ball, apply the standard ball homeomorphism, and then the
pushout complement homeomorphism. No separation property of X is used. -/
theorem single_cell_interior_chart
    {X Y : TopCat.{u}} (n : ℕ)
    (φ : TopCat.diskBoundary.{u} n ⟶ X)
    (f : X ⟶ Y) (χ : TopCat.disk.{u} n ⟶ Y)
    (hpush : IsPushout φ (TopCat.diskBoundaryInclusion.{u} n) f χ) :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃ₜ {y : Y // y ∉ Set.range f.hom},
      (e 0 : Y) = χ.hom (ULift.up ⟨0, by simp⟩) := by
  let E := EuclideanSpace ℝ (Fin n)
  let B := {b : TopCat.disk.{u} n // b ∉ Set.range (TopCat.diskBoundaryInclusion n).hom}
  have hboundary (b : TopCat.disk.{u} n) :
      b ∈ Set.range (TopCat.diskBoundaryInclusion n).hom ↔ ‖b.down.val‖ = 1 := by
    constructor
    · rintro ⟨a, rfl⟩
      change ‖a.down.val‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using a.down.property
    · intro hb
      refine ⟨ULift.up ⟨b.down.val, ?_⟩, ?_⟩
      · simpa only [Metric.mem_sphere, dist_zero_right] using hb
      · apply ULift.ext
        apply Subtype.ext
        rfl
  let j : Metric.ball (0 : E) 1 → B := fun v ↦
    ⟨ULift.up ⟨v.val, Metric.ball_subset_closedBall v.property⟩, by
      rw [hboundary]
      exact ne_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using v.property)⟩
  let inv : B → Metric.ball (0 : E) 1 := fun b ↦
    ⟨b.val.down.val, by
      rw [Metric.mem_ball, dist_zero_right]
      apply lt_of_le_of_ne
      · simpa only [Metric.mem_closedBall, dist_zero_right] using b.val.down.property
      · exact fun heq ↦ b.property ((hboundary b.val).mpr heq)⟩
  have hj : Continuous j := by
    apply Continuous.subtype_mk
    exact continuous_uliftUp.comp (continuous_subtype_val.subtype_mk _)
  have hi : Continuous inv := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_uliftDown.comp continuous_subtype_val)
  let eB : Metric.ball (0 : E) 1 ≃ₜ B :=
    { toFun := j
      invFun := inv
      left_inv := by intro v; rfl
      right_inv := by intro b; apply Subtype.ext; apply ULift.ext; apply Subtype.ext; rfl
      continuous_toFun := hj
      continuous_invFun := hi }
  have hclosed : IsClosed (Set.range (TopCat.diskBoundaryInclusion n).hom) := by
    let : T2Space (TopCat.disk n) := by
      change T2Space (ULift (Metric.closedBall (0 : E) 1))
      infer_instance
    exact (isCompact_range (TopCat.diskBoundaryInclusion n).hom.continuous).isClosed
  obtain ⟨eY, heY⟩ := pushout_complement_homeomorph hpush hclosed
  refine ⟨Homeomorph.unitBall.trans (eB.trans eY), ?_⟩
  change (eY (eB (Homeomorph.unitBall 0)) : Y) = _
  rw [heY]
  apply congrArg χ.hom
  apply ULift.ext
  apply Subtype.ext
  exact Homeomorph.coe_unitBall_apply_zero

/-- The open cell is simply connected, and its puncture at the centre is path
connected in dimension at least two. Source: the two-set argument of Hatcher,
Proposition 1.26 pp.50–51. Transport contractibility of Euclidean space and
path connectedness of its puncture through the pointed open-cell chart. -/
theorem single_cell_open_cover_topology
    {X Y : TopCat.{u}} (n : ℕ) (hn : 2 ≤ n)
    (φ : TopCat.diskBoundary.{u} n ⟶ X)
    (f : X ⟶ Y) (χ : TopCat.disk.{u} n ⟶ Y)
    (hpush : IsPushout φ (TopCat.diskBoundaryInclusion.{u} n) f χ) :
    IsSimplyConnected ((Set.range f.hom)ᶜ : Set Y) ∧
      IsPathConnected (({χ.hom (ULift.up ⟨0, by simp⟩)}ᶜ : Set Y) ∩
        (Set.range f.hom)ᶜ) := by
  obtain ⟨e, he⟩ := single_cell_interior_chart n φ f χ hpush
  refine ⟨?_, ?_⟩
  · let : SimplyConnectedSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
    change SimplyConnectedSpace {y : Y // y ∉ Set.range f.hom}
    exact (e.toHomotopyEquiv.simplyConnectedSpace_iff).mp inferInstance
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank]
    simpa using (show 1 < n by omega)
  have hpc := isPathConnected_compl_singleton_of_one_lt_rank hrank
    (0 : EuclideanSpace ℝ (Fin n))
  have himage := hpc.image (continuous_subtype_val.comp e.continuous)
  have heq : (fun v ↦ (e v : Y)) '' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) =
      ({χ.hom (ULift.up ⟨0, by simp⟩)}ᶜ : Set Y) ∩ (Set.range f.hom)ᶜ := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, (e v).property⟩
      intro hzero
      apply hv
      apply e.injective
      apply Subtype.ext
      exact hzero.trans he.symm
    · rintro ⟨hy0, hy⟩
      refine ⟨e.symm ⟨y, hy⟩, ?_, ?_⟩
      · intro heq
        have hval : (e (e.symm ⟨y, hy⟩) : Y) = y :=
          congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
        apply hy0
        change e.symm ⟨y, hy⟩ = 0 at heq
        rw [heq] at hval
        exact hval.symm.trans he
      · exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  have himage' : IsPathConnected ((fun v ↦ (e v : Y)) '' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) := by
    simpa only [Function.comp_apply] using himage
  rw [heq] at himage'
  exact himage'

end HolomorphicAnosov

