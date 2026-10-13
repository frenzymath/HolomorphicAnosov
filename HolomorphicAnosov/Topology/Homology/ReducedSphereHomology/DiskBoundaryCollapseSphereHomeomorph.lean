import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap_continuous
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap_norm
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap_fiber
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.PolarDiskMap_surjective

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The polar formula descends through the actual boundary-collapse setoid.
Its exact fibres and surjectivity give a compact-to-Hausdorff homeomorphism
onto the native successor sphere, without replacing the quotient topology. -/
def diskBoundaryCollapseSphereHomeomorph (k : ℕ) :
    let D := {x : EuclideanSpace ℝ (Fin (k + 1)) // ‖x‖ ≤ 1}
    let A : Set D := {x | ‖x.val‖ = 1}
    GoodPair.Collapsed A ≃ₜ {y : EuclideanSpace ℝ (Fin (k + 1 + 1)) // ‖y‖ = 1} := by
  let E := EuclideanSpace ℝ (Fin (k + 1))
  let D := {x : E // ‖x‖ ≤ 1}
  let A : Set D := {x | ‖x.val‖ = 1}
  let S := {y : EuclideanSpace ℝ (Fin (k + 1 + 1)) // ‖y‖ = 1}
  let f : D → S := fun x ↦ ⟨polarDiskMap (k + 1) x.val, polarDiskMap_norm _ _⟩
  have hf : Continuous f :=
    ((polarDiskMap_continuous _).comp continuous_subtype_val).subtype_mk _
  have hrel : ∀ a b : D, GoodPair.collapseSetoid A a b → f a = f b := by
    intro a b h
    apply Subtype.ext
    apply (polarDiskMap_fiber _ _ _ a.property b.property).mpr
    rcases h with h | ⟨ha, hb⟩
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr ⟨ha, hb⟩
  let g : GoodPair.Collapsed A → S := Quotient.lift f hrel
  have hg : Function.Bijective g := by
    constructor
    · intro a b
      refine Quotient.inductionOn₂ a b ?_
      intro a b h
      apply Quotient.sound
      have hh := (polarDiskMap_fiber _ _ _ a.property b.property).mp
        (congrArg Subtype.val h)
      rcases hh with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr h
    · intro y
      obtain ⟨x, hx, hxy⟩ := polarDiskMap_surjective k y.val y.property
      refine ⟨Quotient.mk _ ⟨x, hx⟩, ?_⟩
      exact Subtype.ext hxy
  have hD : IsCompact {x : E | ‖x‖ ≤ 1} := by
    have hB : Metric.closedBall (0 : E) 1 = {x : E | ‖x‖ ≤ 1} := by
      ext x
      change dist (x : EuclideanSpace ℝ (Fin (k + 1))) 0 ≤ 1 ↔ ‖x‖ ≤ 1
      rw [dist_eq_norm, sub_zero]
    exact hB ▸ isCompact_closedBall (0 : E) 1
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg)
    (hf.quotient_lift hrel)

end HolomorphicAnosov.Topology.Homology
