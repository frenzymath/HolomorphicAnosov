import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import Mathlib.Topology.Bases

/-! Only countably many plaques in a fixed box belong to a given separable intrinsic leaf.
(Hirsch–Pugh–Shub, §7, pp.115–116) -/

namespace HolomorphicAnosov
open Set _root_.Topology TopologicalSpace
open scoped Topology
universe u v

/-- In a fixed box, the transverse labels of stable plaques belonging to one separable intrinsic
leaf form a countable set. -/
theorem stable_plaque_label_fiber_countable_g9 {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (q : Quotient F.stablePartition) :
    letI := F.stableTopology q
    SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q) →
      {w : FoliationCoordinateDisk t | F.stableLabel b w = q}.Countable := by
  let := F.stableTopology q
  intro hsep
  let := hsep
  let W := {w : FoliationCoordinateDisk t | F.stableLabel b w = q}
  let plaque (w : W) (z : FoliationCoordinateDisk s) :
      IntrinsicFoliationLeaf F.stablePartition q :=
    ⟨((F.box b).chart (z, w.val)).val, (F.stable_label b z w.val).trans w.property⟩
  have hopen (w : W) : IsOpen (range (plaque w)) := by
    have hgeneral : ∀ (q₀ : Quotient F.stablePartition) (hw : F.stableLabel b w.val = q₀),
        letI := F.stableTopology q₀
        IsOpenEmbedding (fun z : FoliationCoordinateDisk s ↦
          (⟨((F.box b).chart (z, w.val)).val, (F.stable_label b z w.val).trans hw⟩ :
            IntrinsicFoliationLeaf F.stablePartition q₀)) := by
      intro q₀ hw
      subst q₀
      exact F.stable_plaque b w.val
    have h : IsOpenEmbedding (plaque w) := hgeneral q w.property
    exact h.isOpen_range
  have hne (w : W) : (range (plaque w)).Nonempty := by
    exact ⟨plaque w ⟨0, by simp⟩, mem_range_self _⟩
  have hd : Pairwise (fun w w' : W ↦ Disjoint (range (plaque w)) (range (plaque w'))) := by
    intro w w' hww'
    rw [disjoint_left]
    rintro y ⟨z, rfl⟩ ⟨z', heq⟩
    apply hww'
    have hp : (F.box b).chart (z', w'.val) = (F.box b).chart (z, w.val) := by
      apply Subtype.ext
      exact congrArg (fun r : IntrinsicFoliationLeaf F.stablePartition q ↦ r.val) heq
    exact Subtype.ext (congrArg Prod.snd ((F.box b).chart.injective hp)).symm
  exact hd.countable_of_isOpen_disjoint hopen hne

end HolomorphicAnosov

