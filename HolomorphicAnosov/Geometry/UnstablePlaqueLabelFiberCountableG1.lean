import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import Mathlib.Topology.Bases

/-!
In a fixed foliation box, a separable intrinsic unstable leaf contains at most countably many
plaques. (HPS, §7, pp. 115–116) -/

namespace HolomorphicAnosov
open Set _root_.Topology TopologicalSpace
open scoped Topology
universe u v

/-- In a fixed foliation box, the set of transverse labels whose unstable plaques belong to a given
separable intrinsic leaf is countable. -/
theorem unstable_plaque_label_fiber_countable_g1 {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (q : Quotient F.unstablePartition) :
    letI := F.unstableTopology q
    SeparableSpace (IntrinsicFoliationLeaf F.unstablePartition q) →
      {w : FoliationCoordinateDisk s | F.unstableLabel b w = q}.Countable := by
  let := F.unstableTopology q
  intro hsep
  let := hsep
  let W := {w : FoliationCoordinateDisk s | F.unstableLabel b w = q}
  let plaque (w : W) (z : FoliationCoordinateDisk t) :
      IntrinsicFoliationLeaf F.unstablePartition q :=
    ⟨((F.box b).chart (w.val, z)).val, (F.unstable_label b w.val z).trans w.property⟩
  have hopen (w : W) : IsOpen (range (plaque w)) := by
    have hgeneral : ∀ (q₀ : Quotient F.unstablePartition) (hw : F.unstableLabel b w.val = q₀),
        letI := F.unstableTopology q₀
        IsOpenEmbedding (fun z : FoliationCoordinateDisk t ↦
          (⟨((F.box b).chart (w.val, z)).val, (F.unstable_label b w.val z).trans hw⟩ :
            IntrinsicFoliationLeaf F.unstablePartition q₀)) := by
      intro q₀ hw
      subst q₀
      exact F.unstable_plaque b w.val
    have h : IsOpenEmbedding (plaque w) := hgeneral q w.property
    exact h.isOpen_range
  have hne (w : W) : (range (plaque w)).Nonempty := by
    exact ⟨plaque w ⟨0, by simp⟩, mem_range_self _⟩
  have hd : Pairwise (fun w w' : W ↦ Disjoint (range (plaque w)) (range (plaque w'))) := by
    intro w w' hww'
    rw [disjoint_left]
    rintro y ⟨z, rfl⟩ ⟨z', heq⟩
    apply hww'
    have hp : (F.box b).chart (w'.val, z') = (F.box b).chart (w.val, z) := by
      apply Subtype.ext
      exact congrArg (fun r : IntrinsicFoliationLeaf F.unstablePartition q ↦ r.val) heq
    exact Subtype.ext (congrArg Prod.fst ((F.box b).chart.injective hp)).symm
  exact hd.countable_of_isOpen_disjoint hopen hne

end HolomorphicAnosov

