import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation

noncomputable section
open scoped ContDiff Manifold _root_.Topology
open Set Filter _root_.Topology
universe u v
namespace HolomorphicAnosov
/-- An unstable plaque chart is an open embedding into the intrinsic leaf specified by an equal
class label. (HPS, p. 116) -/
theorem unstable_plaque_open_at_class_g10 {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (z : FoliationCoordinateDisk s)
    (q : Quotient F.unstablePartition) (h : F.unstableLabel b z = q) :
    letI := F.unstableTopology q
    IsOpenEmbedding (fun w : FoliationCoordinateDisk t ↦
      (⟨((F.box b).chart (z,w)).val, (F.unstable_label b z w).trans h⟩ :
        IntrinsicFoliationLeaf F.unstablePartition q)) := by
  subst q
  exact F.unstable_plaque b z



end HolomorphicAnosov
end
