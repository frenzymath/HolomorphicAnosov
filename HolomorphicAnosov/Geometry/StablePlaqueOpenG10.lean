import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation

noncomputable section
open scoped ContDiff Manifold _root_.Topology
open Set Filter _root_.Topology
universe u v
namespace HolomorphicAnosov
/-- The intrinsic stable plaque charts cover each stable class by open embeddings (HPS, p. 116). -/
theorem stable_plaque_open_at_class_g10 {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (w : FoliationCoordinateDisk t)
    (q : Quotient F.stablePartition) (h : F.stableLabel b w = q) :
    letI := F.stableTopology q
    IsOpenEmbedding (fun z : FoliationCoordinateDisk s ↦
      (⟨((F.box b).chart (z,w)).val, (F.stable_label b z w).trans h⟩ :
        IntrinsicFoliationLeaf F.stablePartition q)) := by
  subst q
  exact F.stable_plaque b w



end HolomorphicAnosov
end
