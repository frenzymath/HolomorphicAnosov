import HolomorphicAnosov.Paper.Ghys.Proposition31

/-! This file records the intrinsic stable-leaf transport induced by the original Anosov map (Ghys, §2 and Prop. 3.1(i)). -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
  {f : Biholomorph d d M M} {a : AnosovDatum f}
  (P : AnosovIntrinsicFoliationPresentation f a)

/-- The original map transports each intrinsic stable leaf bijectively to the stable leaf through its image. -/
def stableLeafEquiv (x : M) :
    letI := P.realCharts
    IntrinsicFoliationLeaf P.foliations.stablePartition (Quotient.mk P.foliations.stablePartition x) ≃
      IntrinsicFoliationLeaf P.foliations.stablePartition (Quotient.mk P.foliations.stablePartition (f x)) := by
  letI := P.realCharts
  refine Equiv.subtypeEquiv f.toEquiv ?_
  intro y
  change Quotient.mk P.foliations.stablePartition y =
      Quotient.mk P.foliations.stablePartition x ↔
    Quotient.mk P.foliations.stablePartition (f y) =
      Quotient.mk P.foliations.stablePartition (f x)
  rw [Quotient.eq, Quotient.eq]
  exact (P.stablePartition_map_iff y x).symm

/-- The stable transport sends `y` to the ambient point `f y`. -/
theorem stableLeafEquiv_apply_val (x : M) :
    letI := P.realCharts
    ∀ y : IntrinsicFoliationLeaf P.foliations.stablePartition (Quotient.mk P.foliations.stablePartition x),
      (stableLeafEquiv P x y).val = f y.val := by
  intro y
  rfl

/-- The inverse stable transport sends `y` to the ambient point `f.symm y`. -/
theorem stableLeafEquiv_symm_apply_val (x : M) :
    letI := P.realCharts
    ∀ y : IntrinsicFoliationLeaf P.foliations.stablePartition (Quotient.mk P.foliations.stablePartition (f x)),
      ((stableLeafEquiv P x).symm y).val = f.symm y.val := by
  intro y
  rfl

end HolomorphicAnosov.Ghys

