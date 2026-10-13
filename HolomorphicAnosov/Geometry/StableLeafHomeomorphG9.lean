import HolomorphicAnosov.Geometry.StableLeafTransportG9
import HolomorphicAnosov.Geometry.ContinuousStableLeafLiftG9

/-! The stable-leaf transport induced by the Anosov map is a homeomorphism for the intrinsic stable-leaf topologies (Ghys, §2 and Prop. 3.1(i)). -/

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

/-- The original map restricts to a homeomorphism between corresponding intrinsic stable leaves. -/
theorem stableLeafHomeomorph_g9 :
    letI := P.realCharts
    ∀ x : M,
    let q := Quotient.mk P.foliations.stablePartition x
    let q' := Quotient.mk P.foliations.stablePartition (f x)
    letI := P.foliations.stableTopology q
    letI := P.foliations.stableTopology q'
    ∃ es : IntrinsicFoliationLeaf P.foliations.stablePartition q ≃ₜ
      IntrinsicFoliationLeaf P.foliations.stablePartition q',
      ∀ y, (es y).val = f y.val := by
  let := P.realCharts
  intro x
  dsimp only
  let q := Quotient.mk P.foliations.stablePartition x
  let q' := Quotient.mk P.foliations.stablePartition (f x)
  let := P.foliations.stableTopology q
  let := P.foliations.stableTopology q'
  let := P.foliations.stableCharts q
  let := P.foliations.stableCharts q'
  let := P.stableSmooth q
  let := P.stableSmooth q'
  let := (P.stableNative q).countable
  let := (P.stableNative q').countable
  let : LocallyConnectedSpace (IntrinsicFoliationLeaf P.foliations.stablePartition q) :=
    ChartedSpace.locallyConnectedSpace (Fin (2*d-2) → ℝ) _
  let : LocallyConnectedSpace (IntrinsicFoliationLeaf P.foliations.stablePartition q') :=
    ChartedSpace.locallyConnectedSpace (Fin (2*d-2) → ℝ) _
  let e := stableLeafEquiv P x
  have he : Continuous e := continuous_stable_leaf_lift_g9 P.foliations q' inferInstance e
    (f.continuous.comp (P.foliations.stable_inclusion q))
  have hei : Continuous e.symm := continuous_stable_leaf_lift_g9 P.foliations q inferInstance e.symm
    (f.symm.continuous.comp (P.foliations.stable_inclusion q'))
  exact ⟨{ e with continuous_toFun := he, continuous_invFun := hei }, fun _ ↦ rfl⟩

end HolomorphicAnosov.Ghys

