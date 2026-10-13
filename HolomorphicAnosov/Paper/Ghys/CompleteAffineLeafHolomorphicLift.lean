import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import HolomorphicAnosov.Paper.Ghys.InjectivePointedLeafLift
import HolomorphicAnosov.Paper.Ghys.HolomorphicOfLift

/-! This file proves the existence of pointed holomorphic lifts of complete intrinsic affine leaves
through holomorphic coverings. (Ghys, §5, pp. 597–598; Hatcher, Prop. 1.33) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff

namespace HolomorphicAnosov.Ghys

universe u v

attribute [local instance] complex_isManifold_real

/-- The inclusion of a complete intrinsic affine asymptotic leaf has an injective holomorphic lift
through a holomorphic covering, sending its marked point to a specified point of the fibre. (Ghys,
§5, pp. 597–598; Hatcher, Prop. 1.33) -/
theorem complete_affine_leaf_holomorphic_lift
    {S : Type u} [MetricSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (g : S ≃ₜ S) (P : RealTangentDistribution (realModel 2) S)
    {U : Type v} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    (p : U → S) (hp : IsCoveringMap p)
    (hpHol : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ p)
    (u : U) (L : NativeCompleteAffineAsymptoticLeaf g P (p u)) :
    let := L.native.topology
    let := L.complexCharts
    ∃ lift : StableAsymptoticLeaf g (p u) → U,
      ContMDiff (complexModel 1) (complexModel 2) ∞ lift ∧
      Function.Injective lift ∧ (∀ z, p (lift z) = z.val) ∧
      (∀ z, z.val = p u → lift z = u) := by
  let := L.native.topology
  let := L.complexCharts
  let := L.complexManifold
  let : SimplyConnectedSpace (StableAsymptoticLeaf g (p u)) := L.complete.1
  let : LocallyPathConnectedSpace (StableAsymptoticLeaf g (p u)) :=
    ChartedSpace.locallyPathConnectedSpace (ComplexModel 1) _
  have hself : ForwardAsymptotic g (p u) (p u) := by
    simp [ForwardAsymptotic]
  let inc : C(StableAsymptoticLeaf g (p u), S) :=
    ⟨Subtype.val, L.inclusion_holomorphic.continuous⟩
  obtain ⟨lift, hi, hproj, hpoint, _⟩ :=
    injective_pointed_leaf_lift hp inc Subtype.val_injective ⟨p u, hself⟩ u rfl
  refine ⟨lift, ?_, hi, hproj, hpoint⟩
  apply holomorphic_of_lift hpHol lift lift.continuous
  have heq : p ∘ lift = (Subtype.val : StableAsymptoticLeaf g (p u) → S) :=
    funext hproj
  rw [heq]
  exact L.inclusion_holomorphic


end HolomorphicAnosov.Ghys
