import HolomorphicAnosov.Paper.Ghys.CompleteLiftedProjectiveLeaves
import HolomorphicAnosov.Paper.Ghys.CompleteAffineLeafHolomorphicLift
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveLiftComponent
import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveDevelopmentFrameContinuation

noncomputable section
open Set _root_.Topology
open scoped ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real

/-- A simply connected holomorphic cover of an ordered projective atlas carries a development with holonomy in the ordered PSL product. (Thurston, §§3.5, 4.8; Ghys, §5) -/
theorem ordered_projective_product_development_exists
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] {p : U → S}
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hsimply : SimplyConnectedSpace U)
    (hhol : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ p) :
    Nonempty (OrderedProjectiveProductDevelopment A p) := by
  exact (ordered_projective_product_development_frame_continuation A hp hsurj hsimply hhol).1

end HolomorphicAnosov.Ghys
