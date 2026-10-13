import HolomorphicAnosov.Paper.Ghys.ProjectiveDeveloping
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Topology.FreeAffineActionTranslations
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.GlobalHolonomy
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Deck
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import HolomorphicAnosov.Paper.Ghys.ProjectionInjectiveOnLiftedFibre
import HolomorphicAnosov.Paper.Ghys.LiftedLeafRangeOfDevelopingProduct

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- The covering projection is injective on each developing fibre when the product description
identifies that fibre with a single lifted intrinsic leaf. (Ghys, p.598) -/
theorem projection_injective_of_developing_product
    {E M Z L : Type*} [TopologicalSpace E] [TopologicalSpace Z] [SimplyConnectedSpace E]
    (p : E → M) (D : E → Z) (z₀ : Z)
    (B : ({e : E // D e = z₀} × Z) ≃ₜ E)
    (hcoord : ∀ r z, D (B (r, z)) = z) (e : E)
    (inc : L → M) (hi : Function.Injective inc) (lift : L → E)
    (hproj : ∀ x, p (lift x) = inc x)
    (hrange : Set.range lift = connectedComponentIn (D ⁻¹' {D e}) e) :
    Set.InjOn p {y : E | D y = D e} := by
  exact projection_injective_on_lifted_fibre p D (D e) inc hi lift hproj
    (lifted_leaf_range_of_developing_product D z₀ B hcoord e lift hrange)

end HolomorphicAnosov.Ghys

