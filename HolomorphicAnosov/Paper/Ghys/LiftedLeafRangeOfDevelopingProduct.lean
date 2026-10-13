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
import HolomorphicAnosov.Paper.Ghys.DevelopingFibreConnected

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- In the continuous product, each developing-fibre component is the entire fibre. (Ghys, Thm. B) -/
theorem lifted_leaf_range_of_developing_product
    {E Z L : Type*} [TopologicalSpace E] [TopologicalSpace Z] [SimplyConnectedSpace E]
    (D : E → Z) (z₀ : Z) (B : ({e : E // D e = z₀} × Z) ≃ₜ E)
    (hcoord : ∀ r z, D (B (r, z)) = z) (e : E) (lift : L → E)
    (hrange : Set.range lift = connectedComponentIn (D ⁻¹' {D e}) e) :
    Set.range lift = {y : E | D y = D e} := by
  rw [hrange]
  exact (developing_fibre_connected D z₀ (D e) B hcoord).2.connectedComponentIn rfl

end HolomorphicAnosov.Ghys

