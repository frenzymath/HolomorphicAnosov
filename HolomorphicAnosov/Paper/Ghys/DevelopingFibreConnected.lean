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
import HolomorphicAnosov.Paper.Ghys.DevelopingFibreRetraction

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- Every fibre of a developing map on a simply connected total space with a global product
trivialization is connected. (Ghys, Thm B, p. 598) -/
theorem developing_fibre_connected
    {E Z : Type*} [TopologicalSpace E] [TopologicalSpace Z] [SimplyConnectedSpace E]
    (D : E → Z) (z₀ z : Z) (B : ({e : E // D e = z₀} × Z) ≃ₜ E)
    (hcoord : ∀ r w, D (B (r, w)) = w) :
    IsConnected {e : E | D e = z} := by
  obtain ⟨r, hr, hrange, _⟩ := developing_fibre_retraction D z₀ z B hcoord
  rw [← hrange]
  exact isConnected_range hr

end HolomorphicAnosov.Ghys

