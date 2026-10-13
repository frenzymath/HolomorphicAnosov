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


noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- A deck transformation of a connected cover with a fixed point is the identity. (Hatcher, Prop.
1.34, p. 62; Ghys, Thm B, p. 598) -/
theorem deck_identity_of_fixed_point
    {E M : Type*} [TopologicalSpace E] [TopologicalSpace M] [PreconnectedSpace E]
    {p : E → M} (hp : IsCoveringMap p) (g : deck p) (e : E)
    (he : (g : E ≃ₜ E) e = e) : g = 1 := by
  have hfun : (fun x ↦ (g : E ≃ₜ E) x) = (id : E → E) :=
    hp.eq_of_comp_eq (g : E ≃ₜ E).continuous continuous_id (deck.comp_eq g) e he
  apply Subtype.ext
  apply Homeomorph.ext
  intro x
  exact congrFun hfun x

end HolomorphicAnosov.Ghys

