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

/-- A covering projection is injective on a developing fibre that is the range of a lift of an
injectively parametrized intrinsic leaf. (Ghys, proof of Theorem B p.598) -/
theorem projection_injective_on_lifted_fibre
    {E M Z L : Type*} (p : E → M) (D : E → Z) (z : Z)
    (inc : L → M) (hi : Function.Injective inc) (lift : L → E)
    (hproj : ∀ x, p (lift x) = inc x)
    (hrange : Set.range lift = {e | D e = z}) :
    Set.InjOn p {e | D e = z} := by
  intro e he e' he' hp
  rw [← hrange] at he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  rw [hproj, hproj] at hp
  exact congrArg lift (hi hp)

end HolomorphicAnosov.Ghys

