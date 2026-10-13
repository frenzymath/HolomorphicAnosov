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

/-- A product equivalence compatible with a continuous developing map is a homeomorphism if the
equivalence and the first coordinate of its inverse are continuous. (Ghys, p.598) -/
theorem product_homeomorph_of_continuous_retraction
    {E Z : Type*} [TopologicalSpace E] [TopologicalSpace Z]
    (D : E → Z) (hD : Continuous D) (z₀ : Z)
    (B : ({e : E // D e = z₀} × Z) ≃ E)
    (hcoord : ∀ r z, D (B (r, z)) = z)
    (hB : Continuous B) (hr : Continuous (fun e ↦ (B.symm e).1)) :
    ∃ H : ({e : E // D e = z₀} × Z) ≃ₜ E,
      (∀ q, H q = B q) ∧ ∀ r z, D (H (r, z)) = z := by
  have hinv : B.symm = fun e ↦ ((B.symm e).1, D e) := by
    funext e
    refine Prod.ext rfl ?_
    have hh := hcoord (B.symm e).1 (B.symm e).2
    simpa only [Prod.mk.eta, B.apply_symm_apply] using hh.symm
  let H : ({e : E // D e = z₀} × Z) ≃ₜ E :=
    { B with
      continuous_toFun := hB
      continuous_invFun := by
        change Continuous B.symm
        rw [hinv]
        exact hr.prodMk hD }
  exact ⟨H, fun q ↦ rfl, hcoord⟩

end HolomorphicAnosov.Ghys

