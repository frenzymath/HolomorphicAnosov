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

/-- Every fibre of a developing map with a global product trivialization is the range of a
continuous retraction of the total space. (Ghys, p. 598) -/
theorem developing_fibre_retraction
    {E Z : Type*} [TopologicalSpace E] [TopologicalSpace Z]
    (D : E → Z) (z₀ z : Z) (B : ({e : E // D e = z₀} × Z) ≃ₜ E)
    (hcoord : ∀ r w, D (B (r, w)) = w) :
    ∃ r : E → E, Continuous r ∧ Set.range r = {e | D e = z} ∧
      ∀ e, D e = z → r e = e := by
  let r : E → E := fun e ↦ B ((B.symm e).1, z)
  have hr : Continuous r := B.continuous.comp (B.symm.continuous.fst.prodMk continuous_const)
  have hfix (e : E) (he : D e = z) : r e = e := by
    have hz : (B.symm e).2 = z := by
      have hh := hcoord (B.symm e).1 (B.symm e).2
      simpa only [Prod.mk.eta, B.apply_symm_apply, he] using hh.symm
    change B ((B.symm e).1, z) = e
    rw [← hz, Prod.mk.eta, B.apply_symm_apply]
  refine ⟨r, hr, ?_, hfix⟩
  ext e
  constructor
  · rintro ⟨a, rfl⟩
    exact hcoord _ _
  · intro he
    exact ⟨e, hfix e he⟩

end HolomorphicAnosov.Ghys

