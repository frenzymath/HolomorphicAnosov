import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- The pullback of a manifold scalar differential along a differentiable map from a normed space is
the ordinary differential of the composed potential. (Demailly, I §3.C, (3.19); Zhang, Lemma
4.2) -/
theorem native_scalar_differential_pullback
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : X → ℂ) (Q : E → X) (z : E)
    (ht : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) t (Q z))
    (hQ : MDifferentiableAt 𝓘(ℂ, E) (complexModel d) Q z) :
    (transverseScalarDifferential (d := d) t (Q z)).comp
      (mfderiv 𝓘(ℂ, E) (complexModel d) Q z) = fderiv ℂ (t ∘ Q) z := by
  have h := mfderiv_comp z ht hQ
  rw [mfderiv_eq_fderiv] at h
  convert! h.symm using 1


end HolomorphicAnosov.Paper.Zhang
