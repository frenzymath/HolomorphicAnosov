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

/-- The scalar differential of `q ∘ s` is the scalar differential of `q` composed with the manifold
derivative of `s`. (Zhang, Lemma 4.2; Demailly, (3.19)) -/
theorem native_scalar_differential_comp
    {d e : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel e) Y]
    (q : Y → ℂ) (s : X → Y) (x : X)
    (hq : MDifferentiableAt (complexModel e) 𝓘(ℂ, ℂ) q (s x))
    (hs : MDifferentiableAt (complexModel d) (complexModel e) s x) :
    transverseScalarDifferential (d := d) (q ∘ s) x =
      (transverseScalarDifferential (d := e) q (s x)).comp
        (mfderiv (complexModel d) (complexModel e) s x) := by
  unfold transverseScalarDifferential
  rw [mfderiv_comp x hq hs]
  rfl


end HolomorphicAnosov.Paper.Zhang
