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

/-- Holomorphic scalar potentials differing by a constant near a point have equal scalar
differentials in its manifold tangent fibre. (Zhang, Lemma 4.2) -/
theorem translated_native_potentials_same_covector
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X]
    (g h : X → ℂ) (x : X) (c : ℂ)
    (hg : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) g x)
    (heq : h =ᶠ[𝓝 x] fun y ↦ g y + c) :
    transverseScalarDifferential (d := d) h x =
      transverseScalarDifferential (d := d) g x := by
  have hh := heq.mfderiv_eq (I := complexModel d) (I' := 𝓘(ℂ, ℂ))
  ext v
  change mfderiv (complexModel d) 𝓘(ℂ, ℂ) h x v =
    mfderiv (complexModel d) 𝓘(ℂ, ℂ) g x v
  rw [hh]
  simp only [tangentSpaceCast]
  change mfderiv (complexModel d) 𝓘(ℂ, ℂ) (g + fun _ ↦ c) x v =
    mfderiv (complexModel d) 𝓘(ℂ, ℂ) g x v
  have hadd : (mfderiv (complexModel d) 𝓘(ℂ, ℂ) (g + fun _ ↦ c) x :
      TangentSpace (complexModel d) x →L[ℂ] ℂ) =
      (by exact mfderiv (complexModel d) 𝓘(ℂ, ℂ) g x) := by
    exact (mfderiv_add hg (mdifferentiableAt_const (c := c))).trans (by
      rw [mfderiv_const]
      ext w
      change (transverseScalarDifferential (d := d) g x w) + (0 : ℂ) =
        transverseScalarDifferential (d := d) g x w
      exact add_zero _)
  exact congrArg (fun L : TangentSpace (complexModel d) x →L[ℂ] ℂ ↦ L v) hadd


end HolomorphicAnosov.Paper.Zhang
