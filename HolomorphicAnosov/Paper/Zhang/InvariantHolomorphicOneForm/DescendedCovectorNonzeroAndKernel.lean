import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeScalarDifferentialComp

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- The covector descended from a submersion through an inverse covering sheet is nonzero, and its
kernel is the prescribed real tangent subspace under `complexTangentToReal`. (Zhang, Lemma 4.2) -/
theorem descended_covector_nonzero_and_kernel
    {d : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
    (q : Y → ℂ) (s : X → Y) (x : X)
    (U : Submodule ℝ (TangentSpace (realModel d) x))
    (θ : TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ : θ = transverseScalarDifferential (d := d) (q ∘ s) x)
    (hq : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) q (s x))
    (hs : MDifferentiableAt (complexModel d) (complexModel d) s x)
    (Dp : TangentSpace (complexModel d) (s x) →L[ℂ] TangentSpace (complexModel d) x)
    (hDpDs : Dp.comp (mfderiv (complexModel d) (complexModel d) s x) =
      ContinuousLinearMap.id ℂ _)
    (hDsDp : (mfderiv (complexModel d) (complexModel d) s x).comp Dp =
      ContinuousLinearMap.id ℂ _)
    (hqsurj : Function.Surjective (transverseScalarDifferential (d := d) q (s x)))
    (hkernel : ∀ w : TangentSpace (complexModel d) (s x),
      transverseScalarDifferential (d := d) q (s x) w = 0 ↔
        complexTangentToReal d x (Dp w) ∈ U) :
    θ ≠ 0 ∧ ∀ v, θ v = 0 ↔ complexTangentToReal d x v ∈ U := by
  have heq := hθ.trans (native_scalar_differential_comp q s x hq hs)
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := hqsurj 1
    have hv : mfderiv (complexModel d) (complexModel d) s x (Dp w) = w :=
      DFunLike.congr_fun hDsDp w
    have hone : θ (Dp w) = 1 := by
      rw [heq]
      change transverseScalarDifferential (d := d) q (s x)
        (mfderiv (complexModel d) (complexModel d) s x (Dp w)) = 1
      rw [hv, hw]
    rw [hz] at hone
    simp at hone
  · intro v
    rw [heq]
    change transverseScalarDifferential (d := d) q (s x)
      (mfderiv (complexModel d) (complexModel d) s x v) = 0 ↔ _
    rw [hkernel]
    have hv : Dp (mfderiv (complexModel d) (complexModel d) s x v) = v :=
      DFunLike.congr_fun hDpDs v
    rw [hv]


end HolomorphicAnosov.Paper.Zhang
