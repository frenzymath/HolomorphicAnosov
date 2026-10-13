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

/-- The equation `q ∘ F = μ * q` implies that the pullback of the scalar differential of `q` by `F`
equals `μ` times that differential. (Zhang, Lemma 4.2, (23)) -/
theorem native_scalar_differential_equivariance
    {d : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel d) Y]
    (q : Y → ℂ) (F : Y → Y) (μ : ℂ) (y : Y)
    (hq : MDifferentiable (complexModel d) 𝓘(ℂ, ℂ) q)
    (hF : MDifferentiableAt (complexModel d) (complexModel d) F y)
    (hEq : q ∘ F = μ • q) :
    (transverseScalarDifferential (d := d) q (F y)).comp
      (mfderiv (complexModel d) (complexModel d) F y) =
      μ • transverseScalarDifferential (d := d) q y := by
  rw [← native_scalar_differential_comp q F y (hq (F y)) hF, hEq]
  unfold transverseScalarDifferential
  rw [const_smul_mfderiv (hq y) μ]
  ext v
  rfl


end HolomorphicAnosov.Paper.Zhang
