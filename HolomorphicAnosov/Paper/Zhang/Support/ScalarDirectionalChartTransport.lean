import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.ComplexToRealManifold

/-! Chart transport of scalar directional derivatives. -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

set_option backward.isDefEq.respectTransparency false in
/-- A scalar directional derivative pulled back through a manifold chart equals the manifold
differential evaluated on the original tangent vector. (Zhang, eq. (13), p. 7) -/
theorem scalar_directional_chart_transport
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ atlas (ComplexModel d) X)
    (g : X → ℂ) {z : ComplexModel d} (hz : z ∈ c.target)
    (hg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) g (c.symm z))
    (Y : (x : X) → TangentSpace (realModel d) x) :
    fderiv ℝ (g ∘ c.symm) z
        (VectorField.mpullback (realModel d) (realModel d) c.symm Y z) =
      QuotientLineConnection.realDifferential (d := d) g (c.symm z) (Y (c.symm z)) := by
  have hc' : c.MDifferentiable (realModel d) (realModel d) :=
    mdifferentiable_of_mem_atlas hc
  have hi : (mfderiv (realModel d) (realModel d) c.symm z).IsInvertible :=
    ⟨hc'.symm.mfderiv hz, rfl⟩
  have hs := hc'.mdifferentiableAt_symm hz
  rw [← mfderiv_eq_fderiv, mfderiv_comp z hg hs, VectorField.mpullback_apply]
  change mfderiv (realModel d) 𝓘(ℝ, ℂ) g (c.symm z)
      (mfderiv (realModel d) (realModel d) c.symm z
        ((mfderiv (realModel d) (realModel d) c.symm z).inverse (Y (c.symm z)))) = _
  rw [hi.self_apply_inverse]
  rfl

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport

