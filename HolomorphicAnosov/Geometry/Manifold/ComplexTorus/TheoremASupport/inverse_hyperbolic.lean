import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Paper.Zhang.CodimensionOne
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Paper.Zhang.TorusModel
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Compactness.Compact
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.inverseModel

namespace HolomorphicAnosov.TheoremAProof.ModelInverse
noncomputable section

theorem inverse_hyperbolic {d : ℕ} {L : FullComplexLattice d}
    (A : LatticeLinearEquiv L) (hA : ComplexLinearHyperbolic A.linear.toLinearMap) :
    ComplexLinearHyperbolic (inverseModel A).linear.toLinearMap := by
  intro μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have he : A.linear.symm v = μ • v := by
    simpa [inverseModel] using hv.apply_eq_smul
  have hm : μ ≠ 0 := by
    intro hm
    have hz : A.linear.symm v = 0 := by simpa [hm] using he
    exact hv.2 (A.linear.symm.injective (hz.trans (map_zero _).symm))
  have hav : A.linear v = μ⁻¹ • v := by
    have h := congrArg A.linear he
    simp only [LinearEquiv.apply_symm_apply, map_smul] at h
    calc
      A.linear v = (μ⁻¹ * μ) • A.linear v := by rw [inv_mul_cancel₀ hm, one_smul]
      _ = μ⁻¹ • v := by rw [mul_smul, ← h]
  have hev : Module.End.HasEigenvector A.linear.toLinearMap μ⁻¹ v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hav, hv.2⟩
  intro hn
  apply hA μ⁻¹ (Module.End.hasEigenvalue_of_hasEigenvector hev)
  rw [norm_inv, hn, inv_one]


end
end HolomorphicAnosov.TheoremAProof.ModelInverse
