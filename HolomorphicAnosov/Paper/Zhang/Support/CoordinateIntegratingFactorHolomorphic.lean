import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! Complex differentiability of coordinate integrating factors. (Zhang, Lemma 2.4, p. 7; Demailly,
I §3.C, p. 23, V.3, p. 256) -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

/-- A real coordinate integrating factor for a holomorphic quotient-line connection is complex
differentiable wherever its derivative equation holds. (Zhang, Lemma 2.4, p. 7) -/
theorem coordinate_integrating_factor_differentiable
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (nabla : QuotientLineConnection.Connection U)
    (hhol : QuotientLineConnection.IsHolomorphic nabla)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ atlas (ComplexModel d) X)
    (g : ComplexModel d → ℂ) (z : ComplexModel d)
    (hz : z ∈ c.target) (hzV : c.symm z ∈ V)
    (hg : HasFDerivAt g
      (-(g z) • QuotientLineConnection.coordinateForm nabla e c z) z) :
    DifferentiableAt ℂ g z := by
  have hf : MDifferentiableAt (complexModel d) (complexModel d) c.symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := complexModel d) (n := ∞) hc) hz).mdifferentiableAt
      (by simp)
  have hr : MDifferentiableAt (realModel d) (realModel d) c.symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := realModel d) (n := ∞) hc) hz).mdifferentiableAt
      (by simp)
  have hder : mfderiv (realModel d) (realModel d) c.symm z =
      (mfderiv (complexModel d) (complexModel d) c.symm z).restrictScalars ℝ := by
    ext v
    apply (tangentSpaceCastModel (realModel d) (c.symm z)).injective
    rw [hf.mfderiv_abuse, hr.mfderiv_abuse]
    have hd := hf.differentiableWithinAt_writtenInExtChartAt
    change (fderivWithin ℝ (writtenInExtChartAt (complexModel d) (complexModel d) z c.symm)
        (Set.range (complexModel d)) ((extChartAt (complexModel d) z) z)) v =
      (fderivWithin ℂ (writtenInExtChartAt (complexModel d) (complexModel d) z c.symm)
        (Set.range (complexModel d)) ((extChartAt (complexModel d) z) z)) v
    exact congrArg (fun L ↦ L v) (hd.restrictScalars_fderivWithin ℝ (by simp)).symm
  let D : ComplexModel d →L[ℂ] TangentSpace (complexModel d) (c.symm z) :=
    (mfderiv (complexModel d) (complexModel d) c.symm z).comp
      (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap
  let A := QuotientLineConnection.coordinateForm nabla e c z
  have hAI (v : ComplexModel d) : A (Complex.I • v) = Complex.I * A v := by
    change nabla.form V e (c.symm z)
      (mfderiv (realModel d) (realModel d) c.symm z (Complex.I • v)) =
      Complex.I * nabla.form V e (c.symm z)
        (mfderiv (realModel d) (realModel d) c.symm z v)
    rw [hder]
    change nabla.form V e (c.symm z)
      (complexTangentToReal d (c.symm z) (D (Complex.I • v))) =
      Complex.I * nabla.form V e (c.symm z)
        (complexTangentToReal d (c.symm z) (D v))
    rw [D.map_smul]
    exact hhol.1 V e (c.symm z) hzV _
  let L : ComplexModel d →L[ℂ] ℂ := {
    toFun := A
    map_add' := A.map_add
    map_smul' := by
      intro a v
      rw [← Complex.re_add_im a]
      simp only [add_smul, mul_smul, Complex.coe_smul, map_add, map_smul, hAI,
        smul_eq_mul, RingHom.id_apply, Complex.real_smul]
      ring
    cont := A.continuous }
  have hg' : HasFDerivAt g ((-(g z) • L).restrictScalars ℝ) z := by
    convert hg using 1
    ext v
    rfl
  exact (hasFDerivAt_of_restrictScalars ℝ hg' rfl).differentiableAt

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
