import HolomorphicAnosov.Analysis.BoundedContinuousInvariantSections
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Regularity.AmbientJourneRegularity
import HolomorphicAnosov.Analysis.SeparatelyHolomorphicSmooth
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle


namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff

attribute [local instance] complex_isManifold_real

/-- For a covector nonzero on `b j`, the vectors `b i - (L (b i) / L (b j)) • b j` with `i ≠ j` are
linearly independent and span its kernel. (Demailly, II §3, pp. 85–86) -/
theorem rankOneKernelFrame {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E] (b : Module.Basis ι ℂ E)
    (L : E →ₗ[ℂ] ℂ) (j : ι) (hj : L (b j) ≠ 0) :
    let v := fun i : {i : ι // i ≠ j} ↦ b i.val - (L (b i.val) / L (b j)) • b j
    LinearIndependent ℂ v ∧ Submodule.span ℂ (Set.range v) = LinearMap.ker L := by
  classical
  dsimp only
  constructor
  · apply linearIndependent_iff'.2
    intro s c hc i hi
    have hcoord := congrArg (fun x ↦ b.repr x i.val) hc
    simpa [map_sum, map_smul, map_sub, Finsupp.sum_apply, b.repr_self_apply,
      i.property, Ne.symm i.property, Finsupp.single_apply, Subtype.val_inj, hi] using hcoord
  · apply le_antisymm
    · apply Submodule.span_le.2
      rintro x ⟨i, rfl⟩
      simp [LinearMap.mem_ker, map_sub, map_smul, div_mul_cancel₀ _ hj]
    · intro x hx
      have hL : L x = 0 := hx
      have hsum : (∑ i, b.repr x i * (L (b i) / L (b j))) = 0 := by
        simp_rw [← mul_div_assoc]
        rw [← Finset.sum_div]
        have heq := congrArg L (b.sum_repr x)
        simp only [map_sum, map_smul, smul_eq_mul] at heq
        rw [heq, hL, zero_div]
      have hrepr : (∑ i, b.repr x i • (b i - (L (b i) / L (b j)) • b j)) = x := by
        simp_rw [smul_sub, smul_smul]
        rw [Finset.sum_sub_distrib, b.sum_repr, ← Finset.sum_smul, hsum,
          zero_smul, sub_zero]
      rw [← hrepr]
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      by_cases hij : i = j
      · subst i
        simp [hj]
      · exact Submodule.subset_span ⟨⟨i, hij⟩, rfl⟩



end HolomorphicAnosov
