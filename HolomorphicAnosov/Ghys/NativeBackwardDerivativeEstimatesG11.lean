import HolomorphicAnosov.Ghys.RealMetricAffinePlaque
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates

noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff Bundle
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- The actual backward leaf diffeomorphisms are smooth in the original real atlases and contract the original pullback tangent speeds by Cρⁿ for fixed C>0 and 0<ρ<1. Source: Ghys (1995), Lemma 3. -/
theorem native_backward_derivative_estimates
    {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2)) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (n : ℕ) (i j : ι)
        (B : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L i) (L j) ∞),
        (∀ x, (U.leaf j).inclusion (B x) =
          ((f.symm : M → M)^[n]) ((U.leaf i).inclusion x)) →
        ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ B ∧
        ∀ z (v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) z),
          realMetricLeafSpeed a.metric (U.leaf j).inclusion (B z)
            (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) B z v) ≤
            (C * ρ ^ n) * realMetricLeafSpeed a.metric (U.leaf i).inclusion z v := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C, ρ, hC, hρ, hρ1, _, hu⟩ := fixed_block_uniform_anosov_estimates f a
  refine ⟨C, ρ, hC, hρ, hρ1, ?_⟩
  intro n i j B hsq
  have hinc (k : ι) : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
      (U.leaf k).inclusion := (U.leaf k).immersion.contMDiff
  have hBreal : ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ B := by
    apply (ContMDiff.iff_comp_isImmersion (U.leaf j).immersion).2
    refine ⟨B.continuous, ?_⟩
    have heq : (U.leaf j).inclusion ∘ B =
        ((f.symm : M → M)^[n]) ∘ (U.leaf i).inclusion := funext hsq
    rw [heq]
    exact (f.toReal.symm.contMDiff.iterate n).comp (hinc i)
  have hF : ContMDiff (realModel d) (realModel d) ∞ ((f.symm : M → M)^[n]) :=
    f.toReal.symm.contMDiff.iterate n
  have hspeed : ∀ z (v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) z),
      realMetricLeafSpeed a.metric (U.leaf j).inclusion (B z)
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) B z v) ≤
      (C * ρ ^ n) * realMetricLeafSpeed a.metric (U.leaf i).inclusion z v := by
    intro z v
    have heq : (U.leaf j).inclusion ∘ B =
        ((f.symm : M → M)^[n]) ∘ (U.leaf i).inclusion := funext hsq
    have hd : mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (U.leaf j).inclusion (B z)
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) B z v) =
        mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[n])
          ((U.leaf i).inclusion z)
          (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (U.leaf i).inclusion z v) := by
      change @Eq (ComplexModel d) _ _
      have he := congrArg (fun q : L i → M ↦
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) q z v : ComplexModel d)) heq
      simpa only [mfderiv_comp z ((hinc j).mdifferentiable (by simp) _)
          (hBreal.mdifferentiable (by simp) _),
        mfderiv_comp z (hF.mdifferentiable (by simp) _)
          ((hinc i).mdifferentiable (by simp) _),
        ContinuousLinearMap.comp_apply] using he
    have hv : mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (U.leaf i).inclusion z v ∈
        a.splitting.unstable.toDistribution ((U.leaf i).inclusion z) := by
      rw [← (U.leaf i).tangent z]
      exact ⟨v, rfl⟩
    have hb := hu n ((U.leaf i).inclusion z) _ hv
    let H : M → ComplexModel d → ComplexModel d → ℝ := fun z v w ↦ a.metric.inner z v w
    change Real.sqrt (H ((U.leaf j).inclusion (B z)) _ _) ≤ _
    rw [hd, hsq z]
    have hnorm (q : M) (w : TangentSpace (realModel d) q) :
        ‖w‖ = Real.sqrt (a.metric.inner q w w) := rfl
    rw [hnorm, hnorm] at hb
    exact hb
  exact ⟨hBreal, hspeed⟩
end HolomorphicAnosov.Ghys
