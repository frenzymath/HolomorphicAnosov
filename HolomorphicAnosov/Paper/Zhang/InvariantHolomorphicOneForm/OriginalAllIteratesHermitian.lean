import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalNormComparison

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.OneFormBundle

attribute [local instance] complex_isManifold_real
universe u

/-- All-iterate Anosov estimates hold in any smooth Hermitian tangent metric on a compact complex
manifold, with the same contraction rate and a uniform comparison constant. (Zhang, Lemma 4.3,
pp.15–16; Demailly, I §3.C, pp.23–25) -/
theorem original_all_iterates_hermitian {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] (f : Biholomorph d d M M) (a : AnosovDatum f)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    ∃ C rate : ℝ, 0 < C ∧ (0 < rate ∧ rate < 1) ∧
      (∀ n x (v : TangentSpace (realModel d) x),
        v ∈ a.splitting.stable.toDistribution x →
        Real.sqrt (hermitianTangentRealPairing h ((f : M → M)^[n] x)
          (mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) x v)
          (mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) x v)) ≤
          C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v)) ∧
      (∀ n x (v : TangentSpace (realModel d) x),
        v ∈ a.splitting.unstable.toDistribution x →
        Real.sqrt (hermitianTangentRealPairing h ((f.symm : M → M)^[n] x)
          (mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[n]) x v)
          (mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[n]) x v)) ≤
          C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v)) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C₀, rate, hC₀, hrate, hrate1, hs, hu⟩ := fixed_block_uniform_anosov_estimates f a
  obtain ⟨c, C₁, hc, hcC₁, hC₁, hcompare⟩ := original_norm_comparison f a h hh
  have hcomp (x : M) (v : TangentSpace (realModel d) x) :
      c * Real.sqrt (hermitianTangentRealPairing h x v v) ≤ ‖v‖ ∧
      ‖v‖ ≤ C₁ * Real.sqrt (hermitianTangentRealPairing h x v v) := by
    simpa only [hermitianTangentRealPairing, hermitianTangentPairing,
      ContinuousLinearEquiv.apply_symm_apply] using
      hcompare x ((complexTangentToReal d x).symm v)
  have transport (n : ℕ) (x y : M) (v : TangentSpace (realModel d) x)
      (w : TangentSpace (realModel d) y) (hb : ‖w‖ ≤ C₀ * rate ^ n * ‖v‖) :
      Real.sqrt (hermitianTangentRealPairing h y w w) ≤
        (C₀ * C₁ / c) * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v) := by
    have hbound := (hcomp y w).1.trans (hb.trans
      (mul_le_mul_of_nonneg_left (hcomp x v).2
        (mul_nonneg hC₀.le (pow_nonneg hrate.le n))))
    have hquot : Real.sqrt (hermitianTangentRealPairing h y w w) ≤
        (C₀ * rate ^ n * (C₁ * Real.sqrt (hermitianTangentRealPairing h x v v))) / c := by
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using hbound
    convert hquot using 1; ring
  refine ⟨C₀ * C₁ / c, rate, div_pos (mul_pos hC₀ (lt_of_lt_of_le zero_lt_one hC₁)) hc,
    ⟨hrate, hrate1⟩, ?_, ?_⟩
  · intro n x v hv
    exact transport n x _ v _ (hs n x v hv)
  · intro n x v hv
    exact transport n x _ v _ (hu n x v hv)


end HolomorphicAnosov.OneFormBundle
