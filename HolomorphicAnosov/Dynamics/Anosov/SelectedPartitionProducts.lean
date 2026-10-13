import HolomorphicAnosov.Geometry.AdaptedNativeProductRealBoxes
import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaques
import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaquesGeometry

/-! The existing selected-partition product theorem, moved upstream unchanged
from NativeActualInvariantFlowboxInput so both the native flowbox and the Zhang
stable-foliation construction can use it without an import cycle. -/
open Set _root_.Topology
noncomputable section
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
variable {ιs ιu : Type u} {Ls : ιs → Type u} {Lu : ιu → Type u}
  {rs : ιs → ℕ} {ru : ιu → ℕ}
  [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
  [∀ i, ChartedSpace (Fin (rs i) → ℝ) (Ls i)]
  [∀ i, ChartedSpace (Fin (ru i) → ℝ) (Lu i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin (rs i) → ℝ) ∞ (Ls i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin (ru i) → ℝ) ∞ (Lu i)]

theorem selectedPartitionProducts
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (splitting : InvariantRealTangentSplitting f)
    (h₀ : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (C τ : ℝ) (hC : 1 ≤ C) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hs : ∀ (x : M) (n : ℕ) (v : TangentSpace 𝓘(ℝ, E) x),
      v ∈ splitting.stable.toDistribution x →
        hyperbolicRiemannianNorm h₀
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f : M → M)^[n]) x v) ≤
            C * τ ^ n * hyperbolicRiemannianNorm h₀ v)
    (hu : ∀ (x : M) (n : ℕ) (v : TangentSpace 𝓘(ℝ, E) x),
      v ∈ splitting.unstable.toDistribution x →
        hyperbolicRiemannianNorm h₀
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f.symm : M → M)^[n]) x v) ≤
            C * τ ^ n * hyperbolicRiemannianNorm h₀ v)
    (S : HPS.LeafPartition splitting.stable.toDistribution ιs Ls rs)
    (U : HPS.LeafPartition splitting.unstable.toDistribution ιu Lu ru)
    (ds : HPS.LeafDynamicalInvariance S f) (du : HPS.LeafDynamicalInvariance U f) :
    let NS := nativeInvariantLeafSystemOfPartition splitting.stable.toDistribution f S ds
    let NU := nativeInvariantLeafSystemInverse splitting.unstable.toDistribution f
      (nativeInvariantLeafSystemOfPartition splitting.unstable.toDistribution f U du)
    ∃ (m : MetricSpace M) (β γ ε : ℝ), 0 < γ ∧ 2 * γ < β ∧ 0 < ε ∧
      m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) ∧
      Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f splitting.stable.toDistribution m β γ NS) ∧
      Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm splitting.unstable.toDistribution m β γ NU) ∧
      ∃ bracket : adaptedClosePairDomain (M := M) m ε → M,
        Continuous bracket ∧
        (∀ p : adaptedClosePairDomain (M := M) m ε,
          adaptedClosedOrbitCore 𝓘(ℝ, E) f m γ p.1.1 ∩
            adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm m γ p.1.2 = {bracket p}) ∧
        ∀ x : M, Nonempty (AdaptedNativeProduct 𝓘(ℝ, E) f
          splitting.stable.toDistribution splitting.unstable.toDistribution
          m γ ε NS NU bracket x) := by
  let NS := nativeInvariantLeafSystemOfPartition splitting.stable.toDistribution f S ds
  let NU := nativeInvariantLeafSystemInverse splitting.unstable.toDistribution f
    (nativeInvariantLeafSystemOfPartition splitting.unstable.toDistribution f U du)
  obtain ⟨h, m, D, θ, lam, β₀, γ₀, ε₀, hD, hθpos, hθlt, hlampos, hlamlt,
    hγ₀, hβ₀, hε₀, htop, hcomp, hsep, hs₁, hu₁, _⟩ :=
      hirschPughAdaptedOrbitPlaques f splitting h₀ C τ hC hτ₀ hτ₁ hs hu
  obtain ⟨β, γ, ε, hγ, _, hβ, hε, hNS, hNU, _, _, hbracket⟩ :=
    hirschPughAdaptedOrbitPlaques_geometry f splitting h m 1 (by norm_num) htop hcomp
      θ hθpos hθlt hs₁ hu₁ NS NU
  exact ⟨m, β, γ, ε, hγ, hβ, hε, htop, hNS, hNU, hbracket⟩
end HolomorphicAnosov.Ghys
