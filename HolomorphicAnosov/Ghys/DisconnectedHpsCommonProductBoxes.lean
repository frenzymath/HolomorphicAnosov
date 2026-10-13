import HolomorphicAnosov.Dynamics.Anosov.NativeLeafRank
import HolomorphicAnosov.Geometry.AdaptedNativeProductRealBoxes
import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaques
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorMetric
import HolomorphicAnosov.Dynamics.Anosov.DistanceLeafRange
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.HasComplexRankOne_real_finrank_eq_two
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.original_real_tangent_finrank
import Mathlib.Topology.UniformSpace.Compact

/-! This file constructs common Euclidean product boxes for the native stable and unstable laminations of a disconnected HPS system. (HPS, §7; Shub, Prop. 10.10) -/

noncomputable section
open scoped ContDiff Manifold Bundle _root_.Topology
open Set TopologicalSpace _root_.Topology
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- The native stable and unstable laminations admit common Euclidean product boxes with the stated invariance, rank, and bracket properties. (HPS, §7; Shub, Prop. 10.10) -/
theorem disconnected_hps_common_product_boxes
    {d : ℕ} {M : Type u} [m₀ : MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    ∃ (ιs ιu : Type u) (Ls : ιs → Type u) (Lu : ιu → Type u)
      (topS : ∀ i, TopologicalSpace (Ls i))
      (topU : ∀ i, TopologicalSpace (Lu i)),
      letI := topS; letI := topU
      ∃ (chartS : ∀ i, ChartedSpace (Fin (2*d-2) → ℝ) (Ls i))
        (chartU : ∀ i, ChartedSpace (Fin 2 → ℝ) (Lu i)),
        letI := chartS; letI := chartU
        ∃ (smoothS : ∀ i, IsManifold 𝓘(ℝ, Fin (2*d-2) → ℝ) ∞ (Ls i))
          (smoothU : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Lu i)),
          letI := smoothS; letI := smoothU
          ∃ (Fs : HPS.LeafPartition a.splitting.stable.toDistribution
              ιs Ls (fun _ ↦ 2*d-2))
            (Fu : HPS.LeafPartition a.splitting.unstable.toDistribution
              ιu Lu (fun _ ↦ 2)),
            (∀ i x, Set.range (Fs.leaf i).inclusion =
              {y | ForwardAsymptotic f ((Fs.leaf i).inclusion x) y}) ∧
            (∀ i x, Set.range (Fu.leaf i).inclusion =
              {y | ForwardAsymptotic f.symm ((Fu.leaf i).inclusion x) y}) ∧
            (∀ p : M, ∃ (Ds : TopologicalSpace.Opens (Fin (2*d-2) → ℝ))
              (Du : TopologicalSpace.Opens (Fin 2 → ℝ))
              (O : TopologicalSpace.Opens M)
              (e : (Ds × Du) ≃ₜ O),
              p ∈ O ∧
              (∀ w : Du, ∃ (i : ιs) (V : TopologicalSpace.Opens (Ls i))
                (c : Ds ≃ₜ V),
                ∀ z : Ds, (e (z, w)).val =
                  (Fs.leaf i).inclusion (c z)) ∧
              (∀ z : Ds, ∃ (i : ιu) (V : TopologicalSpace.Opens (Lu i))
                (c : Du ≃ₜ V),
                ∀ w : Du, (e (z, w)).val =
                  (Fu.leaf i).inclusion (c w))) := by
  classical
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C, rate, hC, hr, hr1, hs, hu⟩ := fixed_block_uniform_anosov_estimates f a
  have hi (x : M) (v w : TangentSpace (realModel d) x) :
      inner ℝ v w = a.metric.inner x v w := rfl
  have hb : Nonempty (TensorAnosovBounds f.toReal a.splitting a.metric) := by
    refine ⟨⟨C, rate, hC, hr, hr1, ?_, ?_⟩⟩
    · intro n x v hv
      have he : (realIterate (realModel d) f.toReal n : M → M) =
          (f : M → M)^[n] := rfl
      rw [he]
      simpa only [norm_eq_sqrt_real_inner, hi] using hs n x v hv
    · intro n x v hv
      have he : (realIterate (realModel d) f.toReal.symm n : M → M) =
          (f.symm : M → M)^[n] := rfl
      rw [he]
      simpa only [norm_eq_sqrt_real_inner, hi] using hu n x v hv
  let ambientMetric : MetricSpace M := m₀
  let : MetricSpace M := ambientMetric
  obtain ⟨hstableNative, hunstableNative⟩ :=
    HPS.anosov_global_lamination_tensor_metric f.toReal a.splitting a.metric hb
  obtain ⟨ιu, Lu, ru, topU, chartU, smoothU, U, hboxesU, hinvariantU,
    familiesU, coherentU, hextraU⟩ := hunstableNative
  let := topU
  let := chartU
  let := smoothU
  have hrankU (i : ιu) : ru i = 2 := by
    let := (U.leaf i).connected
    obtain ⟨z⟩ := (inferInstance : Nonempty (Lu i))
    exact ((U.leaf i).finrank_tangent z).symm.trans
      (TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two hRank _)
  have hrufun : ru = (fun _ ↦ 2) := funext hrankU
  cases hrufun
  obtain ⟨ιs, Ls, rs, topS, chartS, smoothS, S, hboxesS, hinvariantS,
    familiesS, coherentS, hextraS⟩ := hstableNative
  let := topS
  let := chartS
  let := smoothS
  have hrankS (i : ιs) : rs i = 2 * d - 2 := by
    let := (S.leaf i).connected
    obtain ⟨z⟩ := (inferInstance : Nonempty (Ls i))
    have hsum := Submodule.finrank_add_eq_of_isCompl
      (a.splitting.isCompl ((S.leaf i).inclusion z))
    rw [(S.leaf i).finrank_tangent z,
      TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two hRank,
      TheoremAProof.Dimension.original_real_tangent_finrank] at hsum
    omega
  have hrsfun : rs = (fun _ ↦ 2 * d - 2) := funext hrankS
  cases hrsfun
  obtain ⟨_, _, _, _, ⟨identificationS, _⟩, _, _⟩ := hextraS
  obtain ⟨_, _, _, _, ⟨identificationU, _⟩, _, _⟩ := hextraU
  have hsAP (x : M) (n : ℕ) (v : TangentSpace (realModel d) x)
      (hv : v ∈ a.splitting.stable.toDistribution x) :
      hyperbolicRiemannianNorm a.metric
        (mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) x v) ≤
          max C 1 * rate ^ n * hyperbolicRiemannianNorm a.metric v := by
    have h := (hs n x v hv).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hr.le n)) (norm_nonneg v))
    simpa only [hyperbolicRiemannianNorm, norm_eq_sqrt_real_inner, hi] using h
  have huAP (x : M) (n : ℕ) (v : TangentSpace (realModel d) x)
      (hv : v ∈ a.splitting.unstable.toDistribution x) :
      hyperbolicRiemannianNorm a.metric
        (mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[n]) x v) ≤
          max C 1 * rate ^ n * hyperbolicRiemannianNorm a.metric v := by
    have h := (hu n x v hv).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hr.le n)) (norm_nonneg v))
    simpa only [hyperbolicRiemannianNorm, norm_eq_sqrt_real_inner, hi] using h
  let dynS := Classical.choice hinvariantS
  let dynU := Classical.choice hinvariantU
  let NS := nativeInvariantLeafSystemOfPartition a.splitting.stable.toDistribution f.toReal S dynS
  let NU := nativeInvariantLeafSystemInverse a.splitting.unstable.toDistribution f.toReal
    (nativeInvariantLeafSystemOfPartition a.splitting.unstable.toDistribution f.toReal U dynU)
  obtain ⟨h, productMetric, D, θ, lam, β₀, γ₀, ε₀, hD, hθpos, hθlt, hlampos, hlamlt,
    hγ₀, hβ₀, hε₀, hproductTopology, hcomp, hsep, hs₁, hu₁, _⟩ :=
      hirschPughAdaptedOrbitPlaques f.toReal a.splitting a.metric (max C 1) rate
        (le_max_right C 1) hr hr1 hsAP huAP
  let : MetricSpace M := m₀
  obtain ⟨β, γ, ε, hγ, _, hβ, hε, ⟨stableOrbitPlaques⟩, ⟨unstableOrbitPlaques⟩,
    _, _, bracket, hbracketContinuous, hbracketIntersection, products⟩ :=
    @hirschPughAdaptedOrbitPlaques_geometry (ComplexModel d) _ _ M
      m₀.toUniformSpace.toTopologicalSpace _ _ _ _ _ f.toReal a.splitting h productMetric 1
      (by norm_num) hproductTopology hcomp θ hθpos hθlt hs₁ hu₁ NS NU
  let : MetricSpace M := m₀
  have hRealBoxes (x : M) :
      ∃ (Ds : Opens (Fin (2*d-2) → ℝ)) (Du : Opens (Fin 2 → ℝ))
        (O : Opens M) (e : (Ds × Du) ≃ₜ O), x ∈ O ∧
        (∀ w : Du, ∃ (i : ιs) (V : Opens (Ls i)) (c : Ds ≃ₜ V),
          ∀ z : Ds, (e (z,w)).val = (S.leaf i).inclusion (c z).val) ∧
        (∀ z : Ds, ∃ (i : ιu) (V : Opens (Lu i)) (c : Du ≃ₜ V),
          ∀ w : Du, (e (z,w)).val = (U.leaf i).inclusion (c w).val) := by
    obtain ⟨Ds, Du, O, e, hx, hs, hu⟩ := adaptedProduct_real_box f.toReal
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution productMetric
      NS NU hγ hε bracket hbracketIntersection stableOrbitPlaques unstableOrbitPlaques hβ
      hproductTopology x (Classical.choice (products x))
    refine ⟨Ds, Du, O, e, hx, ?_, ?_⟩
    · intro w
      obtain ⟨y, V, c, hc⟩ := hs w
      exact ⟨Classical.choose (S.cover y), V, c, hc⟩
    · intro z
      obtain ⟨y, V, c, hc⟩ := hu z
      exact ⟨Classical.choose (U.cover y), V, c, hc⟩
  refine ⟨ιs, ιu, Ls, Lu, topS, topU, chartS, chartU, smoothS, smoothU,
    S, U, ?_, ?_, hRealBoxes⟩
  · intro i x
    exact identificationS.range_eq_forwardAsymptotic i x
  · intro i x
    exact identificationU.range_eq_forwardAsymptotic i x

end HolomorphicAnosov.Ghys
