import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.RankOneStableHolomorphicUnstable
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExists
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalAllIteratesHermitian
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeAsymptoticDatumOfLeaf
import Mathlib.Geometry.Manifold.Metrizable

open scoped Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-! An Anosov map with complex stable rank one admits native unstable leaf data on its inverse
asymptotic carriers, with intrinsic charts and inclusion tangent images equal to the unstable
distribution. (Zhang, §2.1, pp. 5–7; HPS, §§6B–7, pp. 114–116) -/
theorem exists_native_unstable_leaf_data_of_anosov
    {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (_hstable : HasComplexRankOne a.splitting.stable.toDistribution) :
    letI : TopologicalSpace.MetrizableSpace X :=
      Manifold.metrizableSpace (realModel d) X
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    ∀ x : X, Nonempty (NativeAsymptoticLeafDatum (realModel d) f.toHomeomorph.symm
      a.splitting.unstable.toDistribution x) := by
  let : TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace (realModel d) X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨hmetric, hsmooth⟩ :=
    OneFormBundle.original_smooth_tangent_metric_exists (d := d) (M := X)
  obtain ⟨C, rate, hC, hrate, hs, hu⟩ :=
    OneFormBundle.original_all_iterates_hermitian f a hmetric hsmooth
  obtain ⟨s, t, hst, S, U, hranks, hSr, hUr, hfamily⟩ :=
    stableFoliations f hmetric hsmooth a.splitting C rate hC hrate hs hu
  intro x
  rcases hfamily with ⟨ιs, ιu, Ls, Lu, ts, tu, hfamily⟩
  let : ∀ i, TopologicalSpace (Ls i) := ts
  let : ∀ i, TopologicalSpace (Lu i) := tu
  rcases hfamily with ⟨cs, cu, hfamily⟩
  let : ∀ i, ChartedSpace (Fin (2 * s) → ℝ) (Ls i) := cs
  let : ∀ i, ChartedSpace (Fin (2 * t) → ℝ) (Lu i) := cu
  rcases hfamily with ⟨ms, mu, Fs, Fu, hsa, hua, hse, hue, hsi, hui,
    hboxes, hproducts, hsj, huj, hsc, huc⟩
  let : ∀ i, IsManifold 𝓘(ℝ, Fin (2 * s) → ℝ) ∞ (Ls i) := ms
  let : ∀ i, IsManifold 𝓘(ℝ, Fin (2 * t) → ℝ) ∞ (Lu i) := mu
  obtain ⟨i, a₀, ha₀⟩ := Fu.cover x
  have hrange : Set.range (Fu.leaf i).inclusion =
      {y | ForwardAsymptotic f.toHomeomorph.symm x y} := by
    simpa only [ha₀, Diffeomorph.coe_toHomeomorph_symm] using hua i a₀
  obtain ⟨N, hN, -⟩ := native_asymptotic_datum_of_leaf_g15
    a.splitting.unstable.toDistribution (Fu.leaf i) f.toHomeomorph.symm x hrange
  exact ⟨N⟩

end HolomorphicAnosov

