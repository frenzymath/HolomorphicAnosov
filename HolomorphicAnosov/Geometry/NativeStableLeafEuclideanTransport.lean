import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExists
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalAllIteratesHermitian
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.ContinuousStableLeafLiftG9
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.ManifoldInverse
import Mathlib.Geometry.Manifold.Immersion
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
/-- A continuous point-preserving equivalence between smooth immersed leaves with identical tangent
images yields a diffeomorphism. (HPS, §7, pp. 115–116) -/
theorem immersed_leaf_equivalence_diffeomorph
    {r s : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L K M : Type*}
    [TopologicalSpace L] [TopologicalSpace K] [TopologicalSpace M]
    [ChartedSpace (Fin r → ℝ) L] [ChartedSpace (Fin s → ℝ) K]
    [ChartedSpace (V) M]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ K]
    [IsManifold 𝓘(ℝ, V) ∞ M]
    (j : L → M) (k : K → M)
    (hj : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, V) ∞ j)
    (hk : ContMDiff 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, V) ∞ k)
    (hji : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, V) j x))
    (hki : ∀ y, Manifold.IsImmersionAt 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, V) ∞ k y)
    (e : L ≃ K) (hc : Continuous e) (he : k ∘ e = j)
    (hr : ∀ x, LinearMap.range (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, V) j x).toLinearMap =
      LinearMap.range (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, V) k (e x)).toLinearMap) :
    Nonempty (Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) L K ∞) := by
  have hs : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) ∞ e := by
    intro x
    apply (ContMDiffAt.iff_comp_isImmersionAt (hki (e x))).mpr
    exact ⟨hc.continuousAt, he ▸ hj.contMDiffAt⟩
  have hb (x : L) : Function.Bijective (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) e x) := by
    have hd := mfderiv_comp x ((hk (e x)).mdifferentiableAt (by simp))
      ((hs x).mdifferentiableAt (by simp))
    rw [he] at hd
    have hi := (hki (e x)).mfderiv_injective (by simp)
    constructor
    · intro v w h
      apply hji x
      rw [hd]
      exact congrArg (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, V) k (e x)) h
    · intro w
      have hm : (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, V) k (e x)) w ∈
          LinearMap.range (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, V) j x).toLinearMap := by
        rw [hr x]
        exact ⟨w, rfl⟩
      obtain ⟨v, hv⟩ := hm
      refine ⟨v, hi ?_⟩
      rw [hd] at hv
      exact hv
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) ∞ e := by
    intro x
    let a := (LinearEquiv.ofBijective
      (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) e x).toLinearMap (hb x)).toContinuousLinearEquiv
    have ha : mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) e x = a.toContinuousLinearMap := by
      ext v
      rfl
    obtain ⟨q, hx, _, heq⟩ := W07ManifoldInverseFunction.exists_partialDiffeomorph
      isOpen_univ (Set.mem_univ x) hs.contMDiffOn a ha
    exact ⟨q, hx, heq⟩
  exact ⟨hlocal.diffeomorphOfBijective e.bijective⟩
end HolomorphicAnosov

namespace HolomorphicAnosov
universe u
/-- A Euclidean parametrization of a native stable leaf gives a Euclidean homeomorphism for any
native presentation of the same stable carrier. (HPS, §7, pp. 115–116; Ghys, p. 598) -/
theorem native_stable_leaf_euclidean_of_parametrization
    {d s t r : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification f Ps Pu s t) (x : M)
    {L : Type u} [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (leaf : HPS.NativeLeaf (r := r) Ps L)
    (hrange : Set.range leaf.inclusion = {y | ForwardAsymptotic f x y})
    (param : (Fin r → ℝ) ≃ₜ L) :
    letI := A.realAmbientCharts
    Nonempty ((IntrinsicFoliationLeaf A.F.stablePartition
      (Quotient.mk A.F.stablePartition x)) ≃ₜ (Fin r → ℝ)) := by
  classical
  let := A.realAmbientCharts
  let := (A.nativeS x).topology
  let := (A.nativeS x).charts
  let := (A.nativeS x).smoothAtlas
  let := (A.nativeS x).secondCountable
  let T := IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)
  let H := A.stableClassHomeomorph x
  let e : L ≃ StableAsymptoticLeaf f x := Equiv.ofBijective
    (fun z ↦ ⟨leaf.inclusion z, by
      have hz : leaf.inclusion z ∈ Set.range leaf.inclusion := Set.mem_range_self z
      rwa [hrange] at hz⟩)
    ⟨fun a b h ↦ leaf.injective (congrArg Subtype.val h), fun z ↦ by
      have hz : z.val ∈ Set.range leaf.inclusion := hrange.symm ▸ z.property
      obtain ⟨a, ha⟩ := hz
      exact ⟨a, Subtype.ext ha⟩⟩
  have he (z : L) : (e z).val = leaf.inclusion z := rfl
  have hH (z : T) : (H z).val = z.val := A.stable_points x z
  have hHs (z : StableAsymptoticLeaf f x) : (H.symm z).val = z.val := by
    simpa only [Homeomorph.apply_symm_apply] using (hH (H.symm z)).symm
  let : SecondCountableTopology T := H.secondCountableTopology
  let : LocallyConnectedSpace L := ChartedSpace.locallyConnectedSpace (Fin r → ℝ) L
  have hcont : Continuous (H.symm ∘ e) := by
    apply continuous_stable_leaf_lift_g9 A.F _ inferInstance
    exact leaf.immersion.contMDiff.continuous.congr (fun z ↦ (hHs (e z)).symm)
  have hecont : Continuous e := by
    convert H.continuous.comp hcont using 1
    funext z
    exact (H.apply_symm_apply (e z)).symm
  obtain ⟨E⟩ := immersed_leaf_equivalence_diffeomorph leaf.inclusion
    (Subtype.val : StableAsymptoticLeaf f x → M) leaf.immersion.contMDiff
    (A.nativeS x).inclusion_smooth (leaf.immersion.mfderiv_injective (by simp))
    (A.nativeS x).inclusion_immersion e hecont (funext he) (fun z ↦ by
      rw [leaf.tangent, (A.nativeS x).tangent_image]
      rfl)
  exact ⟨H.trans (E.toHomeomorph.symm.trans param.symm)⟩
end HolomorphicAnosov

namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
/-- For an Anosov map with complex unstable rank one, the intrinsic stable leaf is homeomorphic to
Euclidean space of dimension equal to the ambient real dimension minus two. (Zhang, Prop. 2.9;
Ghys, p. 598) -/
theorem native_stable_leaf_euclidean_of_anosov
    {d s : ℕ} {M : Type*} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hu : ∀ x, Module.finrank ℝ (a.splitting.unstable.toDistribution x) = 2)
    (A : NativeTransverseAsymptoticIdentification f.toHomeomorph
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution s 2)
    (x : M) :
    letI := A.realAmbientCharts
    ∃ r : ℕ, 2*r+2=2*d ∧ Nonempty ((IntrinsicFoliationLeaf A.F.stablePartition
      (Quotient.mk A.F.stablePartition x)) ≃ₜ (Fin (2*r) → ℝ)) := by
  let := A.realAmbientCharts
  obtain ⟨hmetric, hsmooth⟩ := OneFormBundle.original_smooth_tangent_metric_exists (d := d) (M := M)
  obtain ⟨C₁, rate, hC₁, hrate, hs, hu'⟩ :=
    OneFormBundle.original_all_iterates_hermitian f a hmetric hsmooth
  obtain ⟨r, t, hrt, S, U, hranks, hSr, hUr, hfamily⟩ :=
    stableFoliations f hmetric hsmooth a.splitting C₁ rate hC₁ hrate hs hu'
  have ht := hu x
  rw [← hUr x, (complexTangentToReal d x).toLinearEquiv.finrank_map_eq,
    (((U.toDistribution x).restrictScalarsEquiv ℝ).restrictScalars ℝ).finrank_eq,
    finrank_real_of_complex, (hranks x).2] at ht
  have hdim : 2 * r + 2 = 2 * d := by omega
  rcases hfamily with ⟨ιs, ιu, Ls, Lu, ts, tu, hfamily⟩
  let : ∀ i, TopologicalSpace (Ls i) := ts
  let : ∀ i, TopologicalSpace (Lu i) := tu
  rcases hfamily with ⟨cs, cu, hfamily⟩
  let : ∀ i, ChartedSpace (Fin (2 * r) → ℝ) (Ls i) := cs
  let : ∀ i, ChartedSpace (Fin (2 * t) → ℝ) (Lu i) := cu
  rcases hfamily with ⟨ms, mu, Fs, Fu, hsa, hua, hse, hue, hsi, hui,
    hboxes, hproducts, hsj, huj, hsc, huc⟩
  let : ∀ i, IsManifold 𝓘(ℝ, Fin (2 * r) → ℝ) ∞ (Ls i) := ms
  let : ∀ i, IsManifold 𝓘(ℝ, Fin (2 * t) → ℝ) ∞ (Lu i) := mu
  obtain ⟨i, a₀, ha₀⟩ := Fs.cover x
  have hrange : Set.range (Fs.leaf i).inclusion =
      {y | ForwardAsymptotic f.toHomeomorph x y} := by
    simpa only [ha₀, Diffeomorph.coe_toHomeomorph] using hsa i a₀
  obtain ⟨param⟩ := hse i
  obtain ⟨K⟩ := native_stable_leaf_euclidean_of_parametrization A x
    (Fs.leaf i) hrange param.toHomeomorph
  exact ⟨r, hdim, ⟨K⟩⟩
end HolomorphicAnosov
