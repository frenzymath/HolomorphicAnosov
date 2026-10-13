import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Ghys.OpenComponentTangentTransportG12
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalAllIteratesHermitian
import HolomorphicAnosov.Geometry.ComplexHolomorphicImmersionOfInjectiveDerivative
import HolomorphicAnosov.Ghys.CurveScalarIsManifoldComplex
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.HasComplexRankOne_real_finrank_eq_two
import HolomorphicAnosov.Ghys.DisconnectedComponentResidues
import HolomorphicAnosov.Ghys.ConnectedComponentComplexIterate
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExistsNoConnected
import HolomorphicAnosov.Ghys.AffineCompletenessIntrinsicPlaqueLiftProviderG12
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeBijectiveInverseContmdiff


noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace


theorem affine_completeness_intrinsic_carrier_comparison_provider
    {d : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι) :
    Nonempty (L i ≃ₜ (Fin 2 → ℝ)) := by
  classical
  let : ConnectedSpace (L i) := (U.leaf i).connected
  let z₀ : L i := Classical.choice inferInstance
  let x₀ : M := (U.leaf i).inclusion z₀
  obtain ⟨m, hm, hG⟩ := G.asymptotic
  let : MetricSpace M := m.replaceTopology hm.symm
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel d) M
  obtain ⟨N, hN, hcomponent, hforward, hbackward⟩ :=
    disconnected_component_residue_bridge f.toHomeomorph
  let K : TopologicalSpace.Opens M := ⟨connectedComponent x₀, isOpen_connectedComponent⟩
  let : Nonempty K := ⟨⟨x₀, mem_connectedComponent⟩⟩
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : CompactSpace K := isCompact_iff_compactSpace.mp (show IsCompact (K : Set M) from isClosed_connectedComponent.isCompact)
  let : IsCompactComplexManifold d K := {}
  have hmaps := iterate_mapsTo_connectedComponent f.toHomeomorph N hcomponent x₀
  let g : Biholomorph d d K K := restricted_open_biholomorph
    (complexDiffeomorphIterate f N) K inferInstance
    (by simpa [coe_complexDiffeomorphIterate, K] using hmaps.1)
    (by simpa [coe_complexDiffeomorphIterate_symm, K] using hmaps.2)
  have hg (x : K) : (g x).val = (f : M → M)^[N] x.val := by
    change complexDiffeomorphIterate f N x.val = _
    rw [coe_complexDiffeomorphIterate]
  have hgi (x : K) : (g.symm x).val = (f.symm : M → M)^[N] x.val := by
    change (complexDiffeomorphIterate f N).symm x.val = _
    rw [coe_complexDiffeomorphIterate_symm]
  have hgn (n : ℕ) (x : K) : ((g : K → K)^[n] x).val =
      (f : M → M)^[N*n] x.val := by
    have hh : Function.Semiconj (Subtype.val : K → M) g ((f : M → M)^[N]) := hg
    simpa only [Function.iterate_mul] using hh.iterate_right n x
  have hgin (n : ℕ) (x : K) : ((g.symm : K → K)^[n] x).val =
      (f.symm : M → M)^[N*n] x.val := by
    have hh : Function.Semiconj (Subtype.val : K → M) g.symm ((f.symm : M → M)^[N]) := hgi
    simpa only [Function.iterate_mul] using hh.iterate_right n x
  let P := a.splitting.restrictOpenIterate f.toReal K N g.toReal hg
  obtain ⟨h, hh⟩ := OneFormBundle.original_smooth_tangent_metric_exists_no_connected (d := d) (M := M)
  obtain ⟨C, rate, hC, hrate, hs, hu⟩ := OneFormBundle.original_all_iterates_hermitian f a h hh
  let hK : HermitianTangentMetricCore d K := fun x ↦ h x.val
  have hhK : IsSmoothHermitianTangentMetric hK := smooth_hermitian_restrict_open K h hh
  have hsr : ∀ n : ℕ, ∀ x : K, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.stable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing hK ((g : K → K)^[n] x)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) g.toReal n) x v)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) g.toReal n) x v)) ≤
        C * (rate ^ N) ^ n * Real.sqrt (hermitianTangentRealPairing hK x v v) := by
    intro n x v hv
    have hd := open_component_mfderiv_restrict K ((f : M → M)^[N*n])
      ((g : K → K)^[n]) (f.toReal.contMDiff.iterate (N*n)) (g.toReal.contMDiff.iterate n) (hgn n) x
    have hv' : v ∈ a.splitting.stable.toDistribution x.val := hv
    have hb := hs (N*n) x.val v hv'
    change Real.sqrt (hermitianTangentRealPairing h (((g : K → K)^[n] x).val)
      (mfderiv (realModel d) (realModel d) ((g : K → K)^[n]) x v)
      (mfderiv (realModel d) (realModel d) ((g : K → K)^[n]) x v)) ≤
      C * (rate ^ N) ^ n * Real.sqrt (hermitianTangentRealPairing h x.val v v)
    rw [hd, hgn, ← pow_mul]
    exact hb
  have hur : ∀ n : ℕ, ∀ x : K, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.unstable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing hK ((g.symm : K → K)^[n] x)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) g.toReal.symm n) x v)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) g.toReal.symm n) x v)) ≤
        C * (rate ^ N) ^ n * Real.sqrt (hermitianTangentRealPairing hK x v v) := by
    intro n x v hv
    have hd := open_component_mfderiv_restrict K ((f.symm : M → M)^[N*n])
      ((g.symm : K → K)^[n]) (f.toReal.symm.contMDiff.iterate (N*n)) (g.toReal.symm.contMDiff.iterate n) (hgin n) x
    have hv' : v ∈ a.splitting.unstable.toDistribution x.val := hv
    have hb := hu (N*n) x.val v hv'
    change Real.sqrt (hermitianTangentRealPairing h (((g.symm : K → K)^[n] x).val)
      (mfderiv (realModel d) (realModel d) ((g.symm : K → K)^[n]) x v)
      (mfderiv (realModel d) (realModel d) ((g.symm : K → K)^[n]) x v)) ≤
      C * (rate ^ N) ^ n * Real.sqrt (hermitianTangentRealPairing h x.val v v)
    rw [hd, hgin, ← pow_mul]
    exact hb
  have hrN : 0 < rate ^ N ∧ rate ^ N < 1 :=
    ⟨pow_pos hrate.1 _, pow_lt_one₀ hrate.1.le hrate.2 (Nat.ne_of_gt hN)⟩
  obtain ⟨s, t, hst, S, V, hrank, hS, hV, ιs, ιu, Ls, Lu, ts, tu, cs, cu, ms, mu,
    Fs, Fu, hFs, hFu, hEs, hEu, hrest⟩ := stableFoliations g hK hhK P C (rate ^ N) hC hrN hsr hur
  let := ts
  let := tu
  let := cs
  let := cu
  let := ms
  let := mu
  let xK : K := ⟨x₀, mem_connectedComponent⟩
  have ht : t = 1 := by
    have ht' : Module.finrank ℝ (P.unstable.toDistribution xK) = 2 * t := by
      rw [← hV xK, LinearEquiv.finrank_map_eq (complexTangentToReal d xK).toLinearEquiv]
      change Module.finrank ℝ (V.toDistribution xK) = 2 * t
      rw [finrank_real_of_complex, (hrank xK).2]
    have htwo := TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two G.rankOne x₀
    change Module.finrank ℝ (a.splitting.unstable.toDistribution x₀) = 2 * t at ht'
    omega
  subst t
  obtain ⟨j, w, hw⟩ := Fu.cover xK
  let J : Lu j → M := fun z ↦ ((Fu.leaf j).inclusion z).val
  have hJ : Function.Injective J := Subtype.val_injective.comp (Fu.leaf j).injective
  have hJc : Continuous J := continuous_subtype_val.comp (Fu.leaf j).immersion.contMDiff.continuous
  have horig (y : M) : y ∈ Set.range (U.leaf i).inclusion ↔
      ForwardAsymptotic f.symm x₀ y := hG i z₀ y
  have hKrange : Set.range (U.leaf i).inclusion ⊆ (K : Set M) :=
    (isPreconnected_range (U.leaf i).immersion.contMDiff.continuous).subset_connectedComponent
      (mem_range_self z₀)
  have hass (x y : K) : ForwardAsymptotic g.symm x y ↔
      ForwardAsymptotic f.symm x.val y.val := by
    refine Iff.trans ?_ (hbackward x.val y.val)
    change ForwardAsymptotic g.symm x y ↔
      ForwardAsymptotic ((f.symm : M → M)^[N]) x.val y.val
    unfold ForwardAsymptotic
    have heq : (fun n : ℕ ↦ dist ((g.symm : K → K)^[n] y) ((g.symm : K → K)^[n] x)) =
        (fun n : ℕ ↦ dist ((((f.symm : M → M)^[N])^[n]) y.val)
          ((((f.symm : M → M)^[N])^[n]) x.val)) := by
      funext n
      change dist (((g.symm : K → K)^[n] y).val) (((g.symm : K → K)^[n] x).val) = _
      rw [hgin, hgin, Function.iterate_mul]
    rw [heq]
  have hrange : Set.range J = Set.range (U.leaf i).inclusion := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, rfl⟩
      apply (horig _).mpr
      have hh : ForwardAsymptotic g.symm ((Fu.leaf j).inclusion w) ((Fu.leaf j).inclusion z) := by
        change ((Fu.leaf j).inclusion z) ∈ {y | ForwardAsymptotic g.symm ((Fu.leaf j).inclusion w) y}
        rw [← hFu j w]
        exact mem_range_self z
      rw [hw] at hh
      exact (hass xK ((Fu.leaf j).inclusion z)).mp hh
    · intro y hy
      let yK : K := ⟨y, hKrange hy⟩
      have hh : ForwardAsymptotic g.symm ((Fu.leaf j).inclusion w) yK := by
        rw [hw]
        exact (hass xK yK).mpr ((horig y).mp hy)
      have hy' : yK ∈ Set.range (Fu.leaf j).inclusion := by
        rw [hFu j w]
        exact hh
      obtain ⟨z, hz⟩ := hy'
      exact ⟨z, congrArg Subtype.val hz⟩
  let e : Lu j ≃ L i := ((Equiv.ofInjective J hJ).trans (Set.equivOfEq hrange)).trans
    (Equiv.ofInjective (U.leaf i).inclusion (U.leaf i).injective).symm
  have he (z : Lu j) : (U.leaf i).inclusion (e z) = J z := by
    exact Equiv.apply_ofInjective_symm (U.leaf i).injective
      (Set.equivOfEq hrange ((Equiv.ofInjective J hJ) z))
  let : LocallyConnectedSpace (Lu j) := ChartedSpace.locallyConnectedSpace (Fin 2 → ℝ) (Lu j)
  have hec : Continuous e := affine_completeness_intrinsic_plaque_lift_continuous_provider
    f a L U G i e (hJc.congr (fun z ↦ (he z).symm))
  rcases hrest with ⟨_, _, _, _, _, _, _, hcomplex⟩
  obtain ⟨cj, mj, hjimm, upgrade, hupgrade, hjrange⟩ := hcomplex j
  let := cj
  let := mj
  have hjhol : ContMDiff (complexModel 1) (complexModel d) ∞ J :=
    (contMDiff_subtype_val (I := complexModel d) (n := ∞)).comp hjimm.contMDiff
  let : IsManifold (complexModel 1) ∞ (L i) := curve_scalar_is_manifold_complex
  let Q : Diffeomorph (complexModel 1) 𝓘(ℂ) (L i) (L i) ∞ :=
    { toEquiv := Equiv.refl _
      contMDiff_toFun := curveProductToScalar_contMDiff_id (L i)
      contMDiff_invFun := curveScalarToProduct_contMDiff_id (L i) }
  have hLis : ContMDiff (complexModel 1) (complexModel d) ∞ (U.leaf i).inclusion :=
    (G.holomorphic_inclusion i).1.comp Q.contMDiff
  have hLiDer (z : L i) : Function.Injective
      (mfderiv (complexModel 1) (complexModel d) (U.leaf i).inclusion z) := by
    have hh := mfderiv_comp z ((G.holomorphic_inclusion i).1.mdifferentiableAt (by simp))
      (Q.contMDiff.mdifferentiableAt (by simp))
    change mfderiv (complexModel 1) (complexModel d) (U.leaf i).inclusion z = _ at hh
    rw [hh]
    exact ((G.holomorphic_inclusion i).2 z).comp (Q.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hLiImm (z : L i) : Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
      (U.leaf i).inclusion z :=
    complex_holomorphic_immersion_of_injective_derivative (hLis z) (hLiDer z)
  have hes : ContMDiff (complexModel 1) (complexModel 1) ∞ e := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt (hLiImm (e z))).mpr
    refine ⟨hec.continuousAt, ?_⟩
    have heq : (U.leaf i).inclusion ∘ e = J := funext he
    rw [heq]
    exact hjhol z
  have heder (z : Lu j) : Function.Bijective (mfderiv (complexModel 1) (complexModel 1) e z) := by
    have hcomp := mfderiv_comp z (hLis.mdifferentiableAt (by simp))
      (hes.mdifferentiableAt (by simp))
    have heq : (U.leaf i).inclusion ∘ e = J := funext he
    rw [heq] at hcomp
    have hJinj : Function.Injective (mfderiv (complexModel 1) (complexModel d) J z) := by
      have hcompJ := mfderiv_comp z
        ((contMDiff_subtype_val (I := complexModel d) (n := ∞)).mdifferentiableAt (by simp))
        (hjimm.contMDiff.mdifferentiableAt (by simp))
      change Function.Injective (mfderiv (complexModel 1) (complexModel d)
        ((Subtype.val : K → M) ∘ (Fu.leaf j).inclusion) z)
      rw [hcompJ]
      exact (openSubsetInclusion_mfderiv_bijective (complexModel d) K _).1.comp
        ((hjimm.isImmersionAt z).mfderiv_injective (by simp))
    have hinj : Function.Injective (mfderiv (complexModel 1) (complexModel 1) e z) := by
      intro v w hvw
      apply hJinj
      rw [hcomp]
      exact congrArg (mfderiv (complexModel 1) (complexModel d) (U.leaf i).inclusion (e z)) hvw
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by change Module.finrank ℂ (Fin 1 → ℂ) = Module.finrank ℂ (Fin 1 → ℂ); simp)).mp hinj⟩
  have hei := native_bijective_inverse_contMDiff (complexModel 1) (complexModel 1) e hes heder
  let H : Lu j ≃ₜ L i := { e with continuous_toFun := hec, continuous_invFun := hei.continuous }
  obtain ⟨R⟩ := hEu j
  exact ⟨H.symm.trans R.toHomeomorph.symm⟩

end HolomorphicAnosov.Ghys
