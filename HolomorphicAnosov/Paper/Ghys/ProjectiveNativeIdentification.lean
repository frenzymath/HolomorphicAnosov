import HolomorphicAnosov.Geometry.RealImmersionOfPointwiseIntoComplexModelG1
import HolomorphicAnosov.Ghys.DisconnectedNativeTransverseFoliations
import HolomorphicAnosov.Paper.Ghys.NativeUnstableComplexRankOneFromRealRankTwo
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeAsymptoticDatumOfLeaf
import HolomorphicAnosov.Geometry.ContinuousComplexRankOneSubbundle
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgradeOfComplexTangent
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Paper.Zhang.Anosov

/-! The stable and unstable foliations are identified with their asymptotic leaves through point-
preserving intrinsic charts. -/

noncomputable section
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

universe u

attribute [local instance] complex_isManifold_real

/-- A holomorphic Anosov map with real unstable rank two admits point-preserving intrinsic
identifications of its stable and unstable foliations with their asymptotic leaves. (Ghys, §2
pp.588–590, §5 p.597; Hirsch–Pugh–Shub, §§6B–7 pp.114–116) -/
theorem projective_native_identification
    {d : ℕ} {M : Type u} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (x₀ : M)
    (hu : ∀ x : M,
      Module.finrank ℝ (a.splitting.unstable.toDistribution x) = 2) :
    ∃ s : ℕ,
      ∃ _A : NativeTransverseAsymptoticIdentification.{u, u}
        f.toHomeomorph a.splitting.stable.toDistribution
        a.splitting.unstable.toDistribution s 2, True := by
  classical
  let : Nonempty M := ⟨x₀⟩
  have hRank := native_unstable_complex_rank_one_from_real_rank_two f a hu
  obtain ⟨B, F, ⟨hS, hU⟩, hNs, hNu⟩ :=
    disconnected_native_transverse_foliations f a rfl hRank
  let := realCoordinateRechart (M := M) B
  have hNativeS (w : M) :
      ∃ N : NativeAsymptoticLeafDatum (realModel d) f.toHomeomorph
          a.splitting.stable.toDistribution w,
        N.rank = 2 * d - 2 ∧
          (letI := N.topology; letI := N.charts
           letI := F.stableTopology (Quotient.mk F.stablePartition w)
           letI := F.stableCharts (Quotient.mk F.stablePartition w)
           ∃ e : Diffeomorph 𝓘(ℝ, Fin (2 * d - 2) → ℝ) 𝓘(ℝ, Fin N.rank → ℝ)
              (IntrinsicFoliationLeaf F.stablePartition (Quotient.mk F.stablePartition w))
              (StableAsymptoticLeaf f.toHomeomorph w) ∞,
             ∀ z, (e z).val = z.val) := by
    let q := Quotient.mk F.stablePartition w
    let := F.stableTopology q
    let := F.stableCharts q
    obtain ⟨smooth, N, heq⟩ := hNs q
    let := smooth
    have hrange : Set.range N.inclusion =
        {z | ForwardAsymptotic f.toHomeomorph w z} := by
      rw [heq]
      ext z
      constructor
      · rintro ⟨v, rfl⟩
        exact (hS w v.val).mp (Quotient.exact v.property.symm)
      · intro hz
        exact ⟨⟨z, (Quotient.sound ((hS w z).mpr hz)).symm⟩, rfl⟩
    obtain ⟨N', hN, e, he⟩ := native_asymptotic_datum_of_leaf_g15
      a.splitting.stable.toDistribution N f.toHomeomorph w hrange
    refine ⟨N', hN, e, ?_⟩
    intro z
    simpa only [heq] using he z
  have hNativeU (w : M) :
      ∃ N : NativeAsymptoticLeafDatum (realModel d) f.toHomeomorph.symm
          a.splitting.unstable.toDistribution w,
        N.rank = 2 ∧
          (letI := N.topology; letI := N.charts
           letI := F.unstableTopology (Quotient.mk F.unstablePartition w)
           letI := F.unstableCharts (Quotient.mk F.unstablePartition w)
           ∃ e : Diffeomorph 𝓘(ℝ, Fin (2) → ℝ) 𝓘(ℝ, Fin N.rank → ℝ)
              (IntrinsicFoliationLeaf F.unstablePartition (Quotient.mk F.unstablePartition w))
              (StableAsymptoticLeaf f.toHomeomorph.symm w) ∞,
             ∀ z, (e z).val = z.val) := by
    let q := Quotient.mk F.unstablePartition w
    let := F.unstableTopology q
    let := F.unstableCharts q
    obtain ⟨smooth, N, heq⟩ := hNu q
    let := smooth
    have hrange : Set.range N.inclusion =
        {z | ForwardAsymptotic f.toHomeomorph.symm w z} := by
      rw [heq]
      ext z
      constructor
      · rintro ⟨v, rfl⟩
        exact (hU w v.val).mp (Quotient.exact v.property.symm)
      · intro hz
        exact ⟨⟨z, (Quotient.sound ((hU w z).mpr hz)).symm⟩, rfl⟩
    obtain ⟨N', hN, e, he⟩ := native_asymptotic_datum_of_leaf_g15
      a.splitting.unstable.toDistribution N f.toHomeomorph.symm w hrange
    refine ⟨N', hN, e, ?_⟩
    intro z
    simpa only [heq] using he z
  choose Ns hNs eS heS using hNativeS
  choose Nu hNu eU heU using hNativeU
  obtain ⟨S, T, hT, _, hreal⟩ :=
    exists_continuous_complex_rank_one_subbundle a.splitting.unstable hRank
  have hUpgrade (w : M)
      (N : NativeUnstableAsymptoticLeafDatum (realModel d) f.toHomeomorph
        a.splitting.unstable.toDistribution w) (hr : N.rank = 2) :
      letI := N.topology
      letI := N.charts
      Nonempty (NativeLeafComplexUpgrade (d := d) (r := N.rank) 1
        (Subtype.val : UnstableAsymptoticLeaf f.toHomeomorph w → M)) := by
    rcases N with ⟨r, top, charts, haus, second, conn, smooth, hsmooth, himm, ht⟩
    change r = 2 at hr
    subst r
    let := top
    let := charts
    let := smooth
    apply nativeLeafComplexUpgrade_of_complex_tangent (k := 1)
      Subtype.val a.splitting.unstable
      (real_immersion_of_pointwise_into_complex_model_g1 himm) ht T
    intro z
    rw [ht, hT]
    exact hreal z.val
  refine ⟨2*d-2, {
    realCoordinates := B
    F := F
    nativeS := Ns
    nativeU := Nu
    rankS := hNs
    rankU := hNu
    complexU1 := fun x ↦ Classical.choice (hUpgrade x (Nu x) (hNu x))
    stableIdentification := eS
    stable_points := heS
    unstableIdentification := eU
    unstable_points := heU }, trivial⟩



end HolomorphicAnosov.Ghys
