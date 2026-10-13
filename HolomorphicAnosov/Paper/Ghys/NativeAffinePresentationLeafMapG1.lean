import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeBijectiveInverseContmdiff
import HolomorphicAnosov.Geometry.ContinuousUnstableLeafLiftG1
import HolomorphicAnosov.Geometry.ComplexDerivativeInjectiveOfRealCharts
import HolomorphicAnosov.Geometry.ComplexHolomorphicImmersionOfInjectiveDerivative
import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation

/-! This file proves holomorphicity of point-preserving comparisons between native and supplied
intrinsic unstable leaves, and biholomorphicity when the comparisons are bijective. (HPS, §7,
pp. 115–116; Ghys, Prop. 3.1, pp. 590–593) -/
noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- The point-preserving comparison from a native complex unstable leaf to a supplied intrinsic leaf
is holomorphic. (HPS, §7, pp. 115–116; Ghys, Prop. 3.1) -/
theorem native_affine_presentation_leaf_map_holomorphic_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (i : ι) :
    letI := P.realCharts
    ∀ q : Quotient P.foliations.unstablePartition,
    letI := P.foliations.unstableTopology q
    letI := P.complexLeaves.charts q
    ∀ (g : L i → IntrinsicFoliationLeaf P.foliations.unstablePartition q),
      (∀ z, (g z).val = (U.leaf i).inclusion z) →
      ContMDiff 𝓘(ℂ) (complexModel 1) ∞ g := by
  let := P.realCharts
  intro q
  let := P.foliations.unstableTopology q
  let := P.foliations.unstableCharts q
  let := P.unstableSmooth q
  let := P.complexLeaves.charts q
  let := P.complexLeaves.complex_manifold q
  intro g hg
  let : SecondCountableTopology
      (IntrinsicFoliationLeaf P.foliations.unstablePartition q) := (P.unstableNative q).countable
  let : LocallyConnectedSpace (L i) := ChartedSpace.locallyConnectedSpace ℂ (L i)
  have hcont : Continuous g := by
    apply continuous_unstable_leaf_lift_g1 P.foliations q inferInstance g
    exact (G.holomorphic_inclusion i).1.continuous.congr (fun z ↦ (hg z).symm)
  intro z
  have hderiv : Function.Injective (mfderiv (complexModel 1) (complexModel d)
      (Subtype.val : IntrinsicFoliationLeaf P.foliations.unstablePartition q → M) (g z)) := by
    apply complexDerivative_injective_of_compatible_real_charts (r := 2)
    · exact ((P.unstable_real_complex_compatible q).1 (g z)).mdifferentiableAt (by simp)
    · exact ((P.unstable_real_complex_compatible q).2 (g z)).mdifferentiableAt (by simp)
    · exact (P.unstable_holomorphic q (g z)).mdifferentiableAt (by simp)
    · rw [← P.unstable_inclusion_eq q]
      exact (P.unstableNative q).immersion.mfderiv_injective (by simp) (g z)
  have himm := complex_holomorphic_immersion_of_injective_derivative
    ((P.unstable_holomorphic q).contMDiffAt (x := g z)) hderiv
  apply (ContMDiffAt.iff_comp_isImmersionAt himm).mpr
  refine ⟨hcont.continuousAt, ?_⟩
  have heq : (Subtype.val : IntrinsicFoliationLeaf P.foliations.unstablePartition q → M) ∘ g =
      (U.leaf i).inclusion := funext hg
  rw [heq]
  exact (G.holomorphic_inclusion i).1 z

/-- A point-preserving bijection from a native unstable leaf to a supplied intrinsic unstable leaf
is biholomorphic. (Ghys, Prop. 3.1) -/
theorem native_affine_presentation_leaf_equiv_biholomorphic_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (i : ι) :
    letI := P.realCharts
    ∀ q : Quotient P.foliations.unstablePartition,
    letI := P.foliations.unstableTopology q
    letI := P.complexLeaves.charts q
    ∀ (e : L i ≃ IntrinsicFoliationLeaf P.foliations.unstablePartition q),
      (∀ z, (e z).val = (U.leaf i).inclusion z) →
      ∃ E : Diffeomorph 𝓘(ℂ) (complexModel 1) (L i)
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞,
        E.toEquiv = e := by
  let := P.realCharts
  intro q
  let := P.foliations.unstableTopology q
  let := P.complexLeaves.charts q
  let := P.complexLeaves.complex_manifold q
  intro e he
  have hs := native_affine_presentation_leaf_map_holomorphic_g1 f a P L U G i q e he
  have hb (z : L i) : Function.Bijective (mfderiv 𝓘(ℂ) (complexModel 1) e z) := by
    have heq : (Subtype.val : IntrinsicFoliationLeaf P.foliations.unstablePartition q → M) ∘ e =
        (U.leaf i).inclusion := funext he
    have hd := mfderiv_comp z
      ((P.unstable_holomorphic q (e z)).mdifferentiableAt (by simp))
      ((hs z).mdifferentiableAt (by simp))
    rw [heq] at hd
    have hinj : Function.Injective (mfderiv 𝓘(ℂ) (complexModel 1) e z) := by
      intro v w hvw
      apply (G.holomorphic_inclusion i).2 z
      rw [hd]
      exact congrArg (mfderiv (complexModel 1) (complexModel d)
        (Subtype.val : IntrinsicFoliationLeaf P.foliations.unstablePartition q → M) (e z)) hvw
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      change Module.finrank ℂ ℂ = Module.finrank ℂ (Fin 1 → ℂ)
      simp)).mp hinj
  exact ⟨{ e with
    contMDiff_toFun := hs
    contMDiff_invFun := native_bijective_inverse_contMDiff 𝓘(ℂ) (complexModel 1) e hs hb }, rfl⟩

end HolomorphicAnosov.Ghys

