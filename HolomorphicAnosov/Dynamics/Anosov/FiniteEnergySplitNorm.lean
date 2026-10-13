import HolomorphicAnosov.Dynamics.Anosov.FiniteWeightedEnergy
import HolomorphicAnosov.Dynamics.Anosov.InverseDistributionInvariant
import HolomorphicAnosov.Geometry.HPSRealAnosovEstimateDataG8
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Projection
import Mathlib.Geometry.Manifold.Riemannian.Basic

open scoped ContDiff Manifold Topology _root_.Topology Bundle ENNReal
open TopologicalSpace Set

universe u
namespace HolomorphicAnosov.HPS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- The finite-energy adapted product norm for the original stable and unstable splitting.

Source: Hirsch--Pugh--Shub, Invariant Manifolds (1977), (2.8)--(2.9), pp.13--15,
and the finite-sum remark on p.14; the product maximum norm is the GL1 expansion
of `g9.hps_anosov_global_lamination`. The original tangent norms and ambient
Riemannian distance are retained. Continuity is proved for the two summand
energies on the original tangent bundle; no continuity of the complementary
projection or uniform upper bound for the product norm is asserted here.

Proof: Choose λ < θ < 1 and one N ≥ 1 with C λ^N < θ^N. Sum the original
forward, respectively inverse, squared derivative norms with weights θ^(-2j),
0 ≤ j < N. The finite-energy shift identity and chain rule give one-step
contraction by θ². The zero term bounds the original squared norm below, and
the original C λ^j estimates give a common finite upper coefficient on each
summand. These sums are positive symmetric bilinear forms; their square roots
are continuous, homogeneous and satisfy the triangle inequality by Mathlib's
inner-product core construction. Decompose each vector uniquely along the
complementary subspaces and take the maximum of the two energies. The original
triangle inequality gives ‖v‖ ≤ 2ν(v), so this function is definite. The maximum
preserves the triangle inequality and absolute homogeneity. On each summand it
equals that summand's energy; derivative invariance and its inverse version give
both one-step contraction estimates. The construction also covers zero-rank
summands and the empty base without a choice from a unit sphere. -/
theorem anosov_finite_energy_split_norm
    [FiniteDimensional ℝ E] (X : Type u) [EMetricSpace X] [CompactSpace X]
    [SecondCountableTopology X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
    [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E
      (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsRiemannianManifold 𝓘(ℝ, E) X]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X X ∞)
    (S : InvariantRealTangentSplitting f) (h : BundleAnosovBounds f S) :
    ∃ (θ K : ℝ) (νs νu ν : ∀ x : X, TangentSpace 𝓘(ℝ, E) x → ℝ),
      0 < θ ∧ θ < 1 ∧ 0 ≤ K ∧
      Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ νs p.proj p.2) ∧
      Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ νu p.proj p.2) ∧
      (∀ x (v : S.stable.toDistribution x), νs x v ≤ K * ‖v.val‖) ∧
      (∀ x (v : S.unstable.toDistribution x), νu x v ≤ K * ‖v.val‖) ∧
      (∀ x v, ν x v =
        let w := (Submodule.prodEquivOfIsCompl (S.stable.toDistribution x)
          (S.unstable.toDistribution x) (S.isCompl x)).symm v
        max (νs x w.1) (νu x w.2)) ∧
      (∀ x, ν x 0 = 0) ∧
      (∀ x v w, ν x (v + w) ≤ ν x v + ν x w) ∧
      (∀ x (c : ℝ) v, ν x (c • v) = ‖c‖ * ν x v) ∧
      (∀ x v, ‖v‖ ≤ 2 * ν x v) ∧
      (∀ x (v : S.stable.toDistribution x),
        ν (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤ θ * ν x v) ∧
      (∀ x (v : S.unstable.toDistribution x),
        ν (f.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤ θ * ν x v) := by
  -- GL1: one uniform finite horizon for both original derivative cocycles.
  obtain ⟨C, lam, hC, hlam, hlam1, hs, hu⟩ := h
  let θ : ℝ := (lam + 1) / 2
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hlamθ : lam < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  have hdecay : Filter.Tendsto (fun n : ℕ ↦ C * (lam / θ) ^ n)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hlam.le hθ.le) ((div_lt_one hθ).mpr hlamθ)).const_mul C
  obtain ⟨N, hN, hsmall⟩ : ∃ N : ℕ, 1 ≤ N ∧ C * (lam / θ) ^ N < 1 :=
    ((Filter.eventually_ge_atTop 1).and (hdecay.eventually (gt_mem_nhds zero_lt_one))).exists
  have hblock : C * lam ^ N < θ ^ N := by
    apply (div_lt_one (pow_pos hθ N)).mp
    simpa only [div_pow, mul_div_assoc] using hsmall
  have hsblock (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.stable.toDistribution x) :
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f N) x v‖ ≤ θ ^ N * ‖v‖ :=
    (hs N x v hv).trans (mul_le_mul_of_nonneg_right hblock.le (norm_nonneg v))
  have hublock (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.unstable.toDistribution x) :
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm N) x v‖ ≤
        θ ^ N * ‖v‖ :=
    (hu N x v hv).trans (mul_le_mul_of_nonneg_right hblock.le (norm_nonneg v))
  have hsenergy (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.stable.toDistribution x) :
      (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f (j + 1)) x v‖ ^ 2) ≤
      θ ^ 2 * (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) x v‖ ^ 2) := by
    apply finiteWeightedEnergy_contract (θ ^ 2) (sq_pos_of_pos hθ)
      (fun j ↦ ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) x v‖ ^ 2) N
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hsblock x v hv) 2
    have hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f 0) x v = v := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id x v = v
      simp
    rw [hz]
    have hpow : (θ ^ N) ^ 2 = (θ ^ 2) ^ N := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    simpa only [mul_pow, hpow] using hb
  have huenergy (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.unstable.toDistribution x) :
      (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm (j + 1)) x v‖ ^ 2) ≤
      θ ^ 2 * (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) x v‖ ^ 2) := by
    apply finiteWeightedEnergy_contract (θ ^ 2) (sq_pos_of_pos hθ)
      (fun j ↦ ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) x v‖ ^ 2) N
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hublock x v hv) 2
    have hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm 0) x v = v := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id x v = v
      simp
    rw [hz]
    have hpow : (θ ^ N) ^ 2 = (θ ^ 2) ^ N := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    simpa only [mul_pow, hpow] using hb
  -- The chain rule identifies shifted energies with energies in the receiving fibres.
  have hsstep (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.stable.toDistribution x) :
      (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) (f x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ ^ 2) ≤
      θ ^ 2 * (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) x v‖ ^ 2) := by
    convert hsenergy x v hv using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← ContinuousLinearMap.comp_apply, ← mfderiv_comp x
      ((realIterate 𝓘(ℝ, E) f j).contMDiff.mdifferentiable (by simp)).mdifferentiableAt
      (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt]
    rfl
  have hustep (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.unstable.toDistribution x) :
      (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) (f.symm x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v)‖ ^ 2) ≤
      θ ^ 2 * (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) x v‖ ^ 2) := by
    convert huenergy x v hv using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← ContinuousLinearMap.comp_apply, ← mfderiv_comp x
      ((realIterate 𝓘(ℝ, E) f.symm j).contMDiff.mdifferentiable (by simp)).mdifferentiableAt
      (f.symm.contMDiff.mdifferentiable (by simp)).mdifferentiableAt]
    rfl
  -- The original norm and the finite energy are uniformly comparable on each summand.
  have hslower (x : X) (v : TangentSpace 𝓘(ℝ, E) x) :
      ‖v‖ ^ 2 ≤ ∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) x v‖ ^ 2 := by
    have hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f 0) x v = v := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id x v = v
      simp
    have hh := Finset.single_le_sum
      (s := Finset.range N)
      (f := fun j ↦ ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) x v‖ ^ 2)
      (fun j _ ↦ mul_nonneg (pow_nonneg (inv_nonneg.mpr (sq_nonneg θ)) j) (sq_nonneg _))
      (Finset.mem_range.mpr (lt_of_lt_of_le Nat.zero_lt_one hN))
    simpa only [pow_zero, one_mul, hz] using hh
  have hsupper (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.stable.toDistribution x) :
      (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) x v‖ ^ 2) ≤
      (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j * (C * lam ^ j) ^ 2) * ‖v‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hs j x v hv) 2
    calc
      _ ≤ ((θ ^ 2)⁻¹) ^ j * (C * lam ^ j * ‖v‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (inv_nonneg.mpr (sq_nonneg θ)) j)
      _ = _ := by ring

  have hulower (x : X) (v : TangentSpace 𝓘(ℝ, E) x) :
      ‖v‖ ^ 2 ≤ ∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) x v‖ ^ 2 := by
    have hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm 0) x v = v := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id x v = v
      simp
    have hh := Finset.single_le_sum
      (s := Finset.range N)
      (f := fun j ↦ ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) x v‖ ^ 2)
      (fun j _ ↦ mul_nonneg (pow_nonneg (inv_nonneg.mpr (sq_nonneg θ)) j) (sq_nonneg _))
      (Finset.mem_range.mpr (lt_of_lt_of_le Nat.zero_lt_one hN))
    simpa only [pow_zero, one_mul, hz] using hh
  have huupper (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.unstable.toDistribution x) :
      (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) x v‖ ^ 2) ≤
      (∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j * (C * lam ^ j) ^ 2) * ‖v‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hu j x v hv) 2
    calc
      _ ≤ ((θ ^ 2)⁻¹) ^ j * (C * lam ^ j * ‖v‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (inv_nonneg.mpr (sq_nonneg θ)) j)
      _ = _ := by ring

  -- Realize the two finite energies as positive definite symmetric bilinear forms.
  let Bs (x : X) : TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ]
      TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] ℝ :=
    ∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j •
      (innerₗ (TangentSpace 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j x))).compl₁₂
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) x).toLinearMap
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) x).toLinearMap
  let Bu (x : X) : TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ]
      TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] ℝ :=
    ∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j •
      (innerₗ (TangentSpace 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j x))).compl₁₂
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) x).toLinearMap
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) x).toLinearMap
  have hBsdiag (x : X) (v : TangentSpace 𝓘(ℝ, E) x) :
      Bs x v v = ∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f j) x v‖ ^ 2 := by
    simp [Bs, LinearMap.sum_apply]
  have hBudiag (x : X) (v : TangentSpace 𝓘(ℝ, E) x) :
      Bu x v v = ∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j *
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) f.symm j) x v‖ ^ 2 := by
    simp [Bu, LinearMap.sum_apply]
  have hBssymm (x : X) (v w : TangentSpace 𝓘(ℝ, E) x) :
      Bs x v w = Bs x w v := by
    simp only [Bs, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      innerₗ_apply_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm]
  have hBusymm (x : X) (v w : TangentSpace 𝓘(ℝ, E) x) :
      Bu x v w = Bu x w v := by
    simp only [Bu, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      innerₗ_apply_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm]
  have hBspos (x : X) (v : TangentSpace 𝓘(ℝ, E) x) (hv : v ≠ 0) :
      0 < Bs x v v := by
    rw [hBsdiag]
    exact (sq_pos_of_pos (norm_pos_iff.mpr hv)).trans_le (hslower x v)
  have hBupos (x : X) (v : TangentSpace 𝓘(ℝ, E) x) (hv : v ≠ 0) :
      0 < Bu x v v := by
    rw [hBudiag]
    exact (sq_pos_of_pos (norm_pos_iff.mpr hv)).trans_le (hulower x v)
  have hBscontract (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.stable.toDistribution x) :
      Bs (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤ θ ^ 2 * Bs x v v := by
    simpa only [hBsdiag] using hsstep x v hv
  have hBucontract (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.unstable.toDistribution x) :
      Bu (f.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤ θ ^ 2 * Bu x v v := by
    simpa only [hBudiag] using hustep x v hv
  -- Smoothness of the given metric supplies continuity of its bundle inner products.
  let : IsContinuousRiemannianBundle E (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x) := by
    obtain ⟨g, hg, heq⟩ := IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := 𝓘(ℝ, E)) (n := ∞) (F := E) (E := fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)
    exact ⟨g, hg.continuous, heq⟩
  -- The adapted quadratic energies are continuous on the original tangent total space.
  have hBscontinuous : Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ Bs p.proj p.2 p.2) := by
    simp only [Bs, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      innerₗ_apply_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    apply continuous_finsetSum
    intro j hj
    have hjcont := (realIterate 𝓘(ℝ, E) f j).contMDiff.continuous_tangentMap (by simp)
    exact continuous_const.mul (hjcont.inner_bundle hjcont)
  have hBucontinuous : Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ Bu p.proj p.2 p.2) := by
    simp only [Bu, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      innerₗ_apply_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
    apply continuous_finsetSum
    intro j hj
    have hjcont := (realIterate 𝓘(ℝ, E) f.symm j).contMDiff.continuous_tangentMap (by simp)
    exact continuous_const.mul (hjcont.inner_bundle hjcont)
  -- Take square roots without changing any original tangent norm or metric instance.
  let νs (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : ℝ := Real.sqrt (Bs x v v)
  let νu (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : ℝ := Real.sqrt (Bu x v v)
  have hνscontinuous : Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ νs p.proj p.2) :=
    hBscontinuous.sqrt
  have hνucontinuous : Continuous (fun p : TangentBundle 𝓘(ℝ, E) X ↦ νu p.proj p.2) :=
    hBucontinuous.sqrt
  have hνscontract (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.stable.toDistribution x) :
      νs (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤ θ * νs x v := by
    have hc := Real.sqrt_le_sqrt (hBscontract x v hv)
    simpa only [νs, Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ.le] using hc
  have hνucontract (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.unstable.toDistribution x) :
      νu (f.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤ θ * νu x v := by
    have hc := Real.sqrt_le_sqrt (hBucontract x v hv)
    simpa only [νu, Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ.le] using hc
  have hνslower (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : ‖v‖ ≤ νs x v := by
    have hc := Real.sqrt_le_sqrt (hslower x v)
    simpa only [νs, hBsdiag, Real.sqrt_sq (norm_nonneg v)] using hc
  have hνulower (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : ‖v‖ ≤ νu x v := by
    have hc := Real.sqrt_le_sqrt (hulower x v)
    simpa only [νu, hBudiag, Real.sqrt_sq (norm_nonneg v)] using hc
  let K : ℝ := ∑ j ∈ Finset.range N, ((θ ^ 2)⁻¹) ^ j * (C * lam ^ j) ^ 2
  have hνsupper (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.stable.toDistribution x) : νs x v ≤ Real.sqrt K * ‖v‖ := by
    have hc := Real.sqrt_le_sqrt (hsupper x v hv)
    simpa only [νs, hBsdiag, K, Real.sqrt_mul' _ (sq_nonneg ‖v‖),
      Real.sqrt_sq (norm_nonneg v)] using hc
  have hνuupper (x : X) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ∈ S.unstable.toDistribution x) : νu x v ≤ Real.sqrt K * ‖v‖ := by
    have hc := Real.sqrt_le_sqrt (huupper x v hv)
    simpa only [νu, hBudiag, K, Real.sqrt_mul' _ (sq_nonneg ‖v‖),
      Real.sqrt_sq (norm_nonneg v)] using hc
  -- Apply Mathlib's inner-product core construction only as data: the original
  -- tangent norm, topology and ambient Riemannian distance remain the instances.
  let cs (x : X) : PreInnerProductSpace.Core ℝ (TangentSpace 𝓘(ℝ, E) x) := {
    inner := fun v w ↦ Bs x v w
    conj_inner_symm := fun v w ↦ by simpa using hBssymm x w v
    re_inner_nonneg := fun v ↦ by
      change 0 ≤ Bs x v v
      rw [hBsdiag]
      exact (sq_nonneg ‖v‖).trans (hslower x v)
    add_left := fun v w z ↦ by simp
    smul_left := fun v w c ↦ by simp }
  let cu (x : X) : PreInnerProductSpace.Core ℝ (TangentSpace 𝓘(ℝ, E) x) := {
    inner := fun v w ↦ Bu x v w
    conj_inner_symm := fun v w ↦ by simpa using hBusymm x w v
    re_inner_nonneg := fun v ↦ by
      change 0 ≤ Bu x v v
      rw [hBudiag]
      exact (sq_nonneg ‖v‖).trans (hulower x v)
    add_left := fun v w z ↦ by simp
    smul_left := fun v w c ↦ by simp }
  have hνsadd (x : X) (v w : TangentSpace 𝓘(ℝ, E) x) :
      νs x (v + w) ≤ νs x v + νs x w := by
    exact @SeminormedSpace.Core.norm_triangle ℝ (TangentSpace 𝓘(ℝ, E) x) _ _
      (@InnerProductSpace.Core.toNorm ℝ (TangentSpace 𝓘(ℝ, E) x) _ _ _ (cs x)) _
      (InnerProductSpace.Core.toSeminormedSpaceCore (cs x)) v w
  have hνuadd (x : X) (v w : TangentSpace 𝓘(ℝ, E) x) :
      νu x (v + w) ≤ νu x v + νu x w := by
    exact @SeminormedSpace.Core.norm_triangle ℝ (TangentSpace 𝓘(ℝ, E) x) _ _
      (@InnerProductSpace.Core.toNorm ℝ (TangentSpace 𝓘(ℝ, E) x) _ _ _ (cu x)) _
      (InnerProductSpace.Core.toSeminormedSpaceCore (cu x)) v w
  have hνssmul (x : X) (c : ℝ) (v : TangentSpace 𝓘(ℝ, E) x) :
      νs x (c • v) = ‖c‖ * νs x v := by
    exact @SeminormedSpace.Core.norm_smul ℝ (TangentSpace 𝓘(ℝ, E) x) _ _
      (@InnerProductSpace.Core.toNorm ℝ (TangentSpace 𝓘(ℝ, E) x) _ _ _ (cs x)) _
      (InnerProductSpace.Core.toSeminormedSpaceCore (cs x)) c v
  have hνusmul (x : X) (c : ℝ) (v : TangentSpace 𝓘(ℝ, E) x) :
      νu x (c • v) = ‖c‖ * νu x v := by
    exact @SeminormedSpace.Core.norm_smul ℝ (TangentSpace 𝓘(ℝ, E) x) _ _
      (@InnerProductSpace.Core.toNorm ℝ (TangentSpace 𝓘(ℝ, E) x) _ _ _ (cu x)) _
      (InnerProductSpace.Core.toSeminormedSpaceCore (cu x)) c v
  let split (x : X) :=
    (Submodule.prodEquivOfIsCompl (S.stable.toDistribution x)
      (S.unstable.toDistribution x) (S.isCompl x)).symm
  let ν (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : ℝ :=
    max (νs x (split x v).1) (νu x (split x v).2)
  have hνnonneg (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : 0 ≤ ν x v :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hνzero (x : X) : ν x 0 = 0 := by simp [ν, νs, νu]
  have hνadd (x : X) (v w : TangentSpace 𝓘(ℝ, E) x) :
      ν x (v + w) ≤ ν x v + ν x w := by
    dsimp [ν]
    simp only [map_add, Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    exact max_le
      ((hνsadd x _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
      ((hνuadd x _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _)))
  have hνsmul (x : X) (c : ℝ) (v : TangentSpace 𝓘(ℝ, E) x) :
      ν x (c • v) = ‖c‖ * ν x v := by
    dsimp [ν]
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd, SetLike.val_smul,
      hνssmul, hνusmul]
    exact (mul_max_of_nonneg _ _ (norm_nonneg c)).symm
  have hνlower (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : ‖v‖ ≤ 2 * ν x v := by
    have hsum : ((split x v).1 : TangentSpace 𝓘(ℝ, E) x) + (split x v).2 = v :=
      (Submodule.prodEquivOfIsCompl (S.stable.toDistribution x)
        (S.unstable.toDistribution x) (S.isCompl x)).apply_symm_apply v
    calc
      ‖v‖ = ‖((split x v).1 : TangentSpace 𝓘(ℝ, E) x) + (split x v).2‖ := by rw [hsum]
      _ ≤ ‖((split x v).1 : TangentSpace 𝓘(ℝ, E) x)‖ + ‖((split x v).2 :
          TangentSpace 𝓘(ℝ, E) x)‖ := norm_add_le _ _
      _ ≤ νs x (split x v).1 + νu x (split x v).2 :=
        add_le_add (hνslower x _) (hνulower x _)
      _ ≤ 2 * ν x v := by
        dsimp [ν]
        have hleft := le_max_left (νs x (split x v).1) (νu x (split x v).2)
        have hright := le_max_right (νs x (split x v).1) (νu x (split x v).2)
        linarith
  have hνdefinite (x : X) (v : TangentSpace 𝓘(ℝ, E) x) : ν x v = 0 ↔ v = 0 := by
    constructor
    · intro hv
      exact norm_eq_zero.mp (le_antisymm (by simpa [hv] using hνlower x v) (norm_nonneg v))
    · rintro rfl
      exact hνzero x
  have hνstable (x : X) (v : S.stable.toDistribution x) : ν x v = νs x v := by
    dsimp [ν, split]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [νu, νs]
  have hνunstable (x : X) (v : S.unstable.toDistribution x) : ν x v = νu x v := by
    dsimp [ν, split]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp [νs, νu]
  have hνstable_contract (x : X) (v : S.stable.toDistribution x) :
      ν (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤ θ * ν x v := by
    have hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v ∈ S.stable.toDistribution (f x) := by
      rw [← S.stable_map x]
      exact ⟨v, v.property, rfl⟩
    rw [hνstable x v, hνstable (f x) ⟨_, hv⟩]
    exact hνscontract x v v.property
  have hνunstable_contract (x : X) (v : S.unstable.toDistribution x) :
      ν (f.symm x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤ θ * ν x v := by
    have hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v ∈
        S.unstable.toDistribution (f.symm x) := by
      rw [← FixedBlockEstimates.Inverse.inverse_distribution_invariant f
        S.unstable.toDistribution S.unstable_map x]
      exact ⟨v, v.property, rfl⟩
    rw [hνunstable x v, hνunstable (f.symm x) ⟨_, hv⟩]
    exact hνucontract x v v.property
  exact ⟨θ, Real.sqrt K, νs, νu, ν, hθ, hθ1, Real.sqrt_nonneg _,
    hνscontinuous, hνucontinuous, (fun x v ↦ hνsupper x v v.property),
    (fun x v ↦ hνuupper x v v.property), (fun _ _ ↦ rfl), hνzero, hνadd,
    hνsmul, hνlower, hνstable_contract, hνunstable_contract⟩

end HolomorphicAnosov.HPS
