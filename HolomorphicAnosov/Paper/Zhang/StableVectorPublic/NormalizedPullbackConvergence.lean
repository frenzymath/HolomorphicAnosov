import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform convergence of normalized stable pullbacks in a Hermitian metric. (Zhang, Lemma 4.3, eq.
(24)) -/

open scoped ContDiff Topology _root_.Topology
open Filter
namespace HolomorphicAnosov
noncomputable section
universe u

/-- A one-form whose kernel is the unstable subspace is injective on the complementary stable
subspace. (Zhang, Lemma 4.3) -/
private theorem normalized_stable_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S U : Submodule ℂ V) (θ : V →ₗ[ℂ] ℂ)
    (hcompl : IsCompl S U) (hker : LinearMap.ker θ = U)
    {v w : V} (hv : v ∈ S) (hw : w ∈ S) (hθ : θ v = θ w) : v = w := by
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp hcompl.disjoint (v - w) (S.sub_mem hv hw)
  rw [← hker, LinearMap.mem_ker, map_sub, hθ, sub_self]

/-- Two vectors normalized by the same one-form differ by an unstable vector when its kernel is the
unstable subspace. (Zhang, Lemma 4.3) -/
private theorem normalized_difference_unstable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (U : Submodule ℂ V) (θ : V →ₗ[ℂ] ℂ) (hker : LinearMap.ker θ = U)
    {v w : V} (hv : θ v = 1) (hw : θ w = 1) : v - w ∈ U := by
  rw [← hker, LinearMap.mem_ker, map_sub, hv, hw, sub_self]

/-- The differential sends the normalized stable section `e` to `μ • e ∘ f`. (Zhang, Lemma 4.3) -/
private theorem normalized_stable_derivative
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X)
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hcompl : ∀ x, IsCompl (S x) (U x))
    (hS_invariant : ∀ x, (S x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = S (f x))
    (θ : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ_kernel : ∀ x, LinearMap.ker (θ x).toLinearMap = U x)
    (μ : ℂ)
    (hθ_pullback : ∀ x (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (e : (x : X) → TangentSpace (complexModel d) x)
    (he_stable : ∀ x, e x ∈ S x) (he_normalized : ∀ x, θ x (e x) = 1) (x : X) :
    mfderiv (complexModel d) (complexModel d) f x (e x) = μ • e (f x) := by
  apply normalized_stable_injective (S (f x)) (U (f x)) (θ (f x)).toLinearMap
    (hcompl (f x)) (hθ_kernel (f x))
  · rw [← hS_invariant x]
    exact Submodule.mem_map_of_mem (he_stable x)
  · exact (S (f x)).smul_mem μ (he_stable (f x))
  · change θ (f x) (mfderiv (complexModel d) (complexModel d) f x (e x)) =
      θ (f x) (μ • e (f x))
    rw [hθ_pullback, he_normalized, map_smul, he_normalized]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The differential of the nth iterate sends the normalized stable section to `μ ^ n` times its
value at the image point. (Zhang, Lemma 4.3) -/
theorem normalized_stable_iterate
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X)
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hcompl : ∀ x, IsCompl (S x) (U x))
    (hS_invariant : ∀ x, (S x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = S (f x))
    (θ : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ_kernel : ∀ x, LinearMap.ker (θ x).toLinearMap = U x)
    (μ : ℂ)
    (hθ_pullback : ∀ x (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (e : (x : X) → TangentSpace (complexModel d) x)
    (he_stable : ∀ x, e x ∈ S x) (he_normalized : ∀ x, θ x (e x) = 1)
    (n : ℕ) (x : X) :
    hermitianBoundsDerivative f n x (e x) = μ ^ n • e (hermitianBoundsIterate f n x) := by
  change mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x (e x) =
    μ ^ n • e ((f : X → X)^[n] x)
  induction n generalizing x with
  | zero =>
    simp only [Function.iterate_zero, mfderiv_id, pow_zero]
    exact (one_smul ℂ (e x)).symm
  | succ n ih =>
    have hf : MDifferentiable (complexModel d) (complexModel d) (f : X → X) :=
      f.contMDiff_toFun.mdifferentiable (by simp)
    have hfn : MDifferentiable (complexModel d) (complexModel d) ((f : X → X)^[n]) :=
      (f.contMDiff_toFun.iterate n).mdifferentiable (by simp)
    rw [Function.iterate_succ']
    rw [mfderiv_comp x hf.mdifferentiableAt hfn.mdifferentiableAt]
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
    rw [ih, map_smul, normalized_stable_derivative f S U hcompl hS_invariant θ
      hθ_kernel μ hθ_pullback e he_stable he_normalized]
    rw [smul_smul, pow_succ]

/-- The error of a normalized inverse pullback equals the normalized inverse differential applied to
the initial section error at the image point. (Zhang, eq. (24)) -/
private theorem normalized_stable_pullback_error
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X)
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hcompl : ∀ x, IsCompl (S x) (U x))
    (hS_invariant : ∀ x, (S x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = S (f x))
    (θ : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ_kernel : ∀ x, LinearMap.ker (θ x).toLinearMap = U x)
    (μ : ℂ)
    (hθ_pullback : ∀ x (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (e e₀ : (x : X) → TangentSpace (complexModel d) x)
    (he_stable : ∀ x, e x ∈ S x) (he_normalized : ∀ x, θ x (e x) = 1)
    (n : ℕ) (x : X) :
    μ ^ n • (hermitianBoundsDerivative f n x).symm (e₀ (hermitianBoundsIterate f n x)) -
        e x =
      μ ^ n • (hermitianBoundsDerivative f n x).symm
        (e₀ (hermitianBoundsIterate f n x) - e (hermitianBoundsIterate f n x)) := by
  have he := normalized_stable_iterate f S U hcompl hS_invariant θ hθ_kernel μ
    hθ_pullback e he_stable he_normalized n x
  have he' := congrArg (hermitianBoundsDerivative f n x).symm he
  rw [ContinuousLinearEquiv.symm_apply_apply, map_smul] at he'
  rw [map_sub, smul_sub, ← he']

/-- Normalized inverse pullbacks converge uniformly to the stable section in the given Hermitian
metric under the unstable inverse-operator and initial-error bounds. (Zhang, Lemma 4.3, eq.
(24)) -/
theorem normalized_stable_pullback_convergence
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    (f : Biholomorph d d X X)
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hcompl : ∀ x, IsCompl (S x) (U x))
    (hSinv : ∀ x, (S x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = S (f x))
    (θ : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hker : ∀ x, LinearMap.ker (θ x).toLinearMap = U x)
    (μ : ℂ) (hμ : ‖μ‖ < 1)
    (hpull : ∀ x (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (e e₀ : (x : X) → TangentSpace (complexModel d) x)
    (heS : ∀ x, e x ∈ S x) (he : ∀ x, θ x (e x) = 1)
    (he₀ : ∀ x, θ x (e₀ x) = 1)
    (h : HermitianTangentMetricCore d X) (hsmooth : IsSmoothHermitianTangentMetric h)
    (A L lam : ℝ) (hA : 0 ≤ A) (hlam : 1 < lam)
    (herror : ∀ x, hermitianBoundsNorm h x (e₀ x - e x) ≤ L)
    (hinv : ∀ n x,
      fibreNormOperator (hermitianBoundsNorm h (hermitianBoundsIterate f n x))
        (hermitianBoundsNorm h x) (U (hermitianBoundsIterate f n x))
        (hermitianBoundsDerivative f n x).symm ≤ A * (lam ^ n)⁻¹) :
    (∀ n x, hermitianBoundsNorm h x
      (μ ^ n • (hermitianBoundsDerivative f n x).symm
        (e₀ (hermitianBoundsIterate f n x)) - e x) ≤ A * L * (‖μ‖ / lam) ^ n) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x, hermitianBoundsNorm h x
      (μ ^ n • (hermitianBoundsDerivative f n x).symm
        (e₀ (hermitianBoundsIterate f n x)) - e x) < ε) := by
  let p := HermitianFibreAlgebra.hermitianBoundsRealSeminorm h
  have pp : ∀ x v, v ≠ 0 → 0 < p x v :=
    fun x _ hv ↦ HermitianFibreAlgebra.coreLength_pos (h x) hv
  have pc : Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd) :=
    Preparation.continuous_hermitian_tangent_norm h hsmooth
  have hbound n x : hermitianBoundsNorm h x
      (μ ^ n • (hermitianBoundsDerivative f n x).symm
        (e₀ (hermitianBoundsIterate f n x)) - e x) ≤ A * L * (‖μ‖ / lam) ^ n := by
    rw [normalized_stable_pullback_error f S U hcompl hSinv θ hker μ hpull e e₀ heS he]
    change HermitianFibreAlgebra.coreLength (h x) (_ • _) ≤ _
    rw [HermitianFibreAlgebra.coreLength_complex_smul, norm_pow]
    have hw := normalized_difference_unstable (U (hermitianBoundsIterate f n x))
      (θ (hermitianBoundsIterate f n x)).toLinearMap (hker _)
      (he₀ (hermitianBoundsIterate f n x)) (he (hermitianBoundsIterate f n x))
    have hb := (CompactHermitianAssembly.native_unit_values_bddAbove f p pc pp n x
      (S x) (U (hermitianBoundsIterate f n x))).2
    have hop := CompactHermitianBoundsScratch.pointwise_le_operator
      (p (hermitianBoundsIterate f n x)) (p x) (U (hermitianBoundsIterate f n x))
      ((hermitianBoundsDerivative f n x).symm.toLinearMap.restrictScalars ℝ)
      (pp _) hb hw
    have hv0 : 0 ≤ p (hermitianBoundsIterate f n x)
        (e₀ (hermitianBoundsIterate f n x) - e (hermitianBoundsIterate f n x)) :=
      apply_nonneg _ _
    have hle := hop.trans (mul_le_mul_of_nonneg_right (hinv n x) hv0)
    have hle' := hle.trans (mul_le_mul_of_nonneg_left
      (herror (hermitianBoundsIterate f n x))
      (mul_nonneg hA (inv_nonneg.mpr (pow_nonneg (by linarith) n))))
    calc
      _ ≤ ‖μ‖ ^ n * (A * (lam ^ n)⁻¹ * L) :=
        mul_le_mul_of_nonneg_left hle' (pow_nonneg (norm_nonneg μ) n)
      _ = A * L * (‖μ‖ / lam) ^ n := by rw [div_pow]; ring
  refine ⟨hbound, ?_⟩
  intro ε hε
  have hratio : ‖μ‖ / lam < 1 := (div_lt_one (by linarith)).mpr (hμ.trans hlam)
  have ht : Tendsto (fun n : ℕ ↦ A * L * (‖μ‖ / lam) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg (norm_nonneg μ) (by linarith)) hratio).const_mul (A * L)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  exact fun x ↦ (hbound n x).trans_lt hn

end
end HolomorphicAnosov

