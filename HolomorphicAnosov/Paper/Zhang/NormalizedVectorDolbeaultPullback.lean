import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.HolomorphicComplexOneForm
import HolomorphicAnosov.Geometry.VectorDolbeaultDerivative
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import HolomorphicAnosov.Analysis.Complex.AntiholomorphicValue

/-! This file establishes smoothness, normalization, and the kernel-valued Dolbeault pullback
formula for normalized iterates of a vector section. (Zhang, Lemma 4.3, p.15, equations
(24)–(26)) -/

namespace HolomorphicAnosov

open Set
open scoped Manifold ContDiff


noncomputable section

/-- The nth iterate of a biholomorphism as a biholomorphism. (Zhang, Lemma 4.3, p.15, equation (24)) -/
private def normalizedIterate {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] (f : Biholomorph d d X X) :
    ℕ → Biholomorph d d X X
  | 0 => Diffeomorph.refl (complexModel d) X ∞
  | n + 1 => (normalizedIterate f n).trans f

/-- The iterated biholomorphism acts pointwise as the nth function iterate. (Zhang, Lemma 4.3, p.15,
equation (24)) -/
private theorem normalizedIterate_apply {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] (f : Biholomorph d d X X) (n : ℕ) (x : X) :
    normalizedIterate f n x = (f : X → X)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change f (normalizedIterate f n x) = _
      rw [ih, Function.iterate_succ_apply']

/-- The underlying map of the iterated biholomorphism is the nth function iterate. (Zhang, Lemma
4.3, p.15, equation (24)) -/
private theorem normalizedIterate_coe {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] (f : Biholomorph d d X X) (n : ℕ) :
    (normalizedIterate f n : X → X) = (f : X → X)^[n] := by
  funext x
  exact normalizedIterate_apply f n x

/-- The tangent derivative of every iterate of a biholomorphism is invertible. (Zhang, Lemma 4.3,
p.15, equation (24)) -/
private theorem normalizedIterate_invertible {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (n : ℕ) (x : X) :
    (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x).IsInvertible := by
  rw [← normalizedIterate_coe f n]
  exact (normalizedIterate f n).isInvertible_mfderiv (by simp)

/-- The nth iterate scales the one-form by `μ ^ n` when the biholomorphism scales it by `μ`. (Zhang,
Lemma 4.3, p.15) -/
private theorem normalizedIterate_scale {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (θ : ComplexOneForm d X) (μ : ℂ)
    (hscale : ∀ (x : X) (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (n : ℕ) (x : X) (v : TangentSpace (complexModel d) x) :
    θ ((f : X → X)^[n] x)
      (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x v) =
        μ ^ n * θ x v := by
  induction n with
  | zero =>
      simp only [Function.iterate_zero, id_eq, mfderiv_id, pow_zero, one_mul]
      rfl
  | succ n ih =>
      have hc := mfderiv_comp x
        (f.contMDiff.mdifferentiable (by simp) ((f : X → X)^[n] x))
        ((f.contMDiff.iterate n).mdifferentiable (by simp) x)
      rw [Function.iterate_succ_apply', Function.iterate_succ', hc]
      change θ (f ((f : X → X)^[n] x))
        (mfderiv (complexModel d) (complexModel d) f ((f : X → X)^[n] x)
          (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x v)) = _
      rw [hscale, ih, pow_succ]
      ring


/-- The normalized inverse-derivative pullback of a section pairing to one with the one-form also
pairs to one. (Zhang, Lemma 4.3, p.15) -/
private theorem normalizedIterate_normalized {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (θ : ComplexOneForm d X) (μ : ℂ)
    (hscale : ∀ (x : X) (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (e₀ : (x : X) → TangentSpace (complexModel d) x)
    (hnormalized : ∀ x : X, θ x (e₀ x) = 1) (n : ℕ) (x : X) :
    θ x (μ ^ n •
      (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x).inverse
        (e₀ ((f : X → X)^[n] x))) = 1 := by
  let F := mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x
  have hF : F.IsInvertible := normalizedIterate_invertible f n x
  have h := normalizedIterate_scale f θ μ hscale n x
    (F.inverse (e₀ ((f : X → X)^[n] x)))
  change θ ((f : X → X)^[n] x) (F (F.inverse (e₀ ((f : X → X)^[n] x)))) = _ at h
  rw [hF.self_apply_inverse, hnormalized] at h
  simpa only [map_smul, smul_eq_mul] using h.symm

/-- The iterated tangent derivative maps the one-form kernel onto the kernel at the image point.
(Zhang, Lemma 4.3, p.15, equation (26)) -/
private theorem normalizedIterate_kernel_map {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (θ : ComplexOneForm d X) (μ : ℂ) (hμ : μ ≠ 0)
    (hscale : ∀ (x : X) (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (n : ℕ) (x : X) :
    (LinearMap.ker (θ x).toLinearMap).map
      (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x).toLinearMap =
        LinearMap.ker (θ ((f : X → X)^[n] x)).toLinearMap := by
  let F := mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x
  have hF : F.IsInvertible := normalizedIterate_invertible f n x
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    change θ ((f : X → X)^[n] x) (F v) = 0
    rw [normalizedIterate_scale f θ μ hscale n x]
    change θ x v = 0 at hv
    rw [hv, mul_zero]
  · intro hw
    refine ⟨F.inverse w, ?_, hF.self_apply_inverse w⟩
    change θ x (F.inverse w) = 0
    have h := normalizedIterate_scale f θ μ hscale n x (F.inverse w)
    change θ ((f : X → X)^[n] x) (F (F.inverse w)) = _ at h
    rw [hF.self_apply_inverse] at h
    change θ ((f : X → X)^[n] x) w = 0 at hw
    rw [hw] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero n hμ)

/-- The iterated derivative restricts to a continuous complex-linear equivalence between the
one-form kernels. (Zhang, Lemma 4.3, p.15, equation (26)) -/
private theorem normalizedIterate_kernel_equiv {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (θ : ComplexOneForm d X) (μ : ℂ) (hμ : μ ≠ 0)
    (hscale : ∀ (x : X) (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (n : ℕ) :
    ∃ Uₙ : (x : X) → LinearMap.ker (θ x).toLinearMap ≃L[ℂ]
        LinearMap.ker (θ ((f : X → X)^[n] x)).toLinearMap,
      ∀ (x : X) (u : LinearMap.ker (θ x).toLinearMap),
        (Uₙ x u : TangentSpace (complexModel d) ((f : X → X)^[n] x)) =
          mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x u := by
  let F := fun x ↦ mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x
  let A := fun x ↦ Classical.choose (normalizedIterate_invertible f n x)
  have hA : ∀ x, (A x).toContinuousLinearMap = F x :=
    fun x ↦ Classical.choose_spec (normalizedIterate_invertible f n x)
  have hmap (x : X) : (LinearMap.ker (θ x).toLinearMap).map (A x).toLinearEquiv.toLinearMap =
      LinearMap.ker (θ ((f : X → X)^[n] x)).toLinearMap := by
    change (LinearMap.ker (θ x).toLinearMap).map (A x).toContinuousLinearMap.toLinearMap = _
    rw [hA]
    exact normalizedIterate_kernel_map f θ μ hμ hscale n x
  refine ⟨fun x ↦ (A x).ofSubmodules _ _ (hmap x), ?_⟩
  intro x u
  change (A x) u = F x u
  exact congrArg (fun T ↦ T u) (hA x)


/-- The Dolbeault coefficient matrix is the antiholomorphic part of the real derivative of the
vector coefficients. (Zhang, Lemma 4.3, p.15, equation (25); Demailly, I §3.C, pp.22–24) -/
private theorem vectorDolbeaultMatrix_antiholomorphic {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (V : (x : X) → TangentSpace (complexModel d) x) (x : X)
    (hV : DifferentiableAt ℝ (preferredVectorCoefficients V x)
      (chartAt (ComplexModel d) x x)) (v : ComplexModel d) :
    vectorDolbeaultMatrix V x (star v) =
      antiholomorphicValue
        (fderiv ℝ (preferredVectorCoefficients V x) (chartAt (ComplexModel d) x x)) v := by
  rw [antiholomorphicValue_basis]
  ext j
  simp only [vectorDolbeaultMatrix, ContinuousLinearMap.pi_apply,
    sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, Pi.star_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [vectorDolbeaultCoefficient, fderiv_apply hV]
  simp only [antiholomorphicValue, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hsingle : Pi.single k Complex.I = Complex.I • (Pi.single k 1 : ComplexModel d) := by
    ext l
    by_cases h : k = l <;> simp [h]
  rw [hsingle]
  ring

/-- The Dolbeault tensor is the antiholomorphic derivative of the vector coefficients expressed in
the tangent frame. (Zhang, Lemma 4.3, p.15, equation (25)) -/
private theorem vectorDolbeault_antiholomorphic {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (V : (x : X) → TangentSpace (complexModel d) x) (x : X)
    (hV : DifferentiableAt ℝ (preferredVectorCoefficients V x)
      (chartAt (ComplexModel d) x x)) (v : TangentSpace (complexModel d) x) :
    let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
    vectorDolbeault V x v = t.symmL ℂ x
      (antiholomorphicValue
        (fderiv ℝ (preferredVectorCoefficients V x) (chartAt (ComplexModel d) x x))
        (t.continuousLinearMapAt ℂ x v)) := by
  dsimp only [vectorDolbeault, ContinuousLinearMap.comp_apply]
  exact congrArg _ (vectorDolbeaultMatrix_antiholomorphic V x hV _)

/-- Real smooth vector coefficients are real differentiable at points in the chart target. (Zhang,
Lemma 4.3, p.15) -/
private theorem preferredVectorCoefficients_differentiableAt {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target) (x : X) :
    DifferentiableAt ℝ (preferredVectorCoefficients V x) (chartAt (ComplexModel d) x x) := by
  exact ((hV x).differentiableOn (by simp)).differentiableAt
    ((chartAt (ComplexModel d) x).open_target.mem_nhds (mem_chart_target _ x))

/-- The inverse-chart tangent frame equals the inverse tangent trivialization. (Demailly, II §3.1,
pp.85–86, equations (3.3)–(3.5)) -/
private theorem preferredFrame_eq_symmL {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (a : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target) (i : Fin d) :
    hermitianTangentChartFrame (chartAt (ComplexModel d) a) z i =
      (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a).symmL ℂ
        ((chartAt (ComplexModel d) a).symm z) (Pi.single i 1) := by
  have hsource := (chartAt (ComplexModel d) a).map_target hz
  rw [TangentBundle.symmL_trivializationAt hsource]
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_coe, complexModel,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.range_id, mfderivWithin_univ]
  change mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) a).symm z _ =
    mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) a).symm
      ((chartAt (ComplexModel d) a) ((chartAt (ComplexModel d) a).symm z)) _
  rw [(chartAt (ComplexModel d) a).right_inv hz]
  rfl

/-- The continuous complex-linear functional representing a one-form in a preferred chart.
(Demailly, II §3.1, pp.85–86) -/
def preferredCotangentCoefficients {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    (θ : ComplexOneForm d X) (a : X) (z : ComplexModel d) : ComplexModel d →L[ℂ] ℂ :=
  ∑ i : Fin d, complexOneFormChartCoefficient θ (chartAt (ComplexModel d) a) i z •
    ContinuousLinearMap.proj i

/-- The coordinate functional evaluates as the one-form applied to the inverse-frame tangent vector.
(Demailly, II §3.1, pp.85–86) -/
theorem preferredCotangentCoefficients_apply {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (θ : ComplexOneForm d X)
    (a : X) (z : ComplexModel d) (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (v : ComplexModel d) :
    preferredCotangentCoefficients θ a z v =
      θ ((chartAt (ComplexModel d) a).symm z)
        ((trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a).symmL ℂ
          ((chartAt (ComplexModel d) a).symm z) v) := by
  conv_rhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul, preferredCotangentCoefficients,
    sum_apply, smul_apply, ContinuousLinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [complexOneFormChartCoefficient, preferredFrame_eq_symmL a z hz i]
  exact mul_comm _ _

/-- The coordinate functional of a holomorphic one-form is complex smooth on the chart target.
(Zhang, Lemma 4.3, p.15) -/
theorem preferredCotangentCoefficients_holomorphic {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (θ : ComplexOneForm d X)
    (hθ : IsHolomorphicComplexOneForm θ) (a : X) :
    ContDiffOn ℂ ∞ (preferredCotangentCoefficients θ a)
      (chartAt (ComplexModel d) a).target := by
  apply ContDiffOn.sum
  intro i _
  exact (hθ _ (IsManifold.chart_mem_maximalAtlas a) i).smul contDiffOn_const

/-- The Dolbeault derivative of a section normalized by a holomorphic one-form takes values in the
kernel of that one-form. (Zhang, Lemma 4.3, p.15) -/
private theorem vectorDolbeault_normalized_kernel {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (θ : ComplexOneForm d X)
    (hθ : IsHolomorphicComplexOneForm θ)
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target)
    (hnormalized : ∀ x : X, θ x (V x) = 1)
    (x : X) (v : TangentSpace (complexModel d) x) : θ x (vectorDolbeault V x v) = 0 := by
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let z := chartAt (ComplexModel d) x x
  let T := preferredCotangentCoefficients θ x
  let a := preferredVectorCoefficients V x
  have hz : z ∈ (chartAt (ComplexModel d) x).target := mem_chart_target _ x
  have hT : DifferentiableAt ℂ T z :=
    ((preferredCotangentCoefficients_holomorphic θ hθ x).differentiableOn (by simp)).differentiableAt
      ((chartAt (ComplexModel d) x).open_target.mem_nhds hz)
  have ha : DifferentiableAt ℝ a z := preferredVectorCoefficients_differentiableAt V hV x
  have hpair : (fun w ↦ T w (a w)) =ᶠ[nhds z] (fun _ ↦ (1 : ℂ)) := by
    filter_upwards [(chartAt (ComplexModel d) x).open_target.mem_nhds hz] with w hw
    rw [preferredCotangentCoefficients_apply θ x w hw]
    have hbase : (chartAt (ComplexModel d) x).symm w ∈ t.baseSet := by
      simpa only [t, TangentBundle.trivializationAt_baseSet] using
        (chartAt (ComplexModel d) x).map_target hw
    change θ ((chartAt (ComplexModel d) x).symm w)
      (t.symmL ℂ ((chartAt (ComplexModel d) x).symm w)
        (t ⟨(chartAt (ComplexModel d) x).symm w, V ((chartAt (ComplexModel d) x).symm w)⟩).2) = 1
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ t hbase,
      t.symmL_continuousLinearMapAt hbase]
    exact hnormalized _
  have h := antiholomorphicValue_fderiv_normalized T (fderiv ℂ T z) a
    (fderiv ℝ a z) z hT.hasFDerivAt ha.hasFDerivAt hpair (t.continuousLinearMapAt ℂ x v)
  change preferredCotangentCoefficients θ x z _ = 0 at h
  rw [preferredCotangentCoefficients_apply θ x z hz] at h
  rw [vectorDolbeault_antiholomorphic V x ha v]
  dsimp only [z] at h
  rw [(chartAt (ComplexModel d) x).left_inv (mem_chart_source _ x)] at h
  exact h

/-- The antiholomorphic derivative of real smooth coordinate functions, evaluated at a fixed vector,
is real smooth. (Demailly, V §11, p.267) -/
private theorem antiholomorphicValue_fderiv_smooth {d e : ℕ}
    (a : ComplexModel d → ComplexModel e) (s : Set (ComplexModel d))
    (hs : IsOpen s) (ha : ContDiffOn ℝ ∞ a s) (v : ComplexModel d) :
    ContDiffOn ℝ ∞ (fun z ↦ antiholomorphicValue (fderiv ℝ a z) v) s := by
  have hD := ha.fderiv_of_isOpen hs (m := ∞) (by simp)
  exact ((hD.clm_apply contDiffOn_const).add
    ((hD.clm_apply contDiffOn_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

/-- The complex-linear tangent frame transition between two preferred charts. (Demailly, II §3.1,
pp.85–86) -/
private def preferredTransition {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (a b : X) (z : ComplexModel d) :
    ComplexModel d →L[ℂ] ComplexModel d :=
  (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a).coordChangeL ℂ
    (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b)
    ((chartAt (ComplexModel d) a).symm z)

/-- Tangent frame transitions are complex smooth on chart overlaps. (Demailly, V §11, p.267) -/
private theorem preferredTransition_holomorphicAt {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : (chartAt (ComplexModel d) a).symm z ∈ (chartAt (ComplexModel d) b).source) :
    ContDiffAt ℂ ∞ (preferredTransition a b) z := by
  let ta := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  let tb := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b
  have ha' : (chartAt (ComplexModel d) a).symm z ∈ ta.baseSet := by
    simpa only [ta, TangentBundle.trivializationAt_baseSet] using
      (chartAt (ComplexModel d) a).map_target hz
  have hb' : (chartAt (ComplexModel d) a).symm z ∈ tb.baseSet := by
    simpa only [tb, TangentBundle.trivializationAt_baseSet] using hb
  have h := contMDiffAt_coordChangeL (IB := complexModel d) (n := ∞) ha' hb'
  have hs := contMDiffAt_symm_of_mem_maximalAtlas (I := complexModel d) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas a) hz
  exact (h.comp z hs).contDiffAt

/-- The tangent frame transition equals the derivative of the coordinate change. (Demailly, II §3.1,
pp.85–86) -/
private theorem preferredTransition_eq_fderiv {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : (chartAt (ComplexModel d) a).symm z ∈ (chartAt (ComplexModel d) b).source) :
    preferredTransition a b z =
      fderiv ℂ ((chartAt (ComplexModel d) b) ∘ (chartAt (ComplexModel d) a).symm) z := by
  have hbase : (chartAt (ComplexModel d) a).symm z ∈
      (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a).baseSet ∩
      (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, Set.mem_inter_iff] using
      And.intro ((chartAt (ComplexModel d) a).map_target hz) hb
  apply ContinuousLinearMap.ext
  intro v
  unfold preferredTransition
  erw [(tangentBundleCore (complexModel d) X).trivializationAt_coordChange_eq hbase]
  change tangentCoordChange (complexModel d) a b ((chartAt (ComplexModel d) a).symm z) v = _
  rw [tangentCoordChange_def]
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_coe, complexModel,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.range_id, fderivWithin_univ]
  rw [(chartAt (ComplexModel d) a).right_inv hz]

/-- The preferred coordinate change is complex smooth on its overlap. (Demailly, I §3.C, p.23) -/
private theorem preferredChartChange_holomorphicAt {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : (chartAt (ComplexModel d) a).symm z ∈ (chartAt (ComplexModel d) b).source) :
    ContDiffAt ℂ ∞ ((chartAt (ComplexModel d) b) ∘ (chartAt (ComplexModel d) a).symm) z := by
  have h₁ := contMDiffAt_of_mem_maximalAtlas (I := complexModel d) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas b) hb
  have h₂ := contMDiffAt_symm_of_mem_maximalAtlas (I := complexModel d) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas a) hz
  exact (h₁.comp z h₂).contDiffAt

/-- The vector coefficients of a section transform by the tangent frame transition. (Demailly, V
§11, p.267) -/
private theorem preferredVectorCoefficients_change {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (V : (x : X) → TangentSpace (complexModel d) x)
    (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : (chartAt (ComplexModel d) a).symm z ∈ (chartAt (ComplexModel d) b).source) :
    preferredVectorCoefficients V b
      ((chartAt (ComplexModel d) b) ((chartAt (ComplexModel d) a).symm z)) =
        preferredTransition a b z (preferredVectorCoefficients V a z) := by
  let q := (chartAt (ComplexModel d) a).symm z
  let ta := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  let tb := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b
  have hqa : q ∈ ta.baseSet := (chartAt (ComplexModel d) a).map_target hz
  have hqb : q ∈ tb.baseSet := hb
  change (tb ⟨(chartAt (ComplexModel d) b).symm ((chartAt (ComplexModel d) b) q),
    V ((chartAt (ComplexModel d) b).symm ((chartAt (ComplexModel d) b) q))⟩).2 =
      (ta.coordChangeL ℂ tb q) (ta ⟨q, V q⟩).2
  rw [(chartAt (ComplexModel d) b).left_inv hb, ta.coordChangeL_apply tb ⟨hqa, hqb⟩]
  rw [← ta.symmL_apply (R := ℂ) hqa, ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ ta hqa,
    ta.symmL_continuousLinearMapAt hqa]

/-- The antiholomorphic derivative transforms under a holomorphic frame change by the frame
transition and the derivative of the coordinate change. (Demailly, V §11, p.267) -/
private theorem antiholomorphicValue_fderiv_change {d e : ℕ}
    (a b : ComplexModel d → ComplexModel e)
    (C : ComplexModel d → (ComplexModel e →L[ℂ] ComplexModel e))
    (φ : ComplexModel d → ComplexModel d) (z : ComplexModel d)
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b (φ z))
    (hC : DifferentiableAt ℂ C z) (hφ : DifferentiableAt ℂ φ z)
    (heq : (b ∘ φ) =ᶠ[nhds z] (fun w ↦ C w (a w))) (v : ComplexModel d) :
    antiholomorphicValue (fderiv ℝ b (φ z)) (fderiv ℂ φ z v) =
      C z (antiholomorphicValue (fderiv ℝ a z) v) := by
  have hleft := (hb.hasFDerivAt.comp z (hφ.hasFDerivAt.restrictScalars ℝ)).fderiv
  have hright := antiholomorphicValue_fderiv_pullback C (fderiv ℂ C z) a
    (fderiv ℝ a z) id (ContinuousLinearMap.id ℂ (ComplexModel d)) z hC.hasFDerivAt
    ha.hasFDerivAt (hasFDerivAt_id z) v
  have hpoint := heq.fderiv_eq (𝕜 := ℝ)
  simp only [id_eq, ContinuousLinearMap.id_apply] at hright
  rw [← hpoint, hleft] at hright
  simpa only [antiholomorphicValue, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul,
    ContinuousLinearMap.id_apply] using hright




/-- The antiholomorphic derivatives of vector coefficients satisfy the Dolbeault frame-change law on
chart overlaps. (Demailly, V §11, p.267) -/
private theorem preferredVectorCoefficients_antiholomorphic_change {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target)
    (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : (chartAt (ComplexModel d) a).symm z ∈ (chartAt (ComplexModel d) b).source)
    (v : ComplexModel d) :
    antiholomorphicValue
      (fderiv ℝ (preferredVectorCoefficients V b)
        ((chartAt (ComplexModel d) b) ((chartAt (ComplexModel d) a).symm z)))
      (preferredTransition a b z v) =
        preferredTransition a b z
          (antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V a) z) v) := by
  let φ := (chartAt (ComplexModel d) b) ∘ (chartAt (ComplexModel d) a).symm
  have hza := ((hV a).differentiableOn (by simp)).differentiableAt
    ((chartAt (ComplexModel d) a).open_target.mem_nhds hz)
  have hzb := ((hV b).differentiableOn (by simp)).differentiableAt
    ((chartAt (ComplexModel d) b).open_target.mem_nhds ((chartAt (ComplexModel d) b).map_source hb))
  have hC := (preferredTransition_holomorphicAt a b z hz hb).differentiableAt (by simp)
  have hφ := (preferredChartChange_holomorphicAt a b z hz hb).differentiableAt (by simp)
  have heq : (preferredVectorCoefficients V b ∘ φ) =ᶠ[nhds z]
      (fun w ↦ preferredTransition a b w (preferredVectorCoefficients V a w)) := by
    have hs := (chartAt (ComplexModel d) a).continuousAt_symm hz
    have hn := hs.preimage_mem_nhds ((chartAt (ComplexModel d) b).open_source.mem_nhds hb)
    filter_upwards [(chartAt (ComplexModel d) a).open_target.mem_nhds hz, hn] with w hw₁ hw₂
    exact preferredVectorCoefficients_change V a b w hw₁ hw₂
  have h := antiholomorphicValue_fderiv_change (preferredVectorCoefficients V a)
    (preferredVectorCoefficients V b) (preferredTransition a b) φ z hza hzb hC hφ heq v
  rw [← preferredTransition_eq_fderiv a b z hz hb] at h
  exact h

/-- The tangent frame transition is the target trivialization composed with the inverse source
trivialization. (Demailly, II §3.1, pp.85–86) -/
private theorem preferredTransition_apply {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : (chartAt (ComplexModel d) a).symm z ∈ (chartAt (ComplexModel d) b).source)
    (v : ComplexModel d) :
    preferredTransition a b z v =
      (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b).continuousLinearMapAt ℂ
        ((chartAt (ComplexModel d) a).symm z)
        ((trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a).symmL ℂ
          ((chartAt (ComplexModel d) a).symm z) v) := by
  let q := (chartAt (ComplexModel d) a).symm z
  let ta := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  let tb := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b
  have ha' : q ∈ ta.baseSet := (chartAt (ComplexModel d) a).map_target hz
  have hb' : q ∈ tb.baseSet := hb
  change (ta.coordChangeL ℂ tb q) v = tb.continuousLinearMapAt ℂ q (ta.symmL ℂ q v)
  rw [ta.coordChangeL_apply (R := ℂ) tb ⟨ha', hb'⟩,
    ta.symmL_apply ha', Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ tb hb']

/-- The coordinate coefficients of the Dolbeault tensor equal the antiholomorphic derivative of the
vector coefficients in every preferred chart. (Demailly, V §11, pp.267–268) -/
private theorem preferredAntilinearTensorCoefficients_antiholomorphic {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target)
    (a : X) (z : ComplexModel d) (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (v : ComplexModel d) :
    preferredAntilinearTensorCoefficients (vectorDolbeault V) a z v =
      antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V a) z) v := by
  let q := (chartAt (ComplexModel d) a).symm z
  let ta := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  let tq := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) q
  have hqa : q ∈ ta.baseSet := (chartAt (ComplexModel d) a).map_target hz
  have hqq : q ∈ tq.baseSet := mem_baseSet_trivializationAt _ _ q
  have h := preferredVectorCoefficients_antiholomorphic_change V hV a q z hz (mem_chart_source _ q) v
  change antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V q) ((chartAt (ComplexModel d) q) q))
    (preferredTransition a q z v) =
      preferredTransition a q z (antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V a) z) v) at h
  have hc (w : ComplexModel d) : preferredTransition a q z w =
      tq.continuousLinearMapAt ℂ q (ta.symmL ℂ q w) :=
    preferredTransition_apply a q z hz (mem_chart_source _ q) w
  rw [hc v, hc _] at h
  have h' := congrArg (fun w ↦ ta.continuousLinearMapAt ℂ q (tq.symmL ℂ q w)) h
  rw [tq.symmL_continuousLinearMapAt hqq, ta.continuousLinearMapAt_symmL hqa] at h'
  change ta.continuousLinearMapAt ℂ q (vectorDolbeault V q (ta.symmL ℂ q v)) = _
  rw [vectorDolbeault_antiholomorphic V q (preferredVectorCoefficients_differentiableAt V hV q)]
  exact h'

/-- The continuous conjugate-linear map associated with the antiholomorphic part of a real-linear
derivative. (Demailly, I §3.C, pp.22–24) -/
private def coordinateAntiholomorphicMap {d e : ℕ}
    (D : ComplexModel d →L[ℝ] ComplexModel e) : ComplexModel d →L⋆[ℂ] ComplexModel e :=
  (∑ k : Fin d, (ContinuousLinearMap.proj k).smulRight
    (antiholomorphicValue D (Pi.single k 1))).comp
    (starL ℂ : ComplexModel d ≃L⋆[ℂ] ComplexModel d).toContinuousLinearMap

/-- The assembled conjugate-linear map evaluates to the antiholomorphic part of the real-linear
derivative. (Demailly, I §3.C, pp.22–24) -/
private theorem coordinateAntiholomorphicMap_apply {d e : ℕ}
    (D : ComplexModel d →L[ℝ] ComplexModel e) (v : ComplexModel d) :
    coordinateAntiholomorphicMap D v = antiholomorphicValue D v := by
  rw [antiholomorphicValue_basis]
  simp only [coordinateAntiholomorphicMap, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, starL_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Pi.star_apply]

/-- The conjugate-linear coefficient map of the antiholomorphic derivative of a real smooth function
is real smooth. (Demailly, V §11, p.267) -/
private theorem coordinateAntiholomorphicMap_smooth {d e : ℕ}
    (a : ComplexModel d → ComplexModel e) (s : Set (ComplexModel d))
    (hs : IsOpen s) (ha : ContDiffOn ℝ ∞ a s) :
    ContDiffOn ℝ ∞ (fun z ↦ coordinateAntiholomorphicMap (fderiv ℝ a z)) s := by
  let composeStar : (ComplexModel d →L[ℂ] ComplexModel e) →L[ℂ]
      (ComplexModel d →L⋆[ℂ] ComplexModel e) :=
    (ContinuousLinearMap.compSL (ComplexModel d) (ComplexModel d) (ComplexModel e)
      (starRingEnd ℂ) (RingHom.id ℂ)).flip
        (starL ℂ : ComplexModel d ≃L⋆[ℂ] ComplexModel d).toContinuousLinearMap
  apply (composeStar.restrictScalars ℝ).contDiff.comp_contDiffOn
  apply ContDiffOn.sum
  intro k _
  let rankOne : ComplexModel e →L[ℂ] (ComplexModel d →L[ℂ] ComplexModel e) :=
    ContinuousLinearMap.smulRightL ℂ (ComplexModel d) (ComplexModel e)
      (ContinuousLinearMap.proj k)
  exact (rankOne.restrictScalars ℝ).contDiff.comp_contDiffOn
    (antiholomorphicValue_fderiv_smooth a s hs ha (Pi.single k 1))

/-- The Dolbeault tensor of a real smooth vector section has real smooth coefficients in every
chart. (Demailly, V §11, pp.267–268) -/
private theorem vectorDolbeault_tensor_smooth {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target) (a : X) :
    ContDiffOn ℝ ∞ (preferredAntilinearTensorCoefficients (vectorDolbeault V) a)
      (chartAt (ComplexModel d) a).target := by
  apply (coordinateAntiholomorphicMap_smooth (preferredVectorCoefficients V a)
    _ (chartAt (ComplexModel d) a).open_target (hV a)).congr
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  rw [coordinateAntiholomorphicMap_apply,
    preferredAntilinearTensorCoefficients_antiholomorphic V hV a z hz v]

/-- The coordinate expression of a biholomorphism in source and target preferred charts. (Zhang,
Lemma 4.3, p.15, equation (25)) -/
private def preferredMap {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    (f : Biholomorph d d X X) (a b : X) : ComplexModel d → ComplexModel d :=
  (chartAt (ComplexModel d) b) ∘ f ∘ (chartAt (ComplexModel d) a).symm

/-- The coordinate expression of a biholomorphism is complex smooth on its chart domain. (Zhang,
Lemma 4.3, p.15, equation (25)) -/
private theorem preferredMap_holomorphicAt {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X)
    (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : f ((chartAt (ComplexModel d) a).symm z) ∈ (chartAt (ComplexModel d) b).source) :
    ContDiffAt ℂ ∞ (preferredMap f a b) z := by
  have h₁ := contMDiffAt_of_mem_maximalAtlas (I := complexModel d) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas b) hb
  have h₂ := contMDiffAt_symm_of_mem_maximalAtlas (I := complexModel d) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas a) hz
  exact (h₁.comp z ((f.contMDiff.contMDiffAt).comp z h₂)).contDiffAt

/-- The coordinate Jacobian is the tangent derivative expressed in the source and target frames.
(Zhang, Lemma 4.3, p.15, equation (25)) -/
private theorem preferredMap_fderiv {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X)
    (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : f ((chartAt (ComplexModel d) a).symm z) ∈ (chartAt (ComplexModel d) b).source) :
    fderiv ℂ (preferredMap f a b) z =
      ((trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b).continuousLinearMapAt ℂ
        (f ((chartAt (ComplexModel d) a).symm z))).comp
      ((mfderiv (complexModel d) (complexModel d) f ((chartAt (ComplexModel d) a).symm z)).comp
        ((trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a).symmL ℂ
          ((chartAt (ComplexModel d) a).symm z))) := by
  let q := (chartAt (ComplexModel d) a).symm z
  have h₁ := (contMDiffAt_of_mem_maximalAtlas (I := complexModel d) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas b) hb).mdifferentiableAt (by simp)
  have h₂ := (contMDiffAt_symm_of_mem_maximalAtlas (I := complexModel d) (n := ∞)
    (IsManifold.chart_mem_maximalAtlas a) hz).mdifferentiableAt (by simp)
  have hf := f.contMDiff.mdifferentiable (by simp)
  have hc := mfderiv_comp z (h₁.comp q (hf q)) h₂
  have hd := mfderiv_comp q h₁ (hf q)
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hb,
    TangentBundle.symmL_trivializationAt ((chartAt (ComplexModel d) a).map_target hz)]
  simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_coe, complexModel, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.range_id, mfderivWithin_univ]
  change fderiv ℂ (preferredMap f a b) z =
    (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) b) (f q)).comp
      ((mfderiv (complexModel d) (complexModel d) f q).comp
        (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) a).symm
          ((chartAt (ComplexModel d) a) q)))
  have hq : (chartAt (ComplexModel d) a) q = z := (chartAt (ComplexModel d) a).right_inv hz
  rw [hq, ← ContinuousLinearMap.comp_assoc, ← hd]
  erw [← hc]
  exact (mfderiv_eq_fderiv (𝕜 := ℂ)).symm

/-- The coordinate Jacobian of a biholomorphism is invertible on its chart domain. (Zhang, Lemma
4.3, p.15, equations (24)–(25)) -/
private theorem preferredMap_fderiv_invertible {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X)
    (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : f ((chartAt (ComplexModel d) a).symm z) ∈ (chartAt (ComplexModel d) b).source) :
    (fderiv ℂ (preferredMap f a b) z).IsInvertible := by
  let q := (chartAt (ComplexModel d) a).symm z
  let ta := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  let tb := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b
  have hqa : q ∈ ta.baseSet := (chartAt (ComplexModel d) a).map_target hz
  have hfb : f q ∈ tb.baseSet := hb
  let A := ta.continuousLinearEquivAt ℂ q hqa
  let B := tb.continuousLinearEquivAt ℂ (f q) hfb
  let D := f.mfderivToContinuousLinearEquiv (by simp) q
  refine ⟨A.symm.trans (D.trans B), ?_⟩
  rw [preferredMap_fderiv f a b z hz hb]
  change ((B : TangentSpace (complexModel d) (f q) →L[ℂ] ComplexModel d).comp
    ((D : TangentSpace (complexModel d) q →L[ℂ] TangentSpace (complexModel d) (f q)).comp
      (A.symm : ComplexModel d →L[ℂ] TangentSpace (complexModel d) q))) = _
  rw [ta.symm_continuousLinearEquivAt_eq' hqa, tb.coe_continuousLinearEquivAt_eq' hfb]
  rfl

/-- The vector section obtained by multiplying the inverse tangent pullback by `ν`. (Zhang, Lemma
4.3, p.15, equation (24)) -/
private def normalizedPullbackSection {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    (f : Biholomorph d d X X) (ν : ℂ)
    (V : (x : X) → TangentSpace (complexModel d) x) :
    (x : X) → TangentSpace (complexModel d) x :=
  fun x ↦ ν • (mfderiv (complexModel d) (complexModel d) f x).inverse (V (f x))

/-- The normalized pullback section has coefficients given by the scaled inverse Jacobian applied to
the target section coefficients. (Zhang, Lemma 4.3, p.15, equations (24)–(25)) -/
private theorem normalizedPullbackSection_coefficients {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X) (ν : ℂ)
    (V : (x : X) → TangentSpace (complexModel d) x) (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : f ((chartAt (ComplexModel d) a).symm z) ∈ (chartAt (ComplexModel d) b).source) :
    preferredVectorCoefficients (normalizedPullbackSection f ν V) a z =
      ν • (fderiv ℂ (preferredMap f a b) z).inverse
        (preferredVectorCoefficients V b (preferredMap f a b z)) := by
  let q := (chartAt (ComplexModel d) a).symm z
  let ta := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  let tb := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b
  have hqa : q ∈ ta.baseSet := (chartAt (ComplexModel d) a).map_target hz
  have hfb : f q ∈ tb.baseSet := hb
  have hJ := preferredMap_fderiv_invertible f a b z hz hb
  have hF := f.isInvertible_mfderiv (x := q) (by simp)
  unfold preferredVectorCoefficients
  change (ta ⟨q, ν • (mfderiv (complexModel d) (complexModel d) f q).inverse (V (f q))⟩).2 =
    ν • (fderiv ℂ (preferredMap f a b) z).inverse
      ((tb ⟨(chartAt (ComplexModel d) b).symm ((chartAt (ComplexModel d) b) (f q)),
        V ((chartAt (ComplexModel d) b).symm ((chartAt (ComplexModel d) b) (f q)))⟩).2)
  rw [(chartAt (ComplexModel d) b).left_inv hb]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ ta hqa,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℂ tb hfb, map_smul]
  congr 1
  symm
  apply hJ.inverse_apply_eq.mpr
  rw [preferredMap_fderiv f a b z hz hb]
  change tb.continuousLinearMapAt ℂ (f q) (V (f q)) =
    tb.continuousLinearMapAt ℂ (f q) ((mfderiv (complexModel d) (complexModel d) f q)
      (ta.symmL ℂ q (ta.continuousLinearMapAt ℂ q
        ((mfderiv (complexModel d) (complexModel d) f q).inverse (V (f q))))))
  rw [ta.symmL_continuousLinearMapAt hqa, hF.self_apply_inverse]

/-- The normalized inverse tangent pullback of a real smooth vector section has real smooth
coefficients in every chart. (Zhang, Lemma 4.3, p.15, equations (24)–(25)) -/
private theorem normalizedPullbackSection_smooth {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X) (ν : ℂ)
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target) :
    ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients (normalizedPullbackSection f ν V) a)
      (chartAt (ComplexModel d) a).target := by
  intro a z hz
  let b := f ((chartAt (ComplexModel d) a).symm z)
  let φ := preferredMap f a b
  have hb : f ((chartAt (ComplexModel d) a).symm z) ∈ (chartAt (ComplexModel d) b).source :=
    mem_chart_source _ b
  have hφ := preferredMap_holomorphicAt f a b z hz hb
  have hJ := hφ.fderiv_right (m := ∞) (by simp)
  have hinv := ((preferredMap_fderiv_invertible f a b z hz hb).contDiffAt_map_inverse
    (n := ∞)).comp z hJ
  have hv := (hV b).contDiffAt ((chartAt (ComplexModel d) b).open_target.mem_nhds
    ((chartAt (ComplexModel d) b).map_source hb))
  have hcomp := hv.comp z (hφ.restrict_scalars ℝ)
  let evaluation := (ContinuousLinearMap.apply (E := ComplexModel d) ℂ (ComplexModel d)).flip.bilinearRestrictScalars ℝ
  have hresult := (evaluation.isBoundedBilinearMap.contDiff.comp₂_contDiffAt
    (hinv.restrict_scalars ℝ) hcomp).const_smul ν
  have heq : preferredVectorCoefficients (normalizedPullbackSection f ν V) a =ᶠ[nhds z]
      (fun w ↦ ν • (fderiv ℂ φ w).inverse (preferredVectorCoefficients V b (φ w))) := by
    have hc := f.continuous.continuousAt.comp ((chartAt (ComplexModel d) a).continuousAt_symm hz)
    have hn := hc.preimage_mem_nhds ((chartAt (ComplexModel d) b).open_source.mem_nhds hb)
    filter_upwards [(chartAt (ComplexModel d) a).open_target.mem_nhds hz, hn] with w hw₁ hw₂
    exact normalizedPullbackSection_coefficients f ν V a b w hw₁ hw₂
  exact (hresult.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The Dolbeault tensor is given by the antiholomorphic derivative of the vector coefficients in
any chart containing the point. (Demailly, V §11, pp.267–268) -/
theorem vectorDolbeault_chart {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target)
    (a : X) (z : ComplexModel d) (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (v : TangentSpace (complexModel d) ((chartAt (ComplexModel d) a).symm z)) :
    let q := (chartAt (ComplexModel d) a).symm z
    let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
    vectorDolbeault V q v = t.symmL ℂ q
      (antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V a) z)
        (t.continuousLinearMapAt ℂ q v)) := by
  dsimp only
  let q := (chartAt (ComplexModel d) a).symm z
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  have hq : q ∈ t.baseSet := (chartAt (ComplexModel d) a).map_target hz
  have h := preferredAntilinearTensorCoefficients_antiholomorphic V hV a z hz
    (t.continuousLinearMapAt ℂ q v)
  change t.continuousLinearMapAt ℂ q
    (vectorDolbeault V q (t.symmL ℂ q (t.continuousLinearMapAt ℂ q v))) = _ at h
  rw [t.symmL_continuousLinearMapAt hq] at h
  have h' := congrArg (t.symmL ℂ q) h
  rw [t.symmL_continuousLinearMapAt hq] at h'
  exact h'

/-- The antiholomorphic derivative of the normalized pullback coefficients is the scaled inverse
Jacobian composed with the target antiholomorphic derivative and the source Jacobian. (Zhang,
Lemma 4.3, p.15, equation (25)) -/
private theorem normalizedPullbackSection_antiholomorphic {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X) (ν : ℂ)
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target)
    (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : f ((chartAt (ComplexModel d) a).symm z) ∈ (chartAt (ComplexModel d) b).source)
    (v : ComplexModel d) :
    antiholomorphicValue
      (fderiv ℝ (preferredVectorCoefficients (normalizedPullbackSection f ν V) a) z) v =
    ν • (fderiv ℂ (preferredMap f a b) z).inverse
      (antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V b) (preferredMap f a b z))
        (fderiv ℂ (preferredMap f a b) z v)) := by
  let φ := preferredMap f a b
  let C := fun w ↦ (fderiv ℂ φ w).inverse
  have hφ := preferredMap_holomorphicAt f a b z hz hb
  have hJ := hφ.fderiv_right (m := ∞) (by simp)
  have hC := ((preferredMap_fderiv_invertible f a b z hz hb).contDiffAt_map_inverse
    (n := ∞)).comp z hJ
  have hv := ((hV b).differentiableOn (by simp)).differentiableAt
    ((chartAt (ComplexModel d) b).open_target.mem_nhds ((chartAt (ComplexModel d) b).map_source hb))
  have hc := hC.differentiableAt (by simp)
  have hp := hφ.differentiableAt (by simp)
  let evaluation := (ContinuousLinearMap.apply (E := ComplexModel d) ℂ (ComplexModel d)).flip.bilinearRestrictScalars ℝ
  have hprod := evaluation.hasFDerivAt_of_bilinear (hc.hasFDerivAt.restrictScalars ℝ)
    (hv.hasFDerivAt.comp z (hp.hasFDerivAt.restrictScalars ℝ))
  change HasFDerivAt (fun w ↦ C w (preferredVectorCoefficients V b (φ w))) _ z at hprod
  have heq : preferredVectorCoefficients (normalizedPullbackSection f ν V) a =ᶠ[nhds z]
      (fun w ↦ ν • C w (preferredVectorCoefficients V b (φ w))) := by
    have hcont := f.continuous.continuousAt.comp ((chartAt (ComplexModel d) a).continuousAt_symm hz)
    have hn := hcont.preimage_mem_nhds ((chartAt (ComplexModel d) b).open_source.mem_nhds hb)
    filter_upwards [(chartAt (ComplexModel d) a).open_target.mem_nhds hz, hn] with w hw₁ hw₂
    exact normalizedPullbackSection_coefficients f ν V a b w hw₁ hw₂
  have hsmul := (hprod.const_smul ν).fderiv
  rw [← hprod.fderiv] at hsmul
  change fderiv ℝ (fun w ↦ ν • C w (preferredVectorCoefficients V b (φ w))) z =
    ν • fderiv ℝ (fun w ↦ C w (preferredVectorCoefficients V b (φ w))) z at hsmul
  rw [heq.fderiv_eq (𝕜 := ℝ), hsmul, antiholomorphicValue_output_smul]
  exact congrArg (fun w ↦ ν • w) (antiholomorphicValue_fderiv_pullback C
    (fderiv ℂ C z) (preferredVectorCoefficients V b)
    (fderiv ℝ (preferredVectorCoefficients V b) (φ z)) φ (fderiv ℂ φ z) z
    hc.hasFDerivAt hv.hasFDerivAt hp.hasFDerivAt v)

/-- The Dolbeault tensor of the normalized pullback satisfies the inverse tangent pullback formula
in source and target charts. (Zhang, Lemma 4.3, p.15, equation (25); Demailly, V §11, p.267) -/
private theorem normalizedPullbackSection_dolbeault_chart {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X) (ν : ℂ)
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target)
    (a b : X) (z : ComplexModel d)
    (hz : z ∈ (chartAt (ComplexModel d) a).target)
    (hb : f ((chartAt (ComplexModel d) a).symm z) ∈ (chartAt (ComplexModel d) b).source)
    (v : TangentSpace (complexModel d) ((chartAt (ComplexModel d) a).symm z)) :
    let q := (chartAt (ComplexModel d) a).symm z
    vectorDolbeault (normalizedPullbackSection f ν V) q v =
      ν • (mfderiv (complexModel d) (complexModel d) f q).inverse
        (vectorDolbeault V (f q) (mfderiv (complexModel d) (complexModel d) f q v)) := by
  dsimp only
  let q := (chartAt (ComplexModel d) a).symm z
  let ta := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
  let tb := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) b
  let φ := preferredMap f a b
  let J := fderiv ℂ φ z
  let F := mfderiv (complexModel d) (complexModel d) f q
  have hqa : q ∈ ta.baseSet := (chartAt (ComplexModel d) a).map_target hz
  have hfb : f q ∈ tb.baseSet := hb
  have hJ := preferredMap_fderiv_invertible f a b z hz hb
  have hF := f.isInvertible_mfderiv (x := q) (by simp)
  have hP := vectorDolbeault_chart (normalizedPullbackSection f ν V)
    (normalizedPullbackSection_smooth f ν V hV) a z hz v
  have hVout : vectorDolbeault V (f q) (F v) = tb.symmL ℂ (f q)
      (antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V b) (φ z))
        (tb.continuousLinearMapAt ℂ (f q) (F v))) := by
    have h := vectorDolbeault_chart V hV b (φ z)
      ((chartAt (ComplexModel d) b).map_source hb)
    dsimp only at h
    have hbase : (chartAt (ComplexModel d) b).symm (φ z) = f q :=
      (chartAt (ComplexModel d) b).left_inv hb
    rw [hbase] at h
    exact h (F v)
  rw [hP, hVout, normalizedPullbackSection_antiholomorphic f ν V hV a b z hz hb, map_smul]
  have hJv : J (ta.continuousLinearMapAt ℂ q v) = tb.continuousLinearMapAt ℂ (f q) (F v) := by
    change fderiv ℂ (preferredMap f a b) z (ta.continuousLinearMapAt ℂ q v) = _
    rw [preferredMap_fderiv f a b z hz hb]
    change tb.continuousLinearMapAt ℂ (f q) (F (ta.symmL ℂ q (ta.continuousLinearMapAt ℂ q v))) = _
    rw [ta.symmL_continuousLinearMapAt hqa]
  change ν • ta.symmL ℂ q (J.inverse
      (antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V b) (φ z))
        (J (ta.continuousLinearMapAt ℂ q v)))) =
    ν • F.inverse (tb.symmL ℂ (f q)
      (antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V b) (φ z))
        (tb.continuousLinearMapAt ℂ (f q) (F v))))
  rw [hJv]
  congr 1
  let w := antiholomorphicValue (fderiv ℝ (preferredVectorCoefficients V b) (φ z))
    (tb.continuousLinearMapAt ℂ (f q) (F v))
  change ta.symmL ℂ q (J.inverse w) = F.inverse (tb.symmL ℂ (f q) w)
  symm
  apply hF.inverse_apply_eq.mpr
  have hj : tb.continuousLinearMapAt ℂ (f q) (F (ta.symmL ℂ q (J.inverse w))) = w := by
    have heq : J = (tb.continuousLinearMapAt ℂ (f q)).comp (F.comp (ta.symmL ℂ q)) :=
      preferredMap_fderiv f a b z hz hb
    exact (congrArg (fun L ↦ L (J.inverse w)) heq.symm).trans (hJ.self_apply_inverse w)
  have h := congrArg (tb.symmL ℂ (f q)) hj
  rw [tb.symmL_continuousLinearMapAt hfb] at h
  exact h.symm

/-- The Dolbeault tensor of the normalized pullback equals the scaled inverse tangent derivative
composed with the target Dolbeault tensor and the tangent derivative. (Zhang, Lemma 4.3, p.15,
equation (25)) -/
private theorem normalizedPullbackSection_dolbeault {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (f : Biholomorph d d X X) (ν : ℂ)
    (V : (x : X) → TangentSpace (complexModel d) x)
    (hV : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients V a)
      (chartAt (ComplexModel d) a).target)
    (x : X) (v : TangentSpace (complexModel d) x) :
    vectorDolbeault (normalizedPullbackSection f ν V) x v =
      ν • (mfderiv (complexModel d) (complexModel d) f x).inverse
        (vectorDolbeault V (f x) (mfderiv (complexModel d) (complexModel d) f x v)) := by
  have hx := mem_chart_source (ComplexModel d) x
  have hz := (chartAt (ComplexModel d) x).map_source hx
  have hb : f ((chartAt (ComplexModel d) x).symm ((chartAt (ComplexModel d) x) x)) ∈
      (chartAt (ComplexModel d) (f x)).source := by
    rw [(chartAt (ComplexModel d) x).left_inv hx]
    exact mem_chart_source _ (f x)
  have h := normalizedPullbackSection_dolbeault_chart f ν V hV x (f x)
    ((chartAt (ComplexModel d) x) x) hz hb
  dsimp only at h
  rw [(chartAt (ComplexModel d) x).left_inv hx] at h
  exact h v

/-- The normalized inverse-derivative sections are smooth, pair to one with `θ`, and have smooth
Dolbeault tensors valued in `ker θ`. These tensors satisfy the scaled pullback formula through
the kernel derivative equivalence and the conjugate tangent map. (Zhang, Lemma 4.3, p.15,
equations (24)–(26)) -/
theorem normalized_vector_dolbeault_pullback
    {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (θ : ComplexOneForm d X)
    (hθ : IsHolomorphicComplexOneForm θ) (_hθzero : ∀ x : X, θ x ≠ 0)
    (μ : ℂ) (hμ : μ ≠ 0)
    (hscale : ∀ (x : X) (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (e₀ : (x : X) → TangentSpace (complexModel d) x)
    (hsmooth : ∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients e₀ a)
      (chartAt (ComplexModel d) a).target)
    (hnormalized : ∀ x : X, θ x (e₀ x) = 1) :
    let F : (n : ℕ) → (x : X) → TangentSpace (complexModel d) x →L[ℂ]
        TangentSpace (complexModel d) (((f : X → X)^[n]) x) :=
      fun n x ↦ mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x
    let U := fun x : X ↦ LinearMap.ker (θ x).toLinearMap
    let e : ℕ → (x : X) → TangentSpace (complexModel d) x :=
      fun n x ↦ μ ^ n • (F n x).inverse (e₀ (((f : X → X)^[n]) x))
    (∀ (n : ℕ) (x : X), (F n x).IsInvertible) ∧
    ∃ B₀ : (x : X) → TangentSpace (complexModel d) x →L⋆[ℂ] U x,
      (∀ (x : X) (v : TangentSpace (complexModel d) x),
        (B₀ x v : TangentSpace (complexModel d) x) = vectorDolbeault e₀ x v) ∧
      (∀ a : X, ContDiffOn ℝ ∞
        (preferredAntilinearTensorCoefficients (vectorDolbeault e₀) a)
        (chartAt (ComplexModel d) a).target) ∧
      ∀ n : ℕ,
        (∀ a : X, ContDiffOn ℝ ∞ (preferredVectorCoefficients (e n) a)
          (chartAt (ComplexModel d) a).target) ∧
        (∀ x : X, θ x (e n x) = 1) ∧
        ∃ Uₙ : (x : X) → U x ≃L[ℂ] U (((f : X → X)^[n]) x),
          (∀ (x : X) (u : U x),
            (Uₙ x u : TangentSpace (complexModel d) (((f : X → X)^[n]) x)) = F n x u) ∧
          ∃ Bₙ : (x : X) → TangentSpace (complexModel d) x →L⋆[ℂ] U x,
            (∀ (x : X) (v : TangentSpace (complexModel d) x),
              (Bₙ x v : TangentSpace (complexModel d) x) = vectorDolbeault (e n) x v) ∧
            ∀ x : X,
              Bₙ x = μ ^ n • (((Uₙ x).symm.toContinuousLinearMap.comp
                (B₀ (((f : X → X)^[n]) x))).comp (F n x)) := by
  dsimp only
  let F := fun (n : ℕ) (x : X) ↦
    mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x
  let U := fun x : X ↦ LinearMap.ker (θ x).toLinearMap
  let e := fun (n : ℕ) (x : X) ↦ μ ^ n • (F n x).inverse (e₀ ((f : X → X)^[n] x))
  have hkernel := vectorDolbeault_normalized_kernel θ hθ e₀ hsmooth hnormalized
  have htensor := vectorDolbeault_tensor_smooth e₀ hsmooth
  have hcoordinate :
      (∀ (n : ℕ) (a : X), ContDiffOn ℝ ∞ (preferredVectorCoefficients (e n) a)
        (chartAt (ComplexModel d) a).target) ∧
      (∀ (n : ℕ) (x : X) (v : TangentSpace (complexModel d) x),
        vectorDolbeault (e n) x v =
          μ ^ n • (F n x).inverse
            (vectorDolbeault e₀ ((f : X → X)^[n] x) (F n x v))) := by
    constructor
    · intro n
      have h := normalizedPullbackSection_smooth (normalizedIterate f n) (μ ^ n) e₀ hsmooth
      unfold normalizedPullbackSection at h
      rw [normalizedIterate_coe f n] at h
      exact h
    · intro n x v
      have h := normalizedPullbackSection_dolbeault (normalizedIterate f n) (μ ^ n) e₀ hsmooth x v
      unfold normalizedPullbackSection at h
      rw [normalizedIterate_coe f n] at h
      exact h
  obtain ⟨hsection, hpullback⟩ := hcoordinate
  let B₀ : (x : X) → TangentSpace (complexModel d) x →L⋆[ℂ] U x :=
    fun x ↦ (vectorDolbeault e₀ x).codRestrict (U x) (fun v ↦ hkernel x v)
  refine ⟨normalizedIterate_invertible f, B₀, ?_, htensor, ?_⟩
  · intro x v
    rfl
  · intro n
    obtain ⟨Uₙ, hUₙ⟩ := normalizedIterate_kernel_equiv f θ μ hμ hscale n
    refine ⟨hsection n, normalizedIterate_normalized f θ μ hscale e₀ hnormalized n,
      Uₙ, hUₙ, ?_⟩
    let Bₙ : (x : X) → TangentSpace (complexModel d) x →L⋆[ℂ] U x :=
      fun x ↦ μ ^ n • (((Uₙ x).symm.toContinuousLinearMap.comp
        (B₀ ((f : X → X)^[n] x))).comp (F n x))
    refine ⟨Bₙ, ?_, fun _ ↦ rfl⟩
    intro x v
    have hinverse (u : U ((f : X → X)^[n] x)) :
        ((Uₙ x).symm u : TangentSpace (complexModel d) x) = (F n x).inverse u := by
      symm
      apply (normalizedIterate_invertible f n x).inverse_apply_eq.mpr
      rw [← hUₙ x ((Uₙ x).symm u), ContinuousLinearEquiv.apply_symm_apply]
    change μ ^ n • ((Uₙ x).symm (B₀ ((f : X → X)^[n] x) (F n x v)) :
      TangentSpace (complexModel d) x) = vectorDolbeault (e n) x v
    rw [hinverse, hpullback]
    rfl


end
end HolomorphicAnosov
