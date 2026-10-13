import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.HermitianMetricVolumeJacobian
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.RealTangentTopForm
import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Tactic.FinCases
import HolomorphicAnosov.Geometry.ComplexToRealManifold

/-! This file constructs a smooth Hermitian metric making a normalized section unit and orthogonal
to the one-form kernel, and computes the real Jacobian of iterates. (Zhang, Lemma 4.3, p.15,
equation (27); Demailly, VI §4, pp.296–297, and I §1.B.5, p.10) -/

open scoped ContDiff Manifold
open Module Bundle

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X]

/-- The coefficient of a complex cotangent field in a holomorphic coordinate frame. (Demailly, I
§3.C, pp.23–25) -/
noncomputable def cotangentChartCoefficient
    (θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (e : OpenPartialHomeomorph X (ComplexModel d)) (i : Fin d)
    (z : ComplexModel d) : ℂ :=
  θ (e.symm z) (hermitianTangentChartFrame e z i)

/-- The coordinate coefficient of a tangent section in a holomorphic chart. (Zhang, p.15; Demailly,
I §3.C) -/
noncomputable def tangentSectionChartCoefficient
    (s : ∀ x : X, TangentSpace (complexModel d) x)
    (e : OpenPartialHomeomorph X (ComplexModel d)) (i : Fin d)
    (z : ComplexModel d) : ℂ :=
  NormedSpace.fromTangentSpace (e (e.symm z))
    (mfderiv (complexModel d) (complexModel d) e (e.symm z) (s (e.symm z))) i

/-- The matrix of the differential between kernel bases after projecting its target by `v ↦ v − θ(v)
• e₀`. (Zhang, p.15) -/
noncomputable def normalizedKernelMatrix
    (θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (e₀ : ∀ x : X, TangentSpace (complexModel d) x)
    (he₀ : ∀ x, θ x (e₀ x) = 1) (F : X → X) (x : X)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bs : Basis ι ℂ (LinearMap.ker (θ x).toLinearMap))
    (bt : Basis ι ℂ (LinearMap.ker (θ (F x)).toLinearMap)) : Matrix ι ι ℂ :=
  fun i j => bt.repr ⟨
    mfderiv (complexModel d) (complexModel d) F x (bs j) -
      θ (F x) (mfderiv (complexModel d) (complexModel d) F x (bs j)) • e₀ (F x),
    by simp [he₀]⟩ i

/-- A kernel basis is orthonormal for the Hermitian pairing, which is complex-linear in its first
argument. (Zhang, p.15) -/
def IsHermitianKernelUnitary (h : HermitianTangentMetricCore d X)
    (θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ) (x : X)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ (LinearMap.ker (θ x).toLinearMap)) : Prop :=
  ∀ i j, hermitianTangentPairing h x (b i) (b j) = if i = j then 1 else 0

set_option backward.isDefEq.respectTransparency false in
/-- There exists a smooth Hermitian metric making `e₀` unit and orthogonal to `ker θ`; every such
metric determines a unique positive real volume form. The real Jacobian of the nth iterate is
`‖μ‖ ^ (2 * n)` times the squared modulus of the determinant of its kernel differential in
unitary bases. (Zhang, Lemma 4.3, p.15, equation (27); Demailly, VI §4, pp.296–297, and I
§1.B.5, p.10) -/
theorem normalized_hermitian_jacobian
    [CompactSpace X] [T2Space X] [IsManifold (complexModel d) ∞ X]
    (θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ : ∀ e : OpenPartialHomeomorph X (ComplexModel d),
      e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ∀ i : Fin d, ContDiffOn ℂ ∞ (cotangentChartCoefficient θ e i) e.target)
    (hθnonzero : ∀ x, θ x ≠ 0)
    (e₀ : ∀ x : X, TangentSpace (complexModel d) x)
    (he₀smooth : ∀ e : OpenPartialHomeomorph X (ComplexModel d),
      e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ∀ i : Fin d, ContDiffOn ℝ ∞ (tangentSectionChartCoefficient e₀ e i) e.target)
    (he₀ : ∀ x, θ x (e₀ x) = 1)
    (f : Biholomorph d d X X) (μ : ℂ) (hμ : μ ≠ 0)
    (hθpull : ∀ x v, θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) =
      μ * θ x v) :
    (∃ h : HermitianTangentMetricCore d X,
      IsSmoothHermitianTangentMetric h ∧
      (∀ x, hermitianTangentPairing h x (e₀ x) (e₀ x) = 1) ∧
      (∀ x v, θ x v = 0 → hermitianTangentPairing h x v (e₀ x) = 0)) ∧
    ∀ h : HermitianTangentMetricCore d X, IsSmoothHermitianTangentMetric h →
      (∀ x, hermitianTangentPairing h x (e₀ x) (e₀ x) = 1) →
      (∀ x v, θ x v = 0 → hermitianTangentPairing h x v (e₀ x) = 0) →
      (∀ n x v, θ x v = 0 →
        θ ((f : X → X)^[n] x)
          (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x v) = 0) ∧
      ∃! ν : RealTangentTopForm d X,
        IsSmoothPositiveRealTangentTopForm ν ∧
        (∀ e : OpenPartialHomeomorph X (ComplexModel d),
          e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
          ∀ z ∈ e.target, realTangentTopFormChartCoefficient ν e z =
            (Matrix.det (fun i j : Fin d => hermitianTangentChartCoefficient h e i j z)).re) ∧
        ∀ n : ℕ, ∃! J : X → ℝ,
          ContMDiff (realModel d) 𝓘(ℝ, ℝ) ∞ J ∧ (∀ x, 0 < J x) ∧
          realTangentTopFormPullback ((f : X → X)^[n]) ν = realTangentTopFormScale J ν ∧
          ∀ (x : X) (ι : Type) [Fintype ι] [DecidableEq ι]
            (bs : Basis ι ℂ (LinearMap.ker (θ x).toLinearMap))
            (bt : Basis ι ℂ (LinearMap.ker (θ ((f : X → X)^[n] x)).toLinearMap)),
            IsHermitianKernelUnitary h θ x bs →
            IsHermitianKernelUnitary h θ ((f : X → X)^[n] x) bt →
            J x = ‖μ‖ ^ (2 * n) *
              ‖Matrix.det (normalizedKernelMatrix θ e₀ he₀ ((f : X → X)^[n]) x bs bt)‖ ^ 2 := by
  have _ := hθnonzero
  have _ := hμ
  have hrmanifold : IsManifold (realModel d) ∞ X := complex_isManifold_real d X
  have hvb : VectorBundle ℝ (ComplexModel d)
      (fun x : X ↦ TangentSpace (complexModel d) x) := by
    let hlin (e : Trivialization (ComplexModel d)
        (Bundle.TotalSpace.proj : TangentBundle (complexModel d) X → X))
        [MemTrivializationAtlas e] : e.IsLinear ℝ :=
      ⟨fun b hb ↦ ((e.linearEquivAt ℂ b hb).toLinearMap.restrictScalars ℝ).isLinear⟩
    refine { trivialization_linear' := hlin, continuousOn_coordChange' := ?_ }
    intro e e' _ _
    have hc := continuousOn_coordChange ℂ e e'
    have hc' := (ContinuousLinearMap.restrictScalarsIsometry ℂ (ComplexModel d)
      (ComplexModel d) ℝ ℝ).continuous.comp_continuousOn hc
    apply hc'.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro v
    change (e.coordChangeL ℝ e' x) v = (e.coordChangeL ℂ e' x) v
    rw [Trivialization.coordChangeL_apply e e' hx v,
      Trivialization.coordChangeL_apply e e' hx v]
  have hsb : ContMDiffVectorBundle ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (complexModel d) x) (realModel d) := by
    refine ⟨?_⟩
    intro e e' _ _
    have hc := contMDiffOn_coordChangeL (n := ∞) (𝕜 := ℂ) (IB := complexModel d) e e'
    have hr : ContMDiffOn (realModel d) 𝓘(ℝ, ComplexModel d →L[ℂ] ComplexModel d) ∞
        (fun x ↦ (e.coordChangeL ℂ e' x : ComplexModel d →L[ℂ] ComplexModel d))
        (e.baseSet ∩ e'.baseSet) := by
      intro x hx
      obtain ⟨hcont, hd⟩ := contMDiffWithinAt_iff.mp (hc x hx)
      exact contMDiffWithinAt_iff.mpr ⟨hcont, hd.restrict_scalars ℝ⟩
    have hr' := (ContinuousLinearMap.restrictScalarsIsometry ℂ (ComplexModel d)
      (ComplexModel d) ℝ ℝ).toContinuousLinearMap.contMDiff.comp_contMDiffOn hr
    apply hr'.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro v
    change (e.coordChangeL ℝ e' x) v = (e.coordChangeL ℂ e' x) v
    rw [Trivialization.coordChangeL_apply e e' hx v,
      Trivialization.coordChangeL_apply e e' hx v]
  obtain ⟨g, hgpair, hgframe, hgtopology⟩ :=
    smooth_complex_bundle_hermitian_metric (B := ComplexModel d)
      (M := X) (E := fun x ↦ TangentSpace (complexModel d) x) d
  have hrealchart : ∀ (e : OpenPartialHomeomorph X (ComplexModel d)),
      e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContMDiffOn (realModel d) (realModel d) ∞ e e.source ∧
      ContMDiffOn (realModel d) (realModel d) ∞ e.symm e.target := by
    intro e he
    constructor
    · intro x hx
      obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp ((contMDiffOn_of_mem_maximalAtlas he) x hx)
      exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
    · intro z hz
      obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp ((contMDiffOn_symm_of_mem_maximalAtlas he) z hz)
      exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
  have he0section : ContMDiff (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
      (fun x ↦ TotalSpace.mk' (ComplexModel d) x (e₀ x)) := by
    intro x
    let e := chartAt (ComplexModel d) x
    have he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
      IsManifold.chart_mem_maximalAtlas x
    have hco : ContDiffOn ℝ ∞ (fun z ↦ fun i ↦ tangentSectionChartCoefficient e₀ e i z) e.target :=
      contDiffOn_pi.mpr (he₀smooth e he)
    have hcoords := hco.contMDiffOn.comp (hrealchart e he).1 e.mapsTo
    apply (Trivialization.contMDiffAt_section_iff (trivializationAt (ComplexModel d)
      (TangentSpace (complexModel d)) x) (FiberBundle.mem_baseSet_trivializationAt _ _ x)).mpr
    apply (hcoords x (mem_chart_source _ x)).contMDiffAt (e.open_source.mem_nhds (mem_chart_source _ x)) |>.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds (mem_chart_source _ x)] with y hy
    have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := complexModel d) hy
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℂ _ hy]
    rw [ht]
    simp only [e, extChartAt, complexModel, Function.id_comp,
      tangentSectionChartCoefficient, OpenPartialHomeomorph.extend, mfld_simps]
    rw [(chartAt (ComplexModel d) x).left_inv hy]
    rfl
  have hframesection : ∀ (e : OpenPartialHomeomorph X (ComplexModel d)),
      e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X → ∀ i : Fin d,
      ContMDiffOn (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
        (fun x ↦ TotalSpace.mk' (E := fun x : X ↦ TangentSpace (complexModel d) x) (ComplexModel d) x (hermitianTangentChartFrame e (e x) i)) e.source := by
    intro e he i
    have hs := contMDiffOn_symm_of_mem_maximalAtlas he
    have htm := hs.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      e.open_target.uniqueMDiffOn
    have hinput : ContMDiffOn (complexModel d) ((complexModel d).tangent) ∞
        (fun x ↦ (tangentBundleModelSpaceHomeomorph (complexModel d)).symm
          (e x, Pi.single i 1)) e.source :=
      contMDiff_tangentBundleModelSpaceHomeomorph_symm.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas he).prodMk_space contMDiffOn_const)
    have hc := htm.comp hinput (fun x hx ↦ e.map_source hx)
    have hc' : ContMDiffOn (complexModel d) ((complexModel d).prod 𝓘(ℂ, ComplexModel d)) ∞
        (fun x ↦ TotalSpace.mk' (E := fun x : X ↦ TangentSpace (complexModel d) x) (ComplexModel d) x (hermitianTangentChartFrame e (e x) i)) e.source := by
      apply hc.congr
      intro x hx
      simp only [Function.comp_apply, tangentBundleModelSpaceHomeomorph_coe_symm,
        tangentMapWithin]
      dsimp only [TotalSpace.toProd, Equiv.coe_fn_symm_mk]
      rw [mfderivWithin_eq_mfderiv (e.open_target.uniqueMDiffOn _ (e.map_source hx))
        (((hs _ (e.map_source hx)).contMDiffAt (e.open_target.mem_nhds (e.map_source hx))).mdifferentiableAt (by simp))]
      simp only [hermitianTangentChartFrame]
      apply TotalSpace.ext (e.left_inv hx).symm
      rfl
    intro x hx
    obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (hc' x hx)
    exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
  let proj (x : X) : TangentSpace (complexModel d) x →ₗ[ℂ]
      TangentSpace (complexModel d) x :=
    LinearMap.id - (LinearMap.smulRight (θ x).toLinearMap (e₀ x))
  have hprojectedsection : ∀ (e : OpenPartialHomeomorph X (ComplexModel d)),
      e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X → ∀ i : Fin d,
      ContMDiffOn (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
        (fun x ↦ TotalSpace.mk' (ComplexModel d) x
          (proj x (hermitianTangentChartFrame e (e x) i))) e.source := by
    intro e he i
    have ha := ((hθ e he i).restrict_scalars ℝ).contMDiffOn.comp
      (hrealchart e he).1 e.mapsTo
    have hs := hframesection e he i
    intro x hx
    let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
    have htx := FiberBundle.mem_baseSet_trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
    have hs' := (t.contMDiffWithinAt_section e.source htx).mp (hs x hx)
    have ht' := (t.contMDiffWithinAt_section e.source htx).mp (he0section x).contMDiffWithinAt
    apply (t.contMDiffWithinAt_section e.source htx).mpr
    have hsm := contDiff_smul.comp_contMDiffWithinAt ((ha x hx).prodMk_space ht')
    apply (hs'.sub hsm).congr_of_eventuallyEq
    · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (t.open_baseSet.mem_nhds htx), self_mem_nhdsWithin] with y hy hye
      change (t ⟨y, proj y (hermitianTangentChartFrame e (e y) i)⟩).2 = _
      simp only [Function.comp_apply]
      simp_rw [← t.continuousLinearMapAt_apply_of_mem ℂ hy]
      simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        ContinuousLinearMap.coe_coe, map_sub, map_smul, cotangentChartCoefficient]
      rw [e.left_inv hye]
    · change (t ⟨x, proj x (hermitianTangentChartFrame e (e x) i)⟩).2 = _
      simp only [Function.comp_apply]
      simp_rw [← t.continuousLinearMapAt_apply_of_mem ℂ htx]
      simp only [proj, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        ContinuousLinearMap.coe_coe, map_sub, map_smul, cotangentChartCoefficient]
      rw [e.left_inv hx]
  let hncore : HermitianTangentMetricCore d X := fun x ↦
    { inner := fun v w ↦ (g x).inner (proj x v) (proj x w) +
        starRingEnd ℂ (θ x v) * θ x w
      conj_inner_symm := by
        intro v w
        simp only [map_add, map_mul, (g x).conj_inner_symm,
          RingHomCompTriple.comp_apply, RingHom.id_apply]
        ring
      re_inner_nonneg := by
        intro v
        have hg : 0 ≤ ((g x).inner (proj x v) (proj x v)).re :=
          (g x).re_inner_nonneg (proj x v)
        change 0 ≤ ((g x).inner (proj x v) (proj x v) +
          starRingEnd ℂ (θ x v) * θ x v).re
        simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
        nlinarith [sq_nonneg (θ x v).re, sq_nonneg (θ x v).im]
      add_left := by
        intro v w z
        simp only [map_add, (g x).add_left, add_mul]
        abel
      smul_left := by
        intro v w c
        simp only [map_smul, (g x).smul_left, smul_eq_mul, map_mul]
        ring
      definite := by
        intro v hv
        have hz := congrArg Complex.re hv
        simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.zero_re] at hz
        have hg : 0 ≤ ((g x).inner (proj x v) (proj x v)).re :=
          (g x).re_inner_nonneg (proj x v)
        have hre : (θ x v).re = 0 := by nlinarith [sq_nonneg (θ x v).im]
        have him : (θ x v).im = 0 := by nlinarith [sq_nonneg (θ x v).re]
        have hθv : θ x v = 0 := Complex.ext hre him
        have hpinner : (g x).inner (proj x v) (proj x v) = 0 := by
          simpa only [hθv, map_zero, zero_mul, add_zero] using hv
        have hpzero := (g x).definite _ hpinner
        simpa [proj, hθv] using hpzero }
  have hnunit : ∀ x, hermitianTangentPairing hncore x (e₀ x) (e₀ x) = 1 := by
    intro x
    have hp : proj x (e₀ x) = 0 := by simp [proj, he₀]
    change (g x).inner (proj x (e₀ x)) (proj x (e₀ x)) +
      starRingEnd ℂ (θ x (e₀ x)) * θ x (e₀ x) = 1
    rw [hp, he₀]
    have hz := (g x).add_left (0 : TangentSpace (complexModel d) x) 0 0
    simp only [zero_add] at hz
    have hzero : (g x).inner 0 0 = 0 := (add_eq_left.mp hz.symm)
    simp [hzero]
  have hnorth : ∀ x v, θ x v = 0 →
      hermitianTangentPairing hncore x v (e₀ x) = 0 := by
    intro x v hv
    have hp : proj x (e₀ x) = 0 := by simp [proj, he₀]
    change (g x).inner (proj x (e₀ x)) (proj x v) +
      starRingEnd ℂ (θ x (e₀ x)) * θ x v = 0
    rw [hp, hv, mul_zero, add_zero]
    have hz := (g x).add_left (0 : TangentSpace (complexModel d) x) 0 (proj x v)
    simp only [zero_add] at hz
    exact (add_eq_left.mp hz.symm)
  have hnsmooth : IsSmoothHermitianTangentMetric hncore := by
    intro e he i j
    let si : ∀ x : X, TangentSpace (complexModel d) x :=
      fun x ↦ proj x (hermitianTangentChartFrame e (e x) i)
    let sj : ∀ x : X, TangentSpace (complexModel d) x :=
      fun x ↦ proj x (hermitianTangentChartFrame e (e x) j)
    have hgp := hgpair e.source e.open_source si sj
      (hprojectedsection e he i) (hprojectedsection e he j)
    have hc := (hgp.comp (hrealchart e he).2 e.mapsTo_symm).contDiffOn
    have hi := (hθ e he i).restrict_scalars ℝ
    have hj := (hθ e he j).restrict_scalars ℝ
    have hp := (Complex.conjCLE.contDiff.comp_contDiffOn hj).mul hi
    apply (hc.add hp).congr
    intro z hz
    change (g (e.symm z)).inner
        (proj (e.symm z) (hermitianTangentChartFrame e z j))
        (proj (e.symm z) (hermitianTangentChartFrame e z i)) +
        starRingEnd ℂ (θ (e.symm z) (hermitianTangentChartFrame e z j)) *
          θ (e.symm z) (hermitianTangentChartFrame e z i) = _
    simp only [Function.comp_apply, si, sj]
    rw [e.right_inv hz]
    rfl
  have hpull : ∀ n x v,
      θ ((f : X → X)^[n] x)
        (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x v) =
          μ ^ n * θ x v := by
    intro n
    induction n with
    | zero =>
      intro x v
      simp only [Function.iterate_zero, id_eq, mfderiv_id,
        pow_zero, one_mul]
      rfl
    | succ n ih =>
      intro x v
      rw [Function.iterate_succ]
      rw [mfderiv_comp_apply x
        ((f.contMDiff.iterate n).mdifferentiable (by simp) (f x))
        (f.mdifferentiable (by simp) x)]
      rw [Function.comp_apply, ih, hθpull, pow_succ]
      ring
  have hkernel : ∀ n x v, θ x v = 0 →
      θ ((f : X → X)^[n] x)
        (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x v) = 0 := by
    intro n x v hv
    rw [hpull, hv, mul_zero]
  have hsplit : ∀ x : X, ∃ e : TangentSpace (complexModel d) x ≃ₗ[ℂ]
      (LinearMap.ker (θ x).toLinearMap × ℂ),
      (∀ v, (e v).2 = θ x v) ∧
      (∀ w, e.symm w = (w.1 : TangentSpace (complexModel d) x) + w.2 • e₀ x) := by
    intro x
    let p : TangentSpace (complexModel d) x → LinearMap.ker (θ x).toLinearMap :=
      fun v ↦ ⟨v - θ x v • e₀ x, by simp [he₀]⟩
    let e : TangentSpace (complexModel d) x ≃ₗ[ℂ]
        (LinearMap.ker (θ x).toLinearMap × ℂ) :=
      { toFun := fun v ↦ (p v, θ x v)
        invFun := fun w ↦ w.1 + w.2 • e₀ x
        left_inv := by
          intro v
          change v - θ x v • e₀ x + θ x v • e₀ x = v
          exact sub_add_cancel _ _
        right_inv := by
          intro w
          have hw : θ x (w.1 : TangentSpace (complexModel d) x) = 0 := w.1.property
          apply Prod.ext
          · apply Subtype.ext
            simp [p, hw, he₀]
          · simp [hw, he₀]
        map_add' := by
          intro v w
          apply Prod.ext
          · apply Subtype.ext
            change (v + w) - θ x (v + w) • e₀ x =
              (v - θ x v • e₀ x) + (w - θ x w • e₀ x)
            rw [map_add, add_smul]
            abel
          · exact map_add (θ x) v w
        map_smul' := by
          intro c v
          apply Prod.ext
          · apply Subtype.ext
            simp [p, smul_sub, mul_smul]
          · exact map_smul (θ x) c v }
    exact ⟨e, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hfullbasis : ∀ (x : X) (ι : Type) [Fintype ι] [DecidableEq ι]
      (bs : Basis ι ℂ (LinearMap.ker (θ x).toLinearMap)),
      ∃ b : Basis (ι ⊕ Unit) ℂ (TangentSpace (complexModel d) x),
        (∀ i, b (Sum.inl i) = (bs i : TangentSpace (complexModel d) x)) ∧
        b (Sum.inr ()) = e₀ x := by
    intro x ι _ _ bs
    obtain ⟨e, he, hinv⟩ := hsplit x
    let b := (bs.prod (Basis.singleton Unit ℂ)).map e.symm
    refine ⟨b, ?_, ?_⟩
    · intro i
      simp only [b, Basis.map_apply, Basis.prod_apply, Sum.elim_inl]
      rw [hinv]
      simp
    · simp only [b, Basis.map_apply, Basis.prod_apply, Sum.elim_inr]
      rw [hinv]
      simp
  have hunitarybasis : ∀ (h : HermitianTangentMetricCore d X),
      (∀ x, hermitianTangentPairing h x (e₀ x) (e₀ x) = 1) →
      (∀ x v, θ x v = 0 → hermitianTangentPairing h x v (e₀ x) = 0) →
      ∀ (x : X) (ι : Type) [Fintype ι] [DecidableEq ι]
        (bs : Basis ι ℂ (LinearMap.ker (θ x).toLinearMap)),
      IsHermitianKernelUnitary h θ x bs →
      ∃ b : Basis (ι ⊕ Unit) ℂ (TangentSpace (complexModel d) x),
        (∀ i, b (Sum.inl i) = (bs i : TangentSpace (complexModel d) x)) ∧
        b (Sum.inr ()) = e₀ x ∧
        ∀ i j, hermitianTangentPairing h x (b i) (b j) = if i = j then 1 else 0 := by
    intro h hn ho x ι _ _ bs hbs
    obtain ⟨b, hb, he⟩ := hfullbasis x ι bs
    refine ⟨b, hb, he, ?_⟩
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa only [hb, Sum.inl.injEq] using hbs i j
      | inr j =>
        cases j
        simp only [hb, he, Sum.inl_ne_inr, ite_false]
        exact ho x (bs i) (bs i).property
    | inr i =>
      cases i
      cases j with
      | inl j =>
        simp only [hb, he, Sum.inr_ne_inl, ite_false]
        have hj := ho x (bs j) (bs j).property
        change (h x).inner (bs j) (e₀ x) = 0
        rw [← (h x).conj_inner_symm]
        change starRingEnd ℂ (hermitianTangentPairing h x (bs j) (e₀ x)) = 0
        rw [hj, map_zero]
      | inr j =>
        cases j
        simpa only [he, ite_true] using hn x
  have hblockdet : ∀ (n : ℕ) (x : X) (ι : Type) [Fintype ι] [DecidableEq ι]
      (bs : Basis ι ℂ (LinearMap.ker (θ x).toLinearMap))
      (bt : Basis ι ℂ (LinearMap.ker (θ ((f : X → X)^[n] x)).toLinearMap)),
      ∃ (b : Basis (ι ⊕ Unit) ℂ (TangentSpace (complexModel d) x))
        (c : Basis (ι ⊕ Unit) ℂ (TangentSpace (complexModel d) ((f : X → X)^[n] x))),
        (∀ i, b (Sum.inl i) = (bs i : TangentSpace (complexModel d) x)) ∧
        b (Sum.inr ()) = e₀ x ∧
        (∀ i, c (Sum.inl i) = (bt i : TangentSpace (complexModel d) ((f : X → X)^[n] x))) ∧
        c (Sum.inr ()) = e₀ ((f : X → X)^[n] x) ∧
        Matrix.det (LinearMap.toMatrix b c
          (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x).toLinearMap) =
          Matrix.det (normalizedKernelMatrix θ e₀ he₀ ((f : X → X)^[n]) x bs bt) * μ ^ n := by
    intro n x ι _ _ bs bt
    obtain ⟨es, hes, hs⟩ := hsplit x
    obtain ⟨et, het, ht⟩ := hsplit ((f : X → X)^[n] x)
    let b := (bs.prod (Basis.singleton Unit ℂ)).map es.symm
    let c := (bt.prod (Basis.singleton Unit ℂ)).map et.symm
    have hb : ∀ i, b (Sum.inl i) = (bs i : TangentSpace (complexModel d) x) := by
      intro i
      simp only [b, Basis.map_apply, Basis.prod_apply, Sum.elim_inl]
      rw [hs]
      simp
    have hb0 : b (Sum.inr ()) = e₀ x := by
      simp only [b, Basis.map_apply, Basis.prod_apply, Sum.elim_inr]
      rw [hs]
      simp
    have hc : ∀ i, c (Sum.inl i) = (bt i : TangentSpace (complexModel d) ((f : X → X)^[n] x)) := by
      intro i
      simp only [c, Basis.map_apply, Basis.prod_apply, Sum.elim_inl]
      rw [ht]
      simp
    have hc0 : c (Sum.inr ()) = e₀ ((f : X → X)^[n] x) := by
      simp only [c, Basis.map_apply, Basis.prod_apply, Sum.elim_inr]
      rw [ht]
      simp
    let T := mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x
    have hfirst : ∀ v, (et v).1 = ⟨v - θ ((f : X → X)^[n] x) v • e₀ ((f : X → X)^[n] x), by simp [he₀]⟩ := by
      intro v
      apply Subtype.ext
      have hv := ht (et v)
      rw [et.symm_apply_apply, het] at hv
      change (et v).1.val = v - θ ((f : X → X)^[n] x) v • e₀ ((f : X → X)^[n] x)
      exact (eq_sub_iff_add_eq).mpr hv.symm
    have hm : LinearMap.toMatrix b c T.toLinearMap =
        Matrix.fromBlocks (normalizedKernelMatrix θ e₀ he₀ ((f : X → X)^[n]) x bs bt)
          (fun i (_ : Unit) ↦ c.repr (T (e₀ x)) (Sum.inl i))
          0 (fun (_ _ : Unit) ↦ μ ^ n) := by
      ext i j
      cases i with
      | inl i =>
        cases j with
        | inl j =>
          rw [LinearMap.toMatrix_apply, hb]
          change bt.repr (et (T (bs j))).1 i = _
          rw [hfirst]
          rfl
        | inr j =>
          cases j
          simp only [LinearMap.toMatrix_apply, hb0, Matrix.fromBlocks_apply₁₂]
          rfl
      | inr i =>
        cases i
        cases j with
        | inl j =>
          rw [LinearMap.toMatrix_apply, hb]
          simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
          change (Basis.singleton Unit ℂ).repr (et (T (bs j))).2 () = 0
          rw [Basis.singleton_repr]
          rw [het]
          exact hkernel n x (bs j) (bs j).property
        | inr j =>
          cases j
          rw [LinearMap.toMatrix_apply, hb0]
          simp only [Matrix.fromBlocks_apply₂₂]
          change (Basis.singleton Unit ℂ).repr (et (T (e₀ x))).2 () = μ ^ n
          rw [Basis.singleton_repr]
          rw [het, hpull, he₀, mul_one]
    refine ⟨b, c, hb, hb0, hc, hc0, ?_⟩
    change Matrix.det (LinearMap.toMatrix b c T.toLinearMap) = _
    rw [hm]
    rw [Matrix.det_fromBlocks_zero₂₁]
    congr 1
    exact Matrix.det_unique (fun (_ _ : Unit) ↦ μ ^ n)
  have hiterate : ∀ n : ℕ, ∃ F : Biholomorph d d X X,
      (F : X → X) = (f : X → X)^[n] := by
    intro n
    induction n with
    | zero => exact ⟨Diffeomorph.refl (complexModel d) X ∞, rfl⟩
    | succ n ih =>
      obtain ⟨F, hF⟩ := ih
      exact ⟨f.trans F, by simp only [Diffeomorph.coe_trans, hF, Function.iterate_succ]⟩
  have hcard : ∀ (x : X) (ι : Type) [Fintype ι]
      (b : Basis ι ℂ (TangentSpace (complexModel d) x)), Fintype.card ι = d := by
    intro x ι _ b
    rw [← Module.finrank_eq_card_basis b]
    change Module.finrank ℂ (Fin d → ℂ) = d
    simp
  have hreindexdet : ∀ (x y : X) (ι : Type) [Fintype ι] [DecidableEq ι]
      (b : Basis ι ℂ (TangentSpace (complexModel d) x))
      (c : Basis ι ℂ (TangentSpace (complexModel d) y))
      (T : TangentSpace (complexModel d) x →ₗ[ℂ] TangentSpace (complexModel d) y)
      (e : ι ≃ Fin d),
      Matrix.det (LinearMap.toMatrix (b.reindex e) (c.reindex e) T) =
        Matrix.det (LinearMap.toMatrix b c T) := by
    intro x y ι _ _ b c T e
    have hm : LinearMap.toMatrix (b.reindex e) (c.reindex e) T =
        Matrix.reindex e e (LinearMap.toMatrix b c T) := by
      ext i j
      simp only [LinearMap.toMatrix_apply, Basis.reindex_apply, Basis.repr_reindex_apply,
        Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hm, Matrix.det_reindex_self]
  have hjacobian : ∀ (h : HermitianTangentMetricCore d X),
      IsSmoothHermitianTangentMetric h →
      (∀ x, hermitianTangentPairing h x (e₀ x) (e₀ x) = 1) →
      (∀ x v, θ x v = 0 → hermitianTangentPairing h x v (e₀ x) = 0) →
      ∀ n : ℕ, ∃! J : X → ℝ,
        ContMDiff (realModel d) 𝓘(ℝ, ℝ) ∞ J ∧ (∀ x, 0 < J x) ∧
        realTangentTopFormPullback ((f : X → X)^[n]) (hermitianMetricPreferredTopForm h) =
          realTangentTopFormScale J (hermitianMetricPreferredTopForm h) ∧
        ∀ (x : X) (ι : Type) [Fintype ι] [DecidableEq ι]
          (bs : Basis ι ℂ (LinearMap.ker (θ x).toLinearMap))
          (bt : Basis ι ℂ (LinearMap.ker (θ ((f : X → X)^[n] x)).toLinearMap)),
          IsHermitianKernelUnitary h θ x bs →
          IsHermitianKernelUnitary h θ ((f : X → X)^[n] x) bt →
          J x = ‖μ‖ ^ (2 * n) *
            ‖Matrix.det (normalizedKernelMatrix θ e₀ he₀ ((f : X → X)^[n]) x bs bt)‖ ^ 2 := by
    intro h hh hu ho n
    obtain ⟨F, hF⟩ := hiterate n
    obtain ⟨J, hJs, hJp, hJe, hJu, hJdet⟩ := (hermitian_metric_volume_jacobian h hh).2.2.2 F
    refine ⟨J, ⟨hJs, hJp, by simpa only [hF] using hJe, ?_⟩, ?_⟩
    · intro x ι _ _ bs bt hbs hbt
      obtain ⟨b, c, hb, hb0, hc, hc0, hdet⟩ := hblockdet n x ι bs bt
      obtain ⟨b', hb', hb0', hbu⟩ := hunitarybasis h hu ho x ι bs hbs
      obtain ⟨c', hc', hc0', hcu⟩ := hunitarybasis h hu ho ((f : X → X)^[n] x) ι bt hbt
      have hbb : b = b' := by
        apply DFunLike.ext
        intro i
        cases i with
        | inl i => rw [hb, hb']
        | inr i => cases i; rw [hb0, hb0']
      have hcc : c = c' := by
        apply DFunLike.ext
        intro i
        cases i with
        | inl i => rw [hc, hc']
        | inr i => cases i; rw [hc0, hc0']
      have e : (ι ⊕ Unit) ≃ Fin d := Fintype.equivFinOfCardEq (hcard x _ b)
      have hbu' : ∀ i j, hermitianTangentPairing h x
          ((b.reindex e) i) ((b.reindex e) j) = if i = j then 1 else 0 := by
        intro i j
        simpa only [Basis.reindex_apply, hbb, Equiv.injective e.symm |>.eq_iff] using hbu (e.symm i) (e.symm j)
      have hcu' : ∀ i j, hermitianTangentPairing h ((f : X → X)^[n] x)
          ((c.reindex e) i) ((c.reindex e) j) = if i = j then 1 else 0 := by
        intro i j
        simpa only [Basis.reindex_apply, hcc, Equiv.injective e.symm |>.eq_iff] using hcu (e.symm i) (e.symm j)
      have hd : J x = ‖Matrix.det (LinearMap.toMatrix (b.reindex e) (c.reindex e)
          (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x).toLinearMap)‖ ^ 2 := by
        have hj := hJdet x
        rw [hF] at hj
        exact hj _ _ hbu' hcu'
      rw [hreindexdet, hdet, norm_mul, mul_pow, norm_pow] at hd
      rw [hd, pow_mul]
      ring
    · intro J' hJ'
      apply hJu
      simpa only [hF] using hJ'.2.2.1
  have htopformext : ∀ ν ν' : RealTangentTopForm d X,
      (∀ (e : OpenPartialHomeomorph X (ComplexModel d)),
        e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X → ∀ z ∈ e.target,
        realTangentTopFormChartCoefficient ν e z = realTangentTopFormChartCoefficient ν' e z) → ν = ν' := by
    intro ν ν' hν
    funext x
    let e := chartAt (ComplexModel d) x
    have hx : x ∈ e.source := mem_chart_source _ x
    have he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
      IsManifold.chart_mem_maximalAtlas x
    have hdiff : e.MDifferentiable (realModel d) (realModel d) :=
      mdifferentiable_chart x
    have hid : mfderiv (realModel d) (realModel d) e x = ContinuousLinearMap.id ℝ _ := by
      simpa only [extChartAt, realModel, OpenPartialHomeomorph.extend, mfld_simps] using
        (mfderiv_extChartAt_self (I := realModel d) (x := x))
    have hdi : mfderiv (realModel d) (realModel d) e.symm (e x) = ContinuousLinearMap.id ℝ _ := by
      have hc := hdiff.symm_comp_deriv hx
      rw [hid, ContinuousLinearMap.comp_id] at hc
      exact hc
    let b : Basis (ComplexPairedIndex d) ℝ (TangentSpace (realModel d) x) :=
      (Pi.basis (fun _ : Fin d ↦ Complex.basisOneI)).reindex (Equiv.sigmaEquivProd (Fin d) (Fin 2))
    have hb : ∀ i : ComplexPairedIndex d,
        b i = Pi.single i.1 (if i.2 = 0 then 1 else Complex.I) := by
      rintro ⟨i, j⟩
      calc
        b (i, j) = (Pi.basis (fun _ : Fin d ↦ Complex.basisOneI)) ⟨i, j⟩ :=
          (Pi.basis (fun _ : Fin d ↦ Complex.basisOneI)).reindex_apply
            (Equiv.sigmaEquivProd (Fin d) (Fin 2)) (i, j)
        _ = Pi.single i (Complex.basisOneI j) :=
          Pi.basis_apply (fun _ : Fin d ↦ Complex.basisOneI) ⟨i, j⟩
        _ = Pi.single i (if j = 0 then 1 else Complex.I) := by
          congr 1
          fin_cases j <;> simp [Complex.coe_basisOneI]
    have heval : ν x b = ν' x b := by
      have hc := hν e he (e x) (e.map_source hx)
      change ν (e.symm (e x)) (realTangentPairedChartFrame e (e x)) =
        ν' (e.symm (e x)) (realTangentPairedChartFrame e (e x)) at hc
      have hf : realTangentPairedChartFrame e (e x) = b := by
        funext i
        simp only [realTangentPairedChartFrame, hdi, hb]
        rfl
      rw [hf, e.left_inv hx] at hc
      exact hc
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    apply b.ext_alternating
    intro v hv
    let σ : Equiv.Perm (ComplexPairedIndex d) :=
      Equiv.ofBijective v ((Finite.injective_iff_bijective).mp hv)
    change ν x (b ∘ σ) = ν' x (b ∘ σ)
    rw [← ContinuousAlternatingMap.coe_toAlternatingMap, ← ContinuousAlternatingMap.coe_toAlternatingMap]
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm]
    exact congrArg (fun r : ℝ ↦ Equiv.Perm.sign σ • r) heval
  refine ⟨⟨hncore, hnsmooth, hnunit, hnorth⟩, ?_⟩
  intro h hh hu ho
  refine ⟨hkernel, ?_⟩
  obtain ⟨hvs, hvc, hvu, hvj⟩ := hermitian_metric_volume_jacobian h hh
  refine ⟨hermitianMetricPreferredTopForm h, ⟨hvs, ?_, hjacobian h hh hu ho⟩, ?_⟩
  · intro e he z hz
    exact (hvc e he z hz).2.2
  · intro ν hν
    apply htopformext
    intro e he z hz
    rw [hν.2.1 e he z hz]
    exact (hvc e he z hz).2.2.symm

end HolomorphicAnosov
