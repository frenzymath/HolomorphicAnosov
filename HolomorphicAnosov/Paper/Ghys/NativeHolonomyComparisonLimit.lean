import HolomorphicAnosov.Geometry.HolomorphicCoordinateOrientationG18
import HolomorphicAnosov.Geometry.NativeUnstableIntrinsicContractionG18
import HolomorphicAnosov.Geometry.IntrinsicPiecewiseC1PathReversal
import HolomorphicAnosov.Geometry.HermitianLeafPathMap
import HolomorphicAnosov.Geometry.ComplexMDerivativeRealification
import Mathlib.Analysis.InnerProductSpace.Basic
import HolomorphicAnosov.Paper.Ghys.NativeUnstableComplexRankOneFromRealRankTwo
import HolomorphicAnosov.Geometry.IntrinsicChartFirstExit
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Convex.Topology
import HolomorphicAnosov.Paper.Ghys.NativeUnstableIterateHolomorphic



noncomputable section
namespace HolomorphicAnosov.Ghys

/-- In an injective complex-linear frame, a Hermitian norm is a positive scalar multiple of complex
modulus. (Demailly, VI §4, pp. 296–297; Ghys, Prop. 2.2, p. 590) -/
theorem hermitian_line_norm_scale
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (h : InnerProductSpace.Core ℂ E) (A : ℂ →ₗ[ℂ] E) (hA : Function.Injective A) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ,
      Real.sqrt ((h.inner (A z) (A z)).re) = ρ * ‖z‖ := by
  let : InnerProductSpace.Core ℂ E := h
  let : Norm E := InnerProductSpace.Core.toNorm (𝕜 := ℂ)
  let ρ := Real.sqrt ((h.inner (A 1) (A 1)).re)
  have hne : A 1 ≠ 0 := by
    intro he
    have he' : A 1 = A 0 := by simpa using he
    exact one_ne_zero (hA he')
  have hρ : 0 < ρ := by
    have hnonneg : 0 ≤ ρ := Real.sqrt_nonneg _
    have hzero : ρ = 0 ↔ A 1 = 0 := h.toNormedSpaceCore.norm_eq_zero_iff (A 1)
    exact lt_of_le_of_ne hnonneg (Ne.symm (hzero.not.mpr hne))
  refine ⟨ρ, hρ, ?_⟩
  intro z
  have hz : A z = z • A 1 := by
    simpa using (A.map_smul z (1 : ℂ))
  rw [hz]
  exact (h.toNormedSpaceCore.norm_smul z (A 1)).trans (mul_comm _ _)

end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v

/-- In an injective complex-linear frame on `ComplexModel 1`, a Hermitian norm is a positive scalar
multiple of the model norm. (Demailly, VI §4, pp. 296–297) -/
theorem hermitian_model_one_norm_scale
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (h : InnerProductSpace.Core ℂ E) (A : ComplexModel 1 →ₗ[ℂ] E)
    (hA : Function.Injective A) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ComplexModel 1,
      Real.sqrt ((h.inner (A z) (A z)).re) = ρ * ‖z‖ := by
  let e := LinearEquiv.funUnique (Fin 1) ℂ ℂ
  obtain ⟨ρ, hρ, hscale⟩ := hermitian_line_norm_scale h (A.comp e.symm.toLinearMap)
    (hA.comp e.symm.injective)
  refine ⟨ρ, hρ, ?_⟩
  intro z
  have hz : z = fun _ ↦ z 0 := by
    funext i
    exact congrArg z (Subsingleton.elim i 0)
  rw [hz]
  have hs := hscale (z 0)
  change Real.sqrt ((h.inner (A (fun _ ↦ z 0)) (A (fun _ ↦ z 0))).re) = ρ * ‖z 0‖ at hs
  simpa only [pi_norm_const] using hs

/-- A holomorphic curve parametrization has a positive Hermitian length density for derivatives in
the real leaf atlas. (Ghys, pp. 589–590; Demailly, I §3.C, p. 23, VI §4, pp. 296–297) -/
theorem hermitian_native_coordinate_norm_scale
    {r d : ℕ} {X : Type u} {M : Type v}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : X → M) (h : HermitianTangentMetricCore d M)
    (c : ComplexModel 1 → X) (a : ComplexModel 1)
    (hinc : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) (realModel d) inc (c a))
    (hc : MDifferentiableAt (realModel 1) 𝓘(ℝ, Fin r → ℝ) c a)
    (hφ : MDifferentiableAt (complexModel 1) (complexModel d) (inc ∘ c) a)
    (hinj : Function.Injective (mfderiv (complexModel 1) (complexModel d) (inc ∘ c) a)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : ComplexModel 1,
      leafPullbackHermitianNorm inc h (c a)
        (mfderiv (realModel 1) 𝓘(ℝ, Fin r → ℝ) c a
          (complexTangentToReal 1 a ((tangentSpaceCastModel (complexModel 1) a).symm v))) =
        ρ * ‖v‖ := by
  let D := mfderiv (complexModel 1) (complexModel d) (inc ∘ c) a
  let T := (tangentSpaceCastModel (complexModel 1) a).symm
  obtain ⟨ρ, hρ, hscale⟩ := hermitian_model_one_norm_scale (h (inc (c a)))
    (D.toLinearMap.comp T.toLinearEquiv.toLinearMap) (hinj.comp T.injective)
  refine ⟨ρ, hρ, ?_⟩
  intro v
  have hchain := mfderiv_comp (I := realModel 1) (I' := 𝓘(ℝ, Fin r → ℝ))
    (I'' := realModel d) a hinc hc
  have he := mfderiv_complex_to_real hφ (T v)
  rw [hchain, ContinuousLinearMap.comp_apply] at he
  unfold leafPullbackHermitianNorm leafPullbackHermitianPairing hermitianTangentRealPairing
  rw [he]
  simp only [hermitianTangentPairing]
  exact hscale v

end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold _root_.Topology
universe u v

/-- The pullback Hermitian norm in a holomorphic curve chart is a positive scalar multiple of the
coordinate norm. (Ghys, p. 590; Demailly, I §3.C, VI §4) -/
theorem hermitian_coordinate_norm_scale
    {r d : ℕ} {X : Type u} {M : Type v}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : X → M) (h : HermitianTangentMetricCore d M)
    (e : OpenPartialHomeomorph X (ComplexModel 1)) {x : X} (hx : x ∈ e.source)
    (hinc : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) (realModel d) inc x)
    (he : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x)
    (hc : MDifferentiableAt (realModel 1) 𝓘(ℝ, Fin r → ℝ) e.symm (e x))
    (hφ : MDifferentiableAt (complexModel 1) (complexModel d) (inc ∘ e.symm) (e x))
    (hinj : Function.Injective
      (mfderiv (complexModel 1) (complexModel d) (inc ∘ e.symm) (e x))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) x,
      leafPullbackHermitianNorm inc h x v =
        ρ * ‖(tangentSpaceCastModel (realModel 1) (e x))
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x v)‖ := by
  obtain ⟨ρ, hρ, hs⟩ := hermitian_native_coordinate_norm_scale inc h e.symm (e x)
    (by simpa only [e.left_inv hx] using hinc) hc hφ hinj
  have hid : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    exact e.left_inv hz
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, Fin r → ℝ)) (I' := realModel 1)
    (I'' := 𝓘(ℝ, Fin r → ℝ)) x hc he
  rw [hid.mfderiv_eq, mfderiv_id] at hcomp
  refine ⟨ρ, hρ, ?_⟩
  intro v
  have hs' := hs ((tangentSpaceCastModel (realModel 1) (e x))
    (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x v))
  have hvec : complexTangentToReal 1 (e x)
      ((tangentSpaceCastModel (complexModel 1) (e x)).symm
        ((tangentSpaceCastModel (realModel 1) (e x))
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x v))) =
      mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x v := by
    rfl
  rw [hvec] at hs'
  have hv := congrArg (fun D ↦ D v) hcomp
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at hv
  rw [← hv] at hs'
  change leafPullbackHermitianNorm inc h (e.symm (e x)) v = _ at hs'
  exact (congrArg (fun z : X ↦ leafPullbackHermitianNorm inc h z v)
    (e.left_inv hx)).symm.trans hs'

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v w

/-- Two-sided Hermitian leaf-norm estimates induce scaled two-sided estimates for the coordinate
derivative. (Ghys, p. 590) -/
theorem hermitian_coordinate_comparison
    {r s d : ℕ} {X : Type u} {Y : Type v} {M : Type w}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [TopologicalSpace Y] [ChartedSpace (Fin s → ℝ) Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (incX : X → M) (incY : Y → M) (h : HermitianTangentMetricCore d M)
    (c : ComplexModel 1 → X) (e : Y → ComplexModel 1) (g : X → Y)
    (a : ComplexModel 1) (α β ε : ℝ)
    (hc : MDifferentiableAt (realModel 1) 𝓘(ℝ, Fin r → ℝ) c a)
    (hg : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g (c a))
    (he : MDifferentiableAt 𝓘(ℝ, Fin s → ℝ) (realModel 1) e (g (c a)))
    (hs : ∀ v : ComplexModel 1,
      leafPullbackHermitianNorm incX h (c a)
        (mfderiv (realModel 1) 𝓘(ℝ, Fin r → ℝ) c a
          ((tangentSpaceCastModel (realModel 1) a).symm v)) = α * ‖v‖)
    (ht : ∀ v : TangentSpace 𝓘(ℝ, Fin s → ℝ) (g (c a)),
      leafPullbackHermitianNorm incY h (g (c a)) v =
        β * ‖(tangentSpaceCastModel (realModel 1) (e (g (c a))))
          (mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel 1) e (g (c a)) v)‖)
    (hbound : ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) (c a),
      (1 - ε) * leafPullbackHermitianNorm incX h (c a) v ≤
        leafPullbackHermitianNorm incY h (g (c a))
          (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g (c a) v) ∧
      leafPullbackHermitianNorm incY h (g (c a))
          (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g (c a) v) ≤
        (1 + ε) * leafPullbackHermitianNorm incX h (c a) v) :
    ∀ v : ComplexModel 1,
      (1 - ε) * α * ‖v‖ ≤ β * ‖fderiv ℝ (e ∘ g ∘ c) a v‖ ∧
      β * ‖fderiv ℝ (e ∘ g ∘ c) a v‖ ≤ (1 + ε) * α * ‖v‖ := by
  intro v
  have hb := hbound (mfderiv (realModel 1) 𝓘(ℝ, Fin r → ℝ) c a
    ((tangentSpaceCastModel (realModel 1) a).symm v))
  rw [hs v, ht] at hb
  have hgc := mfderiv_comp (I := realModel 1) (I' := 𝓘(ℝ, Fin r → ℝ))
    (I'' := 𝓘(ℝ, Fin s → ℝ)) a hg hc
  have hall := mfderiv_comp (I := realModel 1) (I' := 𝓘(ℝ, Fin s → ℝ))
    (I'' := realModel 1) a he (hg.comp a hc)
  rw [hgc] at hall
  have hv := congrArg (fun D ↦ D ((tangentSpaceCastModel (realModel 1) a).symm v)) hall
  rw [mfderiv_eq_fderiv] at hv
  change fderiv ℝ (e ∘ g ∘ c) a v =
    (tangentSpaceCastModel (realModel 1) (e (g (c a))))
      (mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel 1) e (g (c a))
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g (c a)
          (mfderiv (realModel 1) 𝓘(ℝ, Fin r → ℝ) c a
            ((tangentSpaceCastModel (realModel 1) a).symm v)))) at hv
  rw [← hv] at hb
  simpa only [mul_assoc] using hb

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v
/-- The Hermitian length of a real tangent vector under a holomorphic curve parametrization equals a
positive density times its coordinate norm. (Ghys, pp. 589–590; Demailly, I §3.C, p. 23, VI §4,
pp. 296–297) -/
theorem hermitian_native_coordinate_density_formula
    {r d : ℕ} {X : Type u} {M : Type v}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : X → M) (h : HermitianTangentMetricCore d M)
    (c : ComplexModel 1 → X) (a : ComplexModel 1)
    (hinc : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) (realModel d) inc (c a))
    (hc : MDifferentiableAt (realModel 1) 𝓘(ℝ, Fin r → ℝ) c a)
    (hφ : MDifferentiableAt (complexModel 1) (complexModel d) (inc ∘ c) a)
    (hinj : Function.Injective (mfderiv (complexModel 1) (complexModel d) (inc ∘ c) a)) :
    let ρ := Real.sqrt ((h (inc (c a))).inner
      (mfderiv (complexModel 1) (complexModel d) (inc ∘ c) a
        ((tangentSpaceCastModel (complexModel 1) a).symm (1 : ComplexModel 1)))
      (mfderiv (complexModel 1) (complexModel d) (inc ∘ c) a
        ((tangentSpaceCastModel (complexModel 1) a).symm (1 : ComplexModel 1)))).re
    0 < ρ ∧ ∀ v : ComplexModel 1,
      leafPullbackHermitianNorm inc h (c a)
        (mfderiv (realModel 1) 𝓘(ℝ, Fin r → ℝ) c a
          (complexTangentToReal 1 a ((tangentSpaceCastModel (complexModel 1) a).symm v))) =
        ρ * ‖v‖ := by
  let D := mfderiv (complexModel 1) (complexModel d) (inc ∘ c) a
  let T := (tangentSpaceCastModel (complexModel 1) a).symm
  obtain ⟨ρ, hρ, hscale⟩ := hermitian_model_one_norm_scale (h (inc (c a)))
    (D.toLinearMap.comp T.toLinearEquiv.toLinearMap) (hinj.comp T.injective)
  have hρeq := hscale (1 : ComplexModel 1)
  have hone : ‖(1 : ComplexModel 1)‖ = 1 := by
    change ‖fun _ : Fin 1 ↦ (1 : ℂ)‖ = 1
    simp only [pi_norm_const, norm_one]
  rw [hone, mul_one] at hρeq
  change Real.sqrt ((h (inc (c a))).inner (D (T 1)) (D (T 1))).re = ρ at hρeq
  dsimp only
  rw [hρeq]
  refine ⟨hρ, ?_⟩
  intro v
  have hchain := mfderiv_comp (I := realModel 1) (I' := 𝓘(ℝ, Fin r → ℝ))
    (I'' := realModel d) a hinc hc
  have he := mfderiv_complex_to_real hφ (T v)
  rw [hchain, ContinuousLinearMap.comp_apply] at he
  unfold leafPullbackHermitianNorm leafPullbackHermitianPairing hermitianTangentRealPairing
  rw [he]
  simp only [hermitianTangentPairing]
  exact hscale v

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold _root_.Topology
universe u v
/-- In a holomorphic curve chart, the pullback Hermitian norm equals a positive density times the
norm of the coordinate derivative. (Ghys, p. 590; Demailly, I §3.C, VI §4) -/
theorem hermitian_coordinate_density_formula
    {r d : ℕ} {X : Type u} {M : Type v}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : X → M) (h : HermitianTangentMetricCore d M)
    (e : OpenPartialHomeomorph X (ComplexModel 1)) {x : X} (hx : x ∈ e.source)
    (hinc : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) (realModel d) inc x)
    (he : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x)
    (hc : MDifferentiableAt (realModel 1) 𝓘(ℝ, Fin r → ℝ) e.symm (e x))
    (hφ : MDifferentiableAt (complexModel 1) (complexModel d) (inc ∘ e.symm) (e x))
    (hinj : Function.Injective
      (mfderiv (complexModel 1) (complexModel d) (inc ∘ e.symm) (e x))) :
    let ρ := Real.sqrt ((h (inc (e.symm (e x)))).inner
      (mfderiv (complexModel 1) (complexModel d) (inc ∘ e.symm) (e x)
        ((tangentSpaceCastModel (complexModel 1) (e x)).symm (1 : ComplexModel 1)))
      (mfderiv (complexModel 1) (complexModel d) (inc ∘ e.symm) (e x)
        ((tangentSpaceCastModel (complexModel 1) (e x)).symm (1 : ComplexModel 1)))).re
    0 < ρ ∧ ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) x,
      leafPullbackHermitianNorm inc h x v =
        ρ * ‖(tangentSpaceCastModel (realModel 1) (e x))
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x v)‖ := by
  obtain ⟨hρ, hs⟩ := hermitian_native_coordinate_density_formula inc h e.symm (e x)
    (by simpa only [e.left_inv hx] using hinc) hc hφ hinj
  have hid : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    exact e.left_inv hz
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, Fin r → ℝ)) (I' := realModel 1)
    (I'' := 𝓘(ℝ, Fin r → ℝ)) x hc he
  rw [hid.mfderiv_eq, mfderiv_id] at hcomp
  refine ⟨hρ, ?_⟩
  intro v
  have hs' := hs ((tangentSpaceCastModel (realModel 1) (e x))
    (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x v))
  have hvec : complexTangentToReal 1 (e x)
      ((tangentSpaceCastModel (complexModel 1) (e x)).symm
        ((tangentSpaceCastModel (realModel 1) (e x))
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x v))) =
      mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e x v := by
    rfl
  rw [hvec] at hs'
  have hv := congrArg (fun D ↦ D v) hcomp
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at hv
  rw [← hv] at hs'
  change leafPullbackHermitianNorm inc h (e.symm (e x)) v = _ at hs'
  exact (congrArg (fun z : X ↦ leafPullbackHermitianNorm inc h z v)
    (e.left_inv hx)).symm.trans hs'

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Bundle
open scoped ContDiff Manifold
universe u

/-- The Hermitian length of the differential of a fixed coordinate vector is continuous along a
holomorphic parameter disk. (Demailly, I §3.C, p. 23, VI §4, pp. 296–297) -/
theorem continuousOn_hermitian_parameter_density
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    {V : Set (ComplexModel 1)} (hV : IsOpen V) (φ : ComplexModel 1 → M)
    (hφ : ContMDiffOn (complexModel 1) (complexModel d) ∞ φ V)
    (v : ComplexModel 1) :
    ContinuousOn (fun a ↦ Real.sqrt
      (((h (φ a)).inner
        (mfderiv (complexModel 1) (complexModel d) φ a
          ((tangentSpaceCastModel (complexModel 1) a).symm v))
        (mfderiv (complexModel 1) (complexModel d) φ a
          ((tangentSpaceCastModel (complexModel 1) a).symm v))).re)) V := by
  let frame (a : ComplexModel 1) : TangentBundle (complexModel 1) (ComplexModel 1) :=
    ⟨a, (tangentSpaceCastModel (complexModel 1) a).symm v⟩
  have hframe : Continuous frame := by
    exact (tangentBundleModelSpaceHomeomorph (complexModel 1)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hder := (hφ.continuousOn_tangentMapWithin (by simp) hV.uniqueMDiffOn).comp
    hframe.continuousOn (fun a ha ↦ ha)
  have hn := (Preparation.continuous_hermitian_tangent_norm h hh).comp_continuousOn hder
  apply hn.congr
  intro a ha
  simp only [Function.comp_apply, tangentMapWithin, frame]
  rw [mfderivWithin_of_mem_nhds (hV.mem_nhds ha)]
  rfl

end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- A native complex leaf chart and its inverse are smooth in the real atlas, and its ambient
parametrization is a holomorphic immersion. (Demailly, I §3.C, p. 23; Ghys, p. 589) -/
theorem native_complex_chart_properties
    {r d : ℕ} {X M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {inc : X → M} (U : NativeLeafComplexUpgrade (d := d) (r := r) 1 inc) :
    letI := U.charts
    ∀ e : OpenPartialHomeomorph X (ComplexModel 1), e ∈ atlas (ComplexModel 1) X →
      ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel 1) ∞ e e.source ∧
      ContMDiffOn (realModel 1) 𝓘(ℝ, Fin r → ℝ) ∞ e.symm e.target ∧
      ContMDiffOn (complexModel 1) (complexModel d) ∞ (inc ∘ e.symm) e.target ∧
      ∀ a ∈ e.target, Function.Injective
        (mfderiv (complexModel 1) (complexModel d) (inc ∘ e.symm) a) := by
  let := U.charts
  let := U.complex_manifold
  intro e he
  obtain ⟨hforward, hback⟩ := native_complex_upgrade_identity_mdifferentiable U
  have hr := contMDiffOn_of_mem_maximalAtlas
    (I := realModel 1) (n := ∞) (IsManifold.subset_maximalAtlas he)
  have hri := contMDiffOn_symm_of_mem_maximalAtlas
    (I := realModel 1) (n := ∞) (IsManifold.subset_maximalAtlas he)
  have hc := contMDiffOn_symm_of_mem_maximalAtlas
    (I := complexModel 1) (n := ∞) (IsManifold.subset_maximalAtlas he)
  refine ⟨?_, ?_, U.inclusion_holomorphic.comp_contMDiffOn hc, ?_⟩
  · simpa only [Function.comp_id, Set.preimage_id] using
      hr.comp hforward.contMDiffOn (fun _ h ↦ h)
  · simpa only [Function.id_comp] using hback.comp_contMDiffOn hri
  · intro a ha
    have hinc := U.inclusion_holomorphic.mdifferentiable (by simp) (e.symm a)
    have hi := (mdifferentiable_of_mem_atlas (I := complexModel 1) he).symm
    rw [mfderiv_comp a hinc (hi.mdifferentiableAt ha)]
    exact ((U.inclusion_immersion (e.symm a)).mfderiv_injective (by simp)).comp
      (hi.mfderiv_injective ha)

end HolomorphicAnosov.Ghys
namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped _root_.Topology
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- Near every point of a native complex curve chart, the Hermitian speed has a uniform positive
lower bound in terms of coordinate speed. (Ghys, p. 590; Demailly, VI §4) -/
theorem native_chart_hermitian_lower_bound
    {r d : ℕ} {X M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {inc : X → M} (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) 1 inc)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    letI := U.charts
    ∀ e : OpenPartialHomeomorph X (ComplexModel 1), e ∈ atlas (ComplexModel 1) X →
    ∀ x ∈ e.source, ∃ m : ℝ, 0 < m ∧ ∃ V : Set (ComplexModel 1),
      IsOpen V ∧ e x ∈ V ∧ V ⊆ e.target ∧
      ∀ z ∈ e.source, e z ∈ V → ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
        m * ‖(tangentSpaceCastModel (realModel 1) (e z))
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e z v)‖ ≤
          leafPullbackHermitianNorm inc h z v := by
  let := U.charts
  let := U.complex_manifold
  intro e he x hx
  obtain ⟨heR, hcR, hφ, hinj⟩ := native_complex_chart_properties U e he
  let ρ (a : ComplexModel 1) := Real.sqrt ((h (inc (e.symm a))).inner
    (mfderiv (complexModel 1) (complexModel d) (inc ∘ e.symm) a
      ((tangentSpaceCastModel (complexModel 1) a).symm (1 : ComplexModel 1)))
    (mfderiv (complexModel 1) (complexModel d) (inc ∘ e.symm) a
      ((tangentSpaceCastModel (complexModel 1) a).symm (1 : ComplexModel 1)))).re
  have hcont : ContinuousOn ρ e.target :=
    continuousOn_hermitian_parameter_density h hh e.open_target (inc ∘ e.symm) hφ 1
  have hformula (z : X) (hz : z ∈ e.source) : 0 < ρ (e z) ∧
      ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
        leafPullbackHermitianNorm inc h z v = ρ (e z) *
          ‖(tangentSpaceCastModel (realModel 1) (e z))
            (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e z v)‖ := by
    exact hermitian_coordinate_density_formula inc h e hz
      (hinc.mdifferentiable (by simp) z)
      ((heR.contMDiffAt (e.open_source.mem_nhds hz)).mdifferentiableAt (by simp))
      ((hcR.contMDiffAt (e.open_target.mem_nhds (e.map_source hz))).mdifferentiableAt (by simp))
      ((hφ.contMDiffAt (e.open_target.mem_nhds (e.map_source hz))).mdifferentiableAt (by simp))
      (hinj _ (e.map_source hz))
  let m := ρ (e x) / 2
  have hm : 0 < m := half_pos (hformula x hx).1
  let V := e.target ∩ ρ ⁻¹' Ioi m
  have hV : IsOpen V := hcont.isOpen_inter_preimage e.open_target isOpen_Ioi
  refine ⟨m, hm, V, hV, ⟨e.map_source hx, ?_⟩, inter_subset_left, ?_⟩
  · exact half_lt_self (hformula x hx).1
  · intro z hz hzV v
    rw [(hformula z hz).2 v]
    exact mul_le_mul_of_nonneg_right (le_of_lt hzV.2) (norm_nonneg _)

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter
open _root_.Metric
open scoped _root_.Topology
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- Each point admits a buffered holomorphic native chart with a uniform positive Hermitian speed
lower bound on its source. (Ghys, p. 590; HPS, (6.7), p. 86) -/
theorem native_hermitian_buffered_chart
    {r d : ℕ} {X M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {inc : X → M} (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) 1 inc)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (x : X) :
    letI := U.charts
    ∃ e : OpenPartialHomeomorph X (ComplexModel 1), x ∈ e.source ∧
      ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel 1) ∞ e e.source ∧
      ContMDiffOn (realModel 1) 𝓘(ℝ, Fin r → ℝ) ∞ e.symm e.target ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target ∧
      ∃ R m : ℝ, 0 < R ∧ 0 < m ∧ closedBall (e x) (2 * R) ⊆ e.target ∧
      ∀ z ∈ e.source, ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
        m * ‖(tangentSpaceCastModel (realModel 1) (e z))
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e z v)‖ ≤
          leafPullbackHermitianNorm inc h z v := by
  let := U.charts
  let := U.complex_manifold
  let c := chartAt (ComplexModel 1) x
  have hcx : x ∈ c.source := ChartedSpace.mem_chart_source x
  have hc : c ∈ atlas (ComplexModel 1) X := ChartedSpace.chart_mem_atlas x
  obtain ⟨m, hm, V, hV, hxV, hVsub, hbound⟩ :=
    native_chart_hermitian_lower_bound hinc U h hh c hc x hcx
  let e := (c.symm.restrOpen V hV).symm
  have hsource : e.source = c.source ∩ c ⁻¹' V := rfl
  have htarget : e.target = c.target ∩ V := rfl
  have hex : x ∈ e.source := ⟨hcx, hxV⟩
  obtain ⟨hcR, hciR, _, _⟩ := native_complex_chart_properties U c hc
  have hcC : ContMDiffOn (complexModel 1) (complexModel 1) ∞ c c.source :=
    contMDiffOn_chart
  have hciC : ContMDiffOn (complexModel 1) (complexModel 1) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  have hs : e.source ⊆ c.source := inter_subset_left
  have ht : e.target ⊆ c.target := inter_subset_left
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hex)
  refine ⟨e, hex, hcR.mono hs, hciR.mono ht, hcC.mono hs, hciC.mono ht,
    ε/4, m, by positivity, hm, ?_, ?_⟩
  · intro a ha
    apply hεsub
    have ha' := mem_closedBall.mp ha
    apply mem_ball.mpr
    linarith
  · intro z hz v
    exact hbound z hz.1 hz.2 v

end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
open Set Filter
open _root_.Metric
open scoped _root_.Topology
open scoped ContDiff Manifold ENNReal
universe u v

/-- Sufficiently small intrinsic Hermitian distance bounds coordinate displacement in a chart with a
positive speed lower bound. (Lee, §11; HPS, (6.7), p. 86) -/
theorem hermitian_chart_displacement
    {r d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [T2Space L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M) (h : HermitianTangentMetricCore d M)
    (e : OpenPartialHomeomorph L (ComplexModel 1))
    (he : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel 1) 1 e e.source)
    (m : ℝ) (hm : 0 < m)
    (hbound : ∀ z ∈ e.source, ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
      m * ‖(tangentSpaceCastModel (realModel 1) (e z))
        (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e z v)‖ ≤
        leafPullbackHermitianNorm inc h z v)
    {x y : L} (hx : x ∈ e.source) (R : ℝ) (hR : 0 < R)
    (hbuffer : closedBall (e x) R ⊆ e.target)
    (hd : intrinsicHermitianLeafEDist (r := r) inc h y x < ENNReal.ofReal (m * R)) :
    y ∈ e.source ∧ dist (e y) (e x) < R := by
  rw [IntrinsicPiecewiseC1Path.intrinsicHermitianLeafEDist_comm h inc y x] at hd
  exact intrinsic_chart_ball_of_length_inf_lt e he (e x) R hR hbuffer
    (leafPullbackHermitianNorm inc h) m hm hbound hx rfl hd

/-- Uniformly small intrinsic Hermitian errors yield uniform coordinate errors in a common buffered
receiving chart. (Ghys, p. 590; HPS, (6.7), p. 86) -/
theorem hermitian_uniform_coordinate_error
    {r d : ℕ} {L : Type u} {M : Type v} {Z : Type*}
    [TopologicalSpace L] [T2Space L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M) (h : HermitianTangentMetricCore d M)
    (e : OpenPartialHomeomorph L (ComplexModel 1))
    (he : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel 1) 1 e e.source)
    (m : ℝ) (hm : 0 < m)
    (hbound : ∀ z ∈ e.source, ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
      m * ‖(tangentSpaceCastModel (realModel 1) (e z))
        (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e z v)‖ ≤
        leafPullbackHermitianNorm inc h z v)
    (a : ComplexModel 1) (R : ℝ) (hR : 0 < R)
    (hbuffer : closedBall a (2 * R) ⊆ e.target)
    (g : ℕ → Z → L) (f : Z → L) (W : Set Z)
    (hf : ∀ z ∈ W, f z ∈ e.source ∧ dist (e (f z)) a ≤ R)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (herr : ∀ᶠ k in atTop, ∀ z ∈ W,
      intrinsicHermitianLeafEDist (r := r) inc h (g k z) (f z) ≤ ENNReal.ofReal (δ k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ z ∈ W,
      g k z ∈ e.source ∧ dist (e (g k z)) (e (f z)) < ε := by
  intro ε hε
  have hmin : 0 < min ε R := lt_min hε hR
  have hsmall : ∀ᶠ k in atTop, δ k < m * min ε R :=
    hδ.eventually (gt_mem_nhds (mul_pos hm hmin))
  filter_upwards [hsmall, herr] with k hk hkerr
  intro z hz
  have hball : closedBall (e (f z)) (min ε R) ⊆ e.target := by
    intro w hw
    apply hbuffer
    have hw' := mem_closedBall.mp hw
    apply mem_closedBall.mpr
    calc
      dist w a ≤ dist w (e (f z)) + dist (e (f z)) a := dist_triangle _ _ _
      _ ≤ min ε R + R := add_le_add hw' (hf z hz).2
      _ ≤ 2 * R := by linarith [min_le_right ε R]
  have hd : intrinsicHermitianLeafEDist (r := r) inc h (g k z) (f z) <
      ENNReal.ofReal (m * min ε R) :=
    (hkerr z hz).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hm hmin)).mpr hk)
  obtain ⟨hmem, hdist⟩ := hermitian_chart_displacement inc h e he m hm hbound
    (hf z hz).1 (min ε R) hmin hball hd
  exact ⟨hmem, hdist.trans_le (min_le_left ε R)⟩

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold


end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold

/-- A real `C¹` coordinate homeomorphism with a `C¹` inverse has an invertible derivative. -/
theorem c1_positive_derivative_equivalence
    {n : ℕ} (e : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n))
    (he : ContDiffOn ℝ 1 e e.source) (hi : ContDiffOn ℝ 1 e.symm e.target)
    {z : ComplexModel n} (hz : z ∈ e.source) (hdet : 0 < (fderiv ℝ e z).det) :
    ∃ A : ComplexModel n ≃L[ℝ] ComplexModel n,
      HasFDerivAt e A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det := by
  have hm : e.MDifferentiable (realModel n) (realModel n) :=
    ⟨(contMDiffOn_iff_contDiffOn.mpr he).mdifferentiableOn (by simp),
      (contMDiffOn_iff_contDiffOn.mpr hi).mdifferentiableOn (by simp)⟩
  let A : ComplexModel n ≃L[ℝ] ComplexModel n := hm.mfderiv hz
  have hA : A.toContinuousLinearMap = fderiv ℝ e z := mfderiv_eq_fderiv
  refine ⟨A, ?_, ?_⟩
  · rw [hA]
    exact (he.differentiableOn (by simp) z hz).differentiableAt (e.open_source.mem_nhds hz) |>.hasFDerivAt
  · rwa [hA]

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys

/-- A complex-linear endomorphism of `ComplexModel 1` scales every vector norm by `‖A 1‖`. (Ghys, p.
590) -/
theorem complex_model_one_linear_norm (A : ComplexModel 1 →L[ℂ] ComplexModel 1)
    (v : ComplexModel 1) : ‖A v‖ = ‖A 1‖ * ‖v‖ := by
  have hv : v = (v 0) • (1 : ComplexModel 1) := by
    funext i
    simpa using congrArg v (Subsingleton.elim i 0)
  rw [hv, map_smul, norm_smul, norm_smul]
  have hone : ‖(1 : ComplexModel 1)‖ = 1 := by
    change ‖fun _ : Fin 1 ↦ (1 : ℂ)‖ = 1
    simp only [pi_norm_const, norm_one]
  rw [hone, mul_one, mul_comm]

/-- Complex-linear pre- and postcomposition preserve a real map's directional distortion bound on
`ComplexModel 1`. (Ghys, p. 590; Lehto–Virtanen, I §3.3, p. 17) -/
theorem complex_model_one_similarity_distortion
    (A : ComplexModel 1 →L[ℝ] ComplexModel 1) {K : ℝ}
    (hK : ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 → ‖A v‖ ≤ K * ‖A w‖)
    (P Q : ComplexModel 1 →L[ℂ] ComplexModel 1)
    {v w : ComplexModel 1} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖Q (A (P v))‖ ≤ K * ‖Q (A (P w))‖ := by
  by_cases hp : ‖P 1‖ = 0
  · have hpv : P v = 0 := norm_eq_zero.mp (by rw [complex_model_one_linear_norm, hp, zero_mul])
    have hpw : P w = 0 := norm_eq_zero.mp (by rw [complex_model_one_linear_norm, hp, zero_mul])
    simp only [hpv, hpw, map_zero, norm_zero, mul_zero, le_refl]
  have hp' : 0 < ‖P 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)
  have hunit (z : ComplexModel 1) (hz : ‖z‖ = 1) :
      ‖(‖P 1‖⁻¹ : ℝ) • P z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      complex_model_one_linear_norm P z, hz, mul_one, inv_mul_cancel₀ hp]
  have h := hK ((‖P 1‖⁻¹ : ℝ) • P v) ((‖P 1‖⁻¹ : ℝ) • P w)
    (hunit v hv) (hunit w hw)
  simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm] at h
  have h' : ‖A (P v)‖ ≤ K * ‖A (P w)‖ := by
    apply le_of_mul_le_mul_left _ (inv_pos.mpr hp')
    simpa only [mul_left_comm K] using h
  rw [complex_model_one_linear_norm Q (A (P v)), complex_model_one_linear_norm Q (A (P w))]
  simpa only [mul_left_comm K] using mul_le_mul_of_nonneg_left h' (norm_nonneg (Q 1))

/-- Holomorphic pre- and postcomposition with injective derivatives preserve positive orientation
and directional distortion bounds for a real coordinate map. (Ghys, p. 590) -/
theorem complex_model_one_composition_bounds
    {pre mid post : ComplexModel 1 → ComplexModel 1} {z : ComplexModel 1}
    (hp : DifferentiableAt ℂ pre z) (hq : DifferentiableAt ℂ post (mid (pre z)))
    (hm : DifferentiableAt ℝ mid (pre z))
    (hip : Function.Injective (fderiv ℂ pre z))
    (hiq : Function.Injective (fderiv ℂ post (mid (pre z))))
    (hd : 0 < (fderiv ℝ mid (pre z)).det) {K : ℝ}
    (hK : ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ mid (pre z) v‖ ≤ K * ‖fderiv ℝ mid (pre z) w‖) :
    0 < (fderiv ℝ (post ∘ mid ∘ pre) z).det ∧
      ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
        ‖fderiv ℝ (post ∘ mid ∘ pre) z v‖ ≤
          K * ‖fderiv ℝ (post ∘ mid ∘ pre) z w‖ := by
  have hchain := (hq.hasFDerivAt.restrictScalars ℝ).comp z
    (hm.hasFDerivAt.comp z (hp.hasFDerivAt.restrictScalars ℝ))
  constructor
  · rw [hchain.fderiv]
    change 0 < LinearMap.det
      (((fderiv ℂ post (mid (pre z))).toLinearMap.restrictScalars ℝ).comp
        ((fderiv ℝ mid (pre z)).toLinearMap.comp
          ((fderiv ℂ pre z).toLinearMap.restrictScalars ℝ)))
    rw [LinearMap.det_comp, LinearMap.det_comp]
    have hp' := complex_model_derivative_det_pos hp hip
    have hq' := complex_model_derivative_det_pos hq hiq
    rw [(hp.hasFDerivAt.restrictScalars ℝ).fderiv] at hp'
    rw [(hq.hasFDerivAt.restrictScalars ℝ).fderiv] at hq'
    exact mul_pos hq' (mul_pos hd hp')
  · intro v w hv hw
    rw [hchain.fderiv]
    exact complex_model_one_similarity_distortion _ hK _ _ hv hw

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v

/-- The real manifold derivative in the complex coordinate model equals the derivative of the
preferred-chart expression. (Demailly, I §3.C, p. 23) -/
theorem preferred_coordinate_real_derivative
    {m n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel m) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    {f : X → Y} {x : X} (hf : MDifferentiableAt (realModel m) (realModel n) f x) :
    (tangentSpaceCastModel (realModel n) (f x)).toContinuousLinearMap ∘L
      mfderiv (realModel m) (realModel n) f x ∘L
        (tangentSpaceCastModel (realModel m) x).symm.toContinuousLinearMap =
      fderiv ℝ ((chartAt (ComplexModel n) (f x)) ∘ f ∘
        (chartAt (ComplexModel m) x).symm) (chartAt (ComplexModel m) x x) := by
  rw [hf.mfderiv]
  simp only [realModel, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ,
    writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp]
  rfl

/-- The real derivative in preferred coordinates is the scalar restriction of the complex
derivative. (Demailly, I §3.C) -/
theorem complex_model_mfderiv_restrictScalars
    {m n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel m) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    {f : X → Y} {x : X} (hf : MDifferentiableAt (complexModel m) (complexModel n) f x) :
    (tangentSpaceCastModel (realModel n) (f x)).toContinuousLinearMap ∘L
      mfderiv (realModel m) (realModel n) f x ∘L
        (tangentSpaceCastModel (realModel m) x).symm.toContinuousLinearMap =
    ((tangentSpaceCastModel (complexModel n) (f x)).toContinuousLinearMap ∘L
      mfderiv (complexModel m) (complexModel n) f x ∘L
        (tangentSpaceCastModel (complexModel m) x).symm.toContinuousLinearMap).restrictScalars ℝ := by
  apply ContinuousLinearMap.ext
  intro v
  exact mfderiv_complex_to_real hf ((tangentSpaceCastModel (complexModel m) x).symm v)

end HolomorphicAnosov.Ghys
namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v

/-- Holomorphic parametrizations and receiving coordinates preserve preferred-coordinate orientation
and distortion bounds on complex curves. (Ghys, p. 590) -/
theorem native_holomorphic_composition_bounds
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel 1) Y]
    {pre : ComplexModel 1 → X} {mid : X → Y} {post : Y → ComplexModel 1}
    {z : ComplexModel 1}
    (hp : MDifferentiableAt (complexModel 1) (complexModel 1) pre z)
    (hq : MDifferentiableAt (complexModel 1) (complexModel 1) post (mid (pre z)))
    (hpr : MDifferentiableAt (realModel 1) (realModel 1) pre z)
    (hqr : MDifferentiableAt (realModel 1) (realModel 1) post (mid (pre z)))
    (hm : MDifferentiableAt (realModel 1) (realModel 1) mid (pre z))
    (hip : Function.Injective (mfderiv (complexModel 1) (complexModel 1) pre z))
    (hiq : Function.Injective (mfderiv (complexModel 1) (complexModel 1) post (mid (pre z))))
    (hd : 0 < (fderiv ℝ ((chartAt (ComplexModel 1) (mid (pre z))) ∘ mid ∘
      (chartAt (ComplexModel 1) (pre z)).symm)
      (chartAt (ComplexModel 1) (pre z) (pre z))).det) {K : ℝ}
    (hK : ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ ((chartAt (ComplexModel 1) (mid (pre z))) ∘ mid ∘
        (chartAt (ComplexModel 1) (pre z)).symm)
        (chartAt (ComplexModel 1) (pre z) (pre z)) v‖ ≤
      K * ‖fderiv ℝ ((chartAt (ComplexModel 1) (mid (pre z))) ∘ mid ∘
        (chartAt (ComplexModel 1) (pre z)).symm)
        (chartAt (ComplexModel 1) (pre z) (pre z)) w‖) :
    0 < (fderiv ℝ (post ∘ mid ∘ pre) z).det ∧
      ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
        ‖fderiv ℝ (post ∘ mid ∘ pre) z v‖ ≤
          K * ‖fderiv ℝ (post ∘ mid ∘ pre) z w‖ := by
  let P : ComplexModel 1 →L[ℂ] ComplexModel 1 :=
    (tangentSpaceCastModel (complexModel 1) (pre z)).toContinuousLinearMap ∘L
      mfderiv (complexModel 1) (complexModel 1) pre z ∘L
        (tangentSpaceCastModel (complexModel 1) z).symm.toContinuousLinearMap
  let Q : ComplexModel 1 →L[ℂ] ComplexModel 1 :=
    (tangentSpaceCastModel (complexModel 1) (post (mid (pre z)))).toContinuousLinearMap ∘L
      mfderiv (complexModel 1) (complexModel 1) post (mid (pre z)) ∘L
        (tangentSpaceCastModel (complexModel 1) (mid (pre z))).symm.toContinuousLinearMap
  let A : ComplexModel 1 →L[ℝ] ComplexModel 1 :=
    (tangentSpaceCastModel (realModel 1) (mid (pre z))).toContinuousLinearMap ∘L
      mfderiv (realModel 1) (realModel 1) mid (pre z) ∘L
        (tangentSpaceCastModel (realModel 1) (pre z)).symm.toContinuousLinearMap
  have hA := preferred_coordinate_real_derivative hm
  change A = _ at hA
  rw [← hA] at hd hK
  have hchain : fderiv ℝ (post ∘ mid ∘ pre) z =
      (Q.restrictScalars ℝ).comp (A.comp (P.restrictScalars ℝ)) := by
    rw [← mfderiv_eq_fderiv (𝕜 := ℝ)]
    rw [mfderiv_comp z hqr (hm.comp z hpr), mfderiv_comp z hm hpr]
    have hP := complex_model_mfderiv_restrictScalars hp
    have hQ := complex_model_mfderiv_restrictScalars hq
    change _ = P.restrictScalars ℝ at hP
    change _ = Q.restrictScalars ℝ at hQ
    rw [← hP, ← hQ]
    rfl
  have hpos (B : ComplexModel 1 →L[ℂ] ComplexModel 1) (hB : Function.Injective B) :
      0 < (B.restrictScalars ℝ).det := by
    change 0 < LinearMap.det (B.toLinearMap.restrictScalars ℝ)
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
    apply Complex.normSq_pos.mpr
    intro hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hB)
  constructor
  · rw [hchain]
    change 0 < LinearMap.det ((Q.toLinearMap.restrictScalars ℝ).comp
      (A.toLinearMap.comp (P.toLinearMap.restrictScalars ℝ)))
    rw [LinearMap.det_comp, LinearMap.det_comp]
    exact mul_pos (hpos Q ((tangentSpaceCastModel (complexModel 1) _).injective.comp
      (hiq.comp (tangentSpaceCastModel (complexModel 1) _).symm.injective)))
      (mul_pos hd (hpos P ((tangentSpaceCastModel (complexModel 1) _).injective.comp
        (hip.comp (tangentSpaceCastModel (complexModel 1) _).symm.injective))))
  · intro v w hv hw
    rw [hchain]
    exact complex_model_one_similarity_distortion A hK P Q hv hw

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v

/-- Complex `Cᵏ` regularity on an open domain implies real `Cᵏ` regularity in the same charts.
(Demailly, I §3.C, p. 23) -/
theorem contMDiffOn_complex_to_real_local
    {m n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel m) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    {f : X → Y} {W : Set X} {k : ℕ∞ω}
    (hf : ContMDiffOn (complexModel m) (complexModel n) k f W) :
    ContMDiffOn (realModel m) (realModel n) k f W := by
  intro x hx
  obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (hf x hx)
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

/-- Biholomorphic coordinate partial homeomorphisms preserve a native curve map's
preferred-coordinate orientation and distortion bounds. (Ghys, p. 590) -/
theorem native_holomorphic_partial_composition_bounds
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel 1) Y]
    (P : OpenPartialHomeomorph (ComplexModel 1) X)
    (G : OpenPartialHomeomorph X Y)
    (Q : OpenPartialHomeomorph Y (ComplexModel 1))
    (hP : ContMDiffOn (complexModel 1) (complexModel 1) ∞ P P.source)
    (hPi : ContMDiffOn (complexModel 1) (complexModel 1) ∞ P.symm P.target)
    (hQ : ContMDiffOn (complexModel 1) (complexModel 1) ∞ Q Q.source)
    (hQi : ContMDiffOn (complexModel 1) (complexModel 1) ∞ Q.symm Q.target)
    (hG : ContMDiffOn (realModel 1) (realModel 1) 1 G G.source)
    {z : ComplexModel 1} (hz : z ∈ (P.trans (G.trans Q)).source)
    (hd : 0 < (fderiv ℝ ((chartAt (ComplexModel 1) (G (P z))) ∘ G ∘
      (chartAt (ComplexModel 1) (P z)).symm)
      (chartAt (ComplexModel 1) (P z) (P z))).det) {K : ℝ}
    (hK : ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ ((chartAt (ComplexModel 1) (G (P z))) ∘ G ∘
        (chartAt (ComplexModel 1) (P z)).symm)
        (chartAt (ComplexModel 1) (P z) (P z)) v‖ ≤
      K * ‖fderiv ℝ ((chartAt (ComplexModel 1) (G (P z))) ∘ G ∘
        (chartAt (ComplexModel 1) (P z)).symm)
        (chartAt (ComplexModel 1) (P z) (P z)) w‖) :
    0 < (fderiv ℝ (P.trans (G.trans Q)) z).det ∧
      ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
        ‖fderiv ℝ (P.trans (G.trans Q)) z v‖ ≤
          K * ‖fderiv ℝ (P.trans (G.trans Q)) z w‖ := by
  have hpM : P.MDifferentiable (complexModel 1) (complexModel 1) :=
    ⟨hP.mdifferentiableOn (by simp), hPi.mdifferentiableOn (by simp)⟩
  have hqM : Q.MDifferentiable (complexModel 1) (complexModel 1) :=
    ⟨hQ.mdifferentiableOn (by simp), hQi.mdifferentiableOn (by simp)⟩
  exact native_holomorphic_composition_bounds (hpM.mdifferentiableAt hz.1)
    (hqM.mdifferentiableAt hz.2.2)
    (((contMDiffOn_complex_to_real_local hP).contMDiffAt (P.open_source.mem_nhds hz.1)).mdifferentiableAt (by simp))
    (((contMDiffOn_complex_to_real_local hQ).contMDiffAt (Q.open_source.mem_nhds hz.2.2)).mdifferentiableAt (by simp))
    ((hG.contMDiffAt (G.open_source.mem_nhds hz.2.1)).mdifferentiableAt one_ne_zero)
    (hpM.mfderiv_injective hz.1) (hqM.mfderiv_injective hz.2.2) hd hK

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped _root_.Topology
/-- The planar conformal-limit criterion transports from `ℂ` to `ComplexModel 1`. (Ghys, p. 590) -/
theorem asymptotically_conformal_limit_model_transport
    (planarCriterion :
    ∀ (U : Set ℂ) (_hU : IsOpen U) (_hne : U.Nonempty) (_hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (_hFs : ∀ n, (F n).source = U) (_hgs : g.source = U)
    (_hF : ∀ n, ContDiffOn ℝ 1 (F n) U)
    (_hFi : ∀ n, ContDiffOn ℝ 1 (F n).symm (F n).target)
    (_hd : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (F n) A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det)
    (K : ℕ → ℝ) (_hK : ∀ n, 1 ≤ K n) (_hKt : Tendsto K atTop (𝓝 1))
    (_hDist : ∀ n z, z ∈ U → ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖)
    (_hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U),
    DifferentiableOn ℂ g U)
    (U : Set (ComplexModel 1)) (hU : IsOpen U) (hne : U.Nonempty) (hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph (ComplexModel 1) (ComplexModel 1))
    (g : OpenPartialHomeomorph (ComplexModel 1) (ComplexModel 1))
    (hFs : ∀ n, (F n).source = U) (hgs : g.source = U)
    (hF : ∀ n, ContDiffOn ℝ 1 (F n) U)
    (hFi : ∀ n, ContDiffOn ℝ 1 (F n).symm (F n).target)
    (hd : ∀ n z, z ∈ U → ∃ A : (ComplexModel 1) ≃L[ℝ] (ComplexModel 1),
      HasFDerivAt (F n) A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det)
    (K : ℕ → ℝ) (hK : ∀ n, 1 ≤ K n) (hKt : Tendsto K atTop (𝓝 1))
    (hDist : ∀ n z, z ∈ U → ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖)
    (hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U) :
    DifferentiableOn ℂ g U := by
  let D : ComplexModel 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  let DR : ComplexModel 1 ≃L[ℝ] ℂ := ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℂ)
  have hnorm (v : ComplexModel 1) : ‖D v‖ = ‖v‖ := by
    have hv : v = fun _ ↦ v 0 := by
      funext i
      exact congrArg v (Subsingleton.elim i 0)
    rw [hv]
    exact (pi_norm_const _).symm
  let C (e : OpenPartialHomeomorph (ComplexModel 1) (ComplexModel 1)) :=
    D.symm.toHomeomorph.toOpenPartialHomeomorph.trans
      (e.trans D.toHomeomorph.toOpenPartialHomeomorph)
  have hCs (e : OpenPartialHomeomorph (ComplexModel 1) (ComplexModel 1)) :
      (C e).source = D.symm ⁻¹' e.source := by
    ext z
    simp [C]
  have hCt (e : OpenPartialHomeomorph (ComplexModel 1) (ComplexModel 1)) :
      (C e).target = D.symm ⁻¹' e.target := by
    ext z
    simp [C]
  let V := D.symm ⁻¹' U
  have hDV : V = D '' U := by
    ext z
    simp only [V, mem_preimage, mem_image]
    exact ⟨fun hz ↦ ⟨D.symm z, hz, D.apply_symm_apply z⟩,
      by rintro ⟨w, hw, rfl⟩; simpa using hw⟩
  have hFs' (n : ℕ) : (C (F n)).source = V := by rw [hCs, hFs n]
  have hgs' : (C g).source = V := by rw [hCs, hgs]
  have hF' (n : ℕ) : ContDiffOn ℝ 1 (C (F n)) V := by
    exact DR.contDiff.comp_contDiffOn
      ((hF n).comp DR.symm.contDiff.contDiffOn (fun _ hz ↦ hz))
  have hFi' (n : ℕ) : ContDiffOn ℝ 1 (C (F n)).symm (C (F n)).target := by
    rw [hCt]
    exact DR.contDiff.comp_contDiffOn
      ((hFi n).comp DR.symm.contDiff.contDiffOn (fun _ hz ↦ hz))
  have hder (n : ℕ) (z : ℂ) (hz : z ∈ V) :
      ∃ A : ℂ ≃L[ℝ] ℂ, HasFDerivAt (C (F n)) A.toContinuousLinearMap z ∧
        0 < A.toContinuousLinearMap.det := by
    obtain ⟨A, hA, hpos⟩ := hd n (D.symm z) hz
    let B := DR.symm.trans (A.trans DR)
    refine ⟨B, ?_, ?_⟩
    · exact DR.hasFDerivAt.comp z (hA.comp z DR.symm.hasFDerivAt)
    · have heq : B.toContinuousLinearMap.det = A.toContinuousLinearMap.det := by
        exact LinearMap.det_conj A.toLinearEquiv.toLinearMap DR.toLinearEquiv
      rw [heq]
      exact hpos
  have hdist' (n : ℕ) (z : ℂ) (hz : z ∈ V) (v w : ℂ)
      (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖fderiv ℝ (C (F n)) z v‖ ≤ K n * ‖fderiv ℝ (C (F n)) z w‖ := by
    obtain ⟨A, hA, _⟩ := hd n (D.symm z) hz
    have hcder := DR.hasFDerivAt.comp z (hA.comp z DR.symm.hasFDerivAt)
    change HasFDerivAt (C (F n)) _ z at hcder
    rw [hcder.fderiv]
    change ‖D (A (D.symm v))‖ ≤ K n * ‖D (A (D.symm w))‖
    rw [hnorm, hnorm]
    change ‖A.toContinuousLinearMap (D.symm v)‖ ≤ K n * ‖A.toContinuousLinearMap (D.symm w)‖
    rw [← hA.fderiv]
    apply hDist n (D.symm z) hz
    · simpa only [D.apply_symm_apply, hv] using (hnorm (D.symm v)).symm
    · simpa only [D.apply_symm_apply, hw] using (hnorm (D.symm w)).symm
  have hcvg : TendstoLocallyUniformlyOn (fun n z ↦ C (F n) z) (C g) atTop V :=
    D.toContinuousLinearMap.uniformContinuous.comp_tendstoLocallyUniformlyOn
      (hconv.comp D.symm (fun _ hz ↦ hz) D.symm.continuous.continuousOn)
  have hg := planarCriterion V
    (hU.preimage D.symm.continuous) (hDV ▸ hne.image D)
    (hDV ▸ hc.image D D.continuous.continuousOn) (fun n ↦ C (F n)) (C g)
    hFs' hgs' hF' hFi' hder K hK hKt hdist' hcvg
  have hback := D.symm.differentiable.comp_differentiableOn
    (hg.comp D.differentiable.differentiableOn (by
      intro z hz
      change D.symm (D z) ∈ U
      simpa using hz))
  convert hback using 1
  funext z
  exact ((D.symm_apply_apply (g (D.symm (D z)))).trans (congrArg g (D.symm_apply_apply z))).symm

end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped _root_.Topology
open scoped ContDiff

/-- The conformal-limit criterion applies when common-source and distortion bounds hold eventually
for the coordinate approximants. (Ghys, p. 590) -/
theorem conformal_limit_of_eventual_coordinate_bounds
    (planarCriterion :
    ∀ (U : Set ℂ) (_hU : IsOpen U) (_hne : U.Nonempty) (_hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (_hFs : ∀ n, (F n).source = U) (_hgs : g.source = U)
    (_hF : ∀ n, ContDiffOn ℝ 1 (F n) U)
    (_hFi : ∀ n, ContDiffOn ℝ 1 (F n).symm (F n).target)
    (_hd : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (F n) A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det)
    (K : ℕ → ℝ) (_hK : ∀ n, 1 ≤ K n) (_hKt : Tendsto K atTop (𝓝 1))
    (_hDist : ∀ n z, z ∈ U → ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖)
    (_hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U),
    DifferentiableOn ℂ g U)
    (U : Set (ComplexModel 1)) (hU : IsOpen U) (hne : U.Nonempty) (hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph (ComplexModel 1) (ComplexModel 1))
    (g : OpenPartialHomeomorph (ComplexModel 1) (ComplexModel 1))
    (hgs : U ⊆ g.source) (K : ℕ → ℝ) (hKt : Tendsto K atTop (𝓝 1))
    (hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U)
    (hgood : ∀ᶠ n in atTop, U ⊆ (F n).source ∧
      ContDiffOn ℝ 1 (F n) (F n).source ∧
      ContDiffOn ℝ 1 (F n).symm (F n).target ∧ 1 ≤ K n ∧
      ∀ z ∈ U, 0 < (fderiv ℝ (F n) z).det ∧
        ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
          ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖) :
    DifferentiableOn ℂ g U := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  let F' (n : ℕ) := (F (n + N)).restrOpen U hU
  let g' := g.restrOpen U hU
  have hFs (n : ℕ) : (F' n).source = U := inter_eq_right.mpr (hN (n+N) (Nat.le_add_left _ _)).1
  have hgs' : g'.source = U := inter_eq_right.mpr hgs
  have hF' (n : ℕ) : ContDiffOn ℝ 1 (F' n) U :=
    (hN (n+N) (Nat.le_add_left _ _)).2.1.mono (hN (n+N) (Nat.le_add_left _ _)).1
  have hFi' (n : ℕ) : ContDiffOn ℝ 1 (F' n).symm (F' n).target :=
    (hN (n+N) (Nat.le_add_left _ _)).2.2.1.mono inter_subset_left
  have hconv' : TendstoLocallyUniformlyOn (fun n z ↦ F' n z) g' atTop U := by
    intro V hV x hx
    obtain ⟨W, hW, htail⟩ := hconv V hV x hx
    exact ⟨W, hW, (tendsto_add_atTop_nat N).eventually htail⟩
  apply asymptotically_conformal_limit_model_transport planarCriterion U hU hne hc
    F' g' hFs hgs' hF' hFi' ?_ (fun n ↦ K (n+N))
    (fun n ↦ (hN (n+N) (Nat.le_add_left _ _)).2.2.2.1)
    (hKt.comp (tendsto_add_atTop_nat N)) ?_ hconv'
  · intro n z hz
    have hn := hN (n+N) (Nat.le_add_left _ _)
    exact c1_positive_derivative_equivalence (F' n) (by simpa only [hFs n] using hF' n)
      (hFi' n) (by simpa only [hFs n] using hz) (hn.2.2.2.2 z hz).1
  · intro n z hz v w hv hw
    exact (hN (n+N) (Nat.le_add_left _ _)).2.2.2.2 z hz |>.2 v w hv hw

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped _root_.Topology ContDiff
universe u v

/-- Complex differentiability of a coordinate expression on an open neighborhood implies
holomorphicity of the leaf map at its center. (Ghys, p. 589) -/
theorem holomorphic_at_of_coordinate_differentiable
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 1) X] [ChartedSpace (ComplexModel 1) Y]
    (c : OpenPartialHomeomorph X (ComplexModel 1))
    (e : OpenPartialHomeomorph Y (ComplexModel 1))
    (g : OpenPartialHomeomorph X Y)
    (hc : ContMDiffOn (complexModel 1) (complexModel 1) ∞ c c.source)
    (hei : ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target)
    (V : Set (ComplexModel 1)) (hV : IsOpen V)
    (hVs : V ⊆ (c.symm.trans (g.trans e)).source)
    (hD : DifferentiableOn ℂ (c.symm.trans (g.trans e)) V)
    {x : X} (hx : x ∈ c.source) (hxV : c x ∈ V) :
    ContMDiffAt (complexModel 1) (complexModel 1) ∞ g x := by
  let G := c.symm.trans (g.trans e)
  have hG : ContMDiffAt (complexModel 1) (complexModel 1) ∞ G (c x) :=
    ((complex_contDiffOn_iff_differentiableOn hV).mpr hD).contMDiffOn.contMDiffAt
      (hV.mem_nhds hxV)
  have hsource := hVs hxV
  change c x ∈ c.target ∧ c.symm (c x) ∈ g.source ∧ g (c.symm (c x)) ∈ e.source at hsource
  rw [c.left_inv hx] at hsource
  have hgs : x ∈ g.source := by
    exact hsource.2.1
  have hes : g x ∈ e.source := by
    exact hsource.2.2
  have htarget : G (c x) ∈ e.target := by
    change e (g (c.symm (c x))) ∈ e.target
    rw [c.left_inv hx]
    exact e.map_source hes
  have H := (hei.contMDiffAt (e.open_target.mem_nhds htarget)).comp x
    (hG.comp x (hc.contMDiffAt (c.open_source.mem_nhds hx)))
  apply H.congr_of_eventuallyEq
  have hne : ∀ᶠ z in 𝓝 x, g z ∈ e.source :=
    (g.continuousAt hgs).preimage_mem_nhds (e.open_source.mem_nhds hes)
  filter_upwards [c.open_source.mem_nhds hx, hne] with z hz hez
  change g z = e.symm (e (g (c.symm (c z))))
  rw [c.left_inv hz, e.left_inv hez]

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter
open _root_.Metric
open scoped _root_.Topology ContDiff Manifold
universe u v w

/-- Intrinsic Hermitian convergence of orientation-preserving, asymptotically conformal native maps
implies holomorphicity in fixed source and target coordinates. (Ghys, Prop. 2.2, p. 590) -/
theorem native_coordinate_conformal_limit
    (planarCriterion :
    ∀ (U : Set ℂ) (_hU : IsOpen U) (_hne : U.Nonempty) (_hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (_hFs : ∀ n, (F n).source = U) (_hgs : g.source = U)
    (_hF : ∀ n, ContDiffOn ℝ 1 (F n) U)
    (_hFi : ∀ n, ContDiffOn ℝ 1 (F n).symm (F n).target)
    (_hd : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (F n) A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det)
    (K : ℕ → ℝ) (_hK : ∀ n, 1 ≤ K n) (_hKt : Tendsto K atTop (𝓝 1))
    (_hDist : ∀ n z, z ∈ U → ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖)
    (_hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U),
    DifferentiableOn ℂ g U)
    {r d : ℕ} {X : Type u} {Y : Type v} {M : Type w}
    [TopologicalSpace X] [ChartedSpace (ComplexModel 1) X]
    [TopologicalSpace Y] [T2Space Y] [ChartedSpace (ComplexModel 1) Y]
    [ChartedSpace (Fin r → ℝ) Y] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : Y → M) (h : HermitianTangentMetricCore d M)
    (c : OpenPartialHomeomorph X (ComplexModel 1))
    (e : OpenPartialHomeomorph Y (ComplexModel 1))
    (hc : ContMDiffOn (complexModel 1) (complexModel 1) ∞ c c.source)
    (hci : ContMDiffOn (complexModel 1) (complexModel 1) ∞ c.symm c.target)
    (he : ContMDiffOn (complexModel 1) (complexModel 1) ∞ e e.source)
    (hei : ContMDiffOn (complexModel 1) (complexModel 1) ∞ e.symm e.target)
    (heR : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel 1) 1 e e.source)
    (m : ℝ) (hm : 0 < m)
    (hbound : ∀ z ∈ e.source, ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
      m * ‖(tangentSpaceCastModel (realModel 1) (e z))
        (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel 1) e z v)‖ ≤
        leafPullbackHermitianNorm inc h z v)
    (a : ComplexModel 1) (R : ℝ) (hR : 0 < R)
    (hbuffer : closedBall a (2 * R) ⊆ e.target)
    (g : OpenPartialHomeomorph X Y) (G : ℕ → OpenPartialHomeomorph X Y)
    (V : Set (ComplexModel 1)) (hV : IsOpen V) (hne : V.Nonempty) (hconn : IsConnected V)
    (hVs : V ⊆ (c.symm.trans (g.trans e)).source)
    (hgR : ∀ z ∈ V, dist (e (g (c.symm z))) a ≤ R)
    (δ K : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hK : Tendsto K atTop (𝓝 1))
    (herr : ∀ᶠ n in atTop, ∀ z ∈ V,
      intrinsicHermitianLeafEDist (r := r) inc h (G n (c.symm z)) (g (c.symm z)) ≤ ENNReal.ofReal (δ n))
    (hgood : ∀ᶠ n in atTop,
      ContMDiffOn (realModel 1) (realModel 1) 1 (G n) (G n).source ∧
      ContMDiffOn (realModel 1) (realModel 1) 1 (G n).symm (G n).target ∧ 1 ≤ K n ∧
      ∀ z ∈ V, c.symm z ∈ (G n).source ∧
        0 < (fderiv ℝ ((chartAt (ComplexModel 1) (G n (c.symm z))) ∘ G n ∘
          (chartAt (ComplexModel 1) (c.symm z)).symm)
          (chartAt (ComplexModel 1) (c.symm z) (c.symm z))).det ∧
        ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
          ‖fderiv ℝ ((chartAt (ComplexModel 1) (G n (c.symm z))) ∘ G n ∘
            (chartAt (ComplexModel 1) (c.symm z)).symm)
            (chartAt (ComplexModel 1) (c.symm z) (c.symm z)) v‖ ≤ K n *
          ‖fderiv ℝ ((chartAt (ComplexModel 1) (G n (c.symm z))) ∘ G n ∘
            (chartAt (ComplexModel 1) (c.symm z)).symm)
            (chartAt (ComplexModel 1) (c.symm z) (c.symm z)) w‖)
    {x : X} (hx : x ∈ c.source) (hxV : c x ∈ V) :
    ContMDiffAt (complexModel 1) (complexModel 1) ∞ g x := by
  let F (n : ℕ) := c.symm.trans ((G n).trans e)
  let f := c.symm.trans (g.trans e)
  have hcoord := hermitian_uniform_coordinate_error inc h e heR m hm hbound a R hR hbuffer
    (fun n z ↦ G n (c.symm z)) (fun z ↦ g (c.symm z)) V
    (fun z hz ↦ ⟨(hVs hz).2.2, hgR z hz⟩) δ hδ herr
  have hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) f atTop V := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hcoord ε hε] with n hn
    intro z hz
    exact (dist_comm _ _).trans_lt (hn z hz).2
  have hgood' : ∀ᶠ n in atTop, V ⊆ (F n).source ∧
      ContDiffOn ℝ 1 (F n) (F n).source ∧
      ContDiffOn ℝ 1 (F n).symm (F n).target ∧ 1 ≤ K n ∧
      ∀ z ∈ V, 0 < (fderiv ℝ (F n) z).det ∧
        ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
          ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖ := by
    filter_upwards [hgood, hcoord 1 zero_lt_one] with n hn hne
    have hs : V ⊆ (F n).source := by
      intro z hz
      exact ⟨(hVs hz).1, (hn.2.2.2 z hz).1, (hne z hz).1⟩
    have hp := (contMDiffOn_complex_to_real_local hci).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
    have hq := (contMDiffOn_complex_to_real_local he).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
    have hpi := (contMDiffOn_complex_to_real_local hc).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
    have hqi := (contMDiffOn_complex_to_real_local hei).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
    refine ⟨hs, ?_, ?_, hn.2.2.1, ?_⟩
    · exact contMDiffOn_iff_contDiffOn.mp ((hq.comp' hn.1).comp' hp)
    · exact contMDiffOn_iff_contDiffOn.mp (hpi.comp' (hn.2.1.comp' hqi))
    · intro z hz
      exact native_holomorphic_partial_composition_bounds c.symm (G n) e hci hc he hei
        hn.1 (hs hz) (hn.2.2.2 z hz).2.1 (hn.2.2.2 z hz).2.2
  have hdiff := conformal_limit_of_eventual_coordinate_bounds planarCriterion V hV hne hconn
    F f hVs K hK hconv hgood'
  exact holomorphic_at_of_coordinate_differentiable c e g hc hei V hV hVs hdiff hx hxV

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Metric
open scoped _root_.Topology
universe u v

/-- A continuous leaf map admits a source coordinate disk contained in any prescribed source
neighborhood and mapped into an inner receiving ball. (Ghys, p. 590) -/
theorem buffered_holonomy_coordinate_domain
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (c : OpenPartialHomeomorph X (ComplexModel 1))
    (e : OpenPartialHomeomorph Y (ComplexModel 1))
    (g : OpenPartialHomeomorph X Y) {x : X}
    (hx : x ∈ c.source) (hxg : x ∈ g.source) (hxe : g x ∈ e.source)
    {O : Set X} (hO : O ∈ 𝓝 x) (R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧
      ball (c x) r ⊆ (c.symm.trans (g.trans e)).source ∧
      (∀ z ∈ ball (c x) r, c.symm z ∈ O) ∧
      ∀ z ∈ ball (c x) r, dist (e (g (c.symm z))) (e (g x)) < R := by
  let F := c.symm.trans (g.trans e)
  have hxs : c x ∈ F.source := by
    change c x ∈ c.target ∧ c.symm (c x) ∈ g.source ∧ g (c.symm (c x)) ∈ e.source
    rw [c.left_inv hx]
    exact ⟨c.map_source hx, hxg, hxe⟩
  have hf : F (c x) = e (g x) := by
    change e (g (c.symm (c x))) = e (g x)
    rw [c.left_inv hx]
  have hrecv : F ⁻¹' ball (e (g x)) R ∈ 𝓝 (c x) :=
    (F.continuousAt hxs).preimage_mem_nhds (hf ▸ ball_mem_nhds (F (c x)) hR)
  have hsrc : c.symm ⁻¹' O ∈ 𝓝 (c x) :=
    (c.symm.continuousAt (c.map_source hx)).preimage_mem_nhds (by rwa [c.left_inv hx])
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (F.open_source.mem_nhds hxs) (inter_mem hsrc hrecv))
  exact ⟨r, hr, fun z hz ↦ (hsub hz).1,
    fun z hz ↦ (hsub hz).2.1, fun z hz ↦ (hsub hz).2.2⟩

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Metric
open scoped _root_.Topology ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- On native complex curves, intrinsic Hermitian convergence of positively oriented maps with
distortion tending to one implies holomorphicity of the limiting holonomy map at its marked
point. (Ghys, p. 590) -/
theorem native_hermitian_conformal_limit_at
    (planarCriterion :
    ∀ (U : Set ℂ) (_hU : IsOpen U) (_hne : U.Nonempty) (_hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (_hFs : ∀ n, (F n).source = U) (_hgs : g.source = U)
    (_hF : ∀ n, ContDiffOn ℝ 1 (F n) U)
    (_hFi : ∀ n, ContDiffOn ℝ 1 (F n).symm (F n).target)
    (_hd : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (F n) A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det)
    (K : ℕ → ℝ) (_hK : ∀ n, 1 ≤ K n) (_hKt : Tendsto K atTop (𝓝 1))
    (_hDist : ∀ n z, z ∈ U → ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖)
    (_hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U),
    DifferentiableOn ℂ g U)
    {r d : ℕ} {X Y M : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel 1) X]
    [IsManifold (complexModel 1) ∞ X]
    [TopologicalSpace Y] [T2Space Y] [ChartedSpace (Fin r → ℝ) Y]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {inc : Y → M} (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) 1 inc)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    letI := U.charts
    ∀ (g : OpenPartialHomeomorph X Y) (G : ℕ → OpenPartialHomeomorph X Y)
    (x : X) (O : Set X) (_hxg : x ∈ g.source) (_hO : O ∈ 𝓝 x)
    (δ K : ℕ → ℝ) (_hδ : Tendsto δ atTop (𝓝 0)) (_hK : Tendsto K atTop (𝓝 1))
    (_herr : ∀ᶠ n in atTop, ∀ z ∈ O,
      intrinsicHermitianLeafEDist (r := r) inc h (G n z) (g z) ≤ ENNReal.ofReal (δ n))
    (_hgood : ∀ᶠ n in atTop,
      ContMDiffOn (realModel 1) (realModel 1) 1 (G n) (G n).source ∧
      ContMDiffOn (realModel 1) (realModel 1) 1 (G n).symm (G n).target ∧ 1 ≤ K n ∧
      ∀ z ∈ O, z ∈ (G n).source ∧
        0 < (fderiv ℝ ((chartAt (ComplexModel 1) (G n z)) ∘ G n ∘
          (chartAt (ComplexModel 1) z).symm)
          (chartAt (ComplexModel 1) z z)).det ∧
        ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
          ‖fderiv ℝ ((chartAt (ComplexModel 1) (G n z)) ∘ G n ∘
            (chartAt (ComplexModel 1) z).symm)
            (chartAt (ComplexModel 1) z z) v‖ ≤ K n *
          ‖fderiv ℝ ((chartAt (ComplexModel 1) (G n z)) ∘ G n ∘
            (chartAt (ComplexModel 1) z).symm)
            (chartAt (ComplexModel 1) z z) w‖),
    ContMDiffAt (complexModel 1) (complexModel 1) ∞ g x := by
  let := U.charts
  let := U.complex_manifold
  intro g G x O hxg hO δ K hδ hK herr hgood
  obtain ⟨e, hxe, heR, _, he, hei, R, m, hR, hm, hbuffer, hbound⟩ :=
    native_hermitian_buffered_chart hinc U h hh (g x)
  let c := chartAt (ComplexModel 1) x
  have hx : x ∈ c.source := ChartedSpace.mem_chart_source x
  obtain ⟨r, hr, hVs, hVO, hVR⟩ :=
    buffered_holonomy_coordinate_domain c e g hx hxg hxe hO R hR
  apply native_coordinate_conformal_limit planarCriterion inc h c e
    contMDiffOn_chart contMDiffOn_chart_symm he hei (heR.of_le (by simp))
    m hm hbound (e (g x)) R hR hbuffer g G (ball (c x) r)
    isOpen_ball (nonempty_ball.mpr hr) (convex_ball (c x) r |>.isConnected (nonempty_ball.mpr hr))
    hVs (fun z hz ↦ (hVR z hz).le) δ K hδ hK ?_ ?_ hx (mem_ball_self hr)
  · filter_upwards [herr] with n hn
    exact fun z hz ↦ hn (c.symm z) (hVO z hz)
  · filter_upwards [hgood] with n hn
    exact ⟨hn.1, hn.2.1, hn.2.2.1, fun z hz ↦ hn.2.2.2 (c.symm z) (hVO z hz)⟩

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u

/-- Biholomorphic changes of native curve leaves preserve preferred-coordinate orientation and
linear distortion bounds. (Ghys, p. 590) -/
theorem native_holomorphic_conjugation_bounds
    {X Y X' Y' : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel 1) X]
    [IsManifold (complexModel 1) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel 1) Y]
    [IsManifold (complexModel 1) ∞ Y]
    [TopologicalSpace X'] [ChartedSpace (ComplexModel 1) X']
    [TopologicalSpace Y'] [ChartedSpace (ComplexModel 1) Y']
    (P : OpenPartialHomeomorph X X') (G : OpenPartialHomeomorph X' Y')
    (Q : OpenPartialHomeomorph Y' Y)
    (hP : ContMDiffOn (complexModel 1) (complexModel 1) ∞ P P.source)
    (hPi : ContMDiffOn (complexModel 1) (complexModel 1) ∞ P.symm P.target)
    (hQ : ContMDiffOn (complexModel 1) (complexModel 1) ∞ Q Q.source)
    (hQi : ContMDiffOn (complexModel 1) (complexModel 1) ∞ Q.symm Q.target)
    (hG : ContMDiffOn (realModel 1) (realModel 1) 1 G G.source)
    {z : X} (hz : z ∈ (P.trans (G.trans Q)).source)
    (hd : 0 < (fderiv ℝ ((chartAt (ComplexModel 1) (G (P z))) ∘ G ∘
      (chartAt (ComplexModel 1) (P z)).symm)
      (chartAt (ComplexModel 1) (P z) (P z))).det) {K : ℝ}
    (hK : ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ ((chartAt (ComplexModel 1) (G (P z))) ∘ G ∘
        (chartAt (ComplexModel 1) (P z)).symm)
        (chartAt (ComplexModel 1) (P z) (P z)) v‖ ≤
      K * ‖fderiv ℝ ((chartAt (ComplexModel 1) (G (P z))) ∘ G ∘
        (chartAt (ComplexModel 1) (P z)).symm)
        (chartAt (ComplexModel 1) (P z) (P z)) w‖) :
    let H := P.trans (G.trans Q)
    let D := fderiv ℝ ((chartAt (ComplexModel 1) (H z)) ∘ H ∘
      (chartAt (ComplexModel 1) z).symm) (chartAt (ComplexModel 1) z z)
    0 < D.det ∧ ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖D v‖ ≤ K * ‖D w‖ := by
  let H := P.trans (G.trans Q)
  let c := chartAt (ComplexModel 1) z
  let e := chartAt (ComplexModel 1) (H z)
  have hc : z ∈ c.source := ChartedSpace.mem_chart_source z
  have he : H z ∈ e.source := ChartedSpace.mem_chart_source (H z)
  let P' := c.symm.trans P
  let Q' := Q.trans e
  have hp : ContMDiffOn (complexModel 1) (complexModel 1) ∞ P' P'.source :=
    hP.comp' contMDiffOn_chart_symm
  have hpi : ContMDiffOn (complexModel 1) (complexModel 1) ∞ P'.symm P'.target :=
    contMDiffOn_chart.comp' hPi
  have hq : ContMDiffOn (complexModel 1) (complexModel 1) ∞ Q' Q'.source :=
    contMDiffOn_chart.comp' hQ
  have hqi : ContMDiffOn (complexModel 1) (complexModel 1) ∞ Q'.symm Q'.target :=
    hQi.comp' contMDiffOn_chart_symm
  have hz' : c z ∈ (P'.trans (G.trans Q')).source := by
    change (c z ∈ c.target ∧ c.symm (c z) ∈ P.source) ∧
      P (c.symm (c z)) ∈ G.source ∧ G (P (c.symm (c z))) ∈ Q.source ∧
      Q (G (P (c.symm (c z)))) ∈ e.source
    rw [c.left_inv hc]
    exact ⟨⟨c.map_source hc, hz.1⟩, hz.2.1, hz.2.2, he⟩
  have heq : P' (c z) = P z := by
    change P (c.symm (c z)) = P z
    rw [c.left_inv hc]
  have hd' := native_holomorphic_partial_composition_bounds P' G Q' hp hpi hq hqi hG hz'
    (heq.symm ▸ hd) (heq.symm ▸ hK)
  exact hd'

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped _root_.Topology
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- Two-sided Hermitian comparison bounds give the corresponding distortion ratio in preferred
complex curve charts. (Ghys, p. 590) -/
theorem native_comparison_coordinate_distortion
    {r s d : ℕ} {X Y M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (Fin s → ℝ) Y]
    [IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {incX : X → M} {incY : Y → M}
    (hiX : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ incX)
    (hiY : ContMDiff 𝓘(ℝ, Fin s → ℝ) (realModel d) ∞ incY)
    (U : NativeLeafComplexUpgrade (d := d) (r := r) 1 incX)
    (V : NativeLeafComplexUpgrade (d := d) (r := s) 1 incY)
    (h : HermitianTangentMetricCore d M) {g : X → Y} {x : X}
    (hg : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g x)
    (ε : ℝ) (hε : 0 ≤ ε) (hε₁ : ε < 1)
    (hbound : ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) x,
      (1 - ε) * leafPullbackHermitianNorm incX h x v ≤
        leafPullbackHermitianNorm incY h (g x)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g x v) ∧
      leafPullbackHermitianNorm incY h (g x)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g x v) ≤
        (1 + ε) * leafPullbackHermitianNorm incX h x v) :
    letI := U.charts
    letI := V.charts
    ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ ((chartAt (ComplexModel 1) (g x)) ∘ g ∘
          (chartAt (ComplexModel 1) x).symm) (chartAt (ComplexModel 1) x x) v‖ ≤
        ((1 + ε) / (1 - ε)) *
          ‖fderiv ℝ ((chartAt (ComplexModel 1) (g x)) ∘ g ∘
          (chartAt (ComplexModel 1) x).symm) (chartAt (ComplexModel 1) x x) w‖ := by
  let := U.charts
  let := V.charts
  let := U.complex_manifold
  let := V.complex_manifold
  let c := chartAt (ComplexModel 1) x
  let e := chartAt (ComplexModel 1) (g x)
  have hc : c ∈ atlas (ComplexModel 1) X := ChartedSpace.chart_mem_atlas x
  have he : e ∈ atlas (ComplexModel 1) Y := ChartedSpace.chart_mem_atlas (g x)
  have hx : x ∈ c.source := ChartedSpace.mem_chart_source x
  have hy : g x ∈ e.source := ChartedSpace.mem_chart_source (g x)
  obtain ⟨hcR, hciR, hcφ, hcj⟩ := native_complex_chart_properties U c hc
  obtain ⟨heR, heiR, heφ, hej⟩ := native_complex_chart_properties V e he
  have hci := (hciR.contMDiffAt (c.open_target.mem_nhds (c.map_source hx))).mdifferentiableAt (by simp)
  obtain ⟨α, hα, hs⟩ := hermitian_native_coordinate_norm_scale incX h c.symm (c x)
    (by simpa only [c.left_inv hx] using hiX.mdifferentiable (by simp) x) hci
    ((hcφ.contMDiffAt (c.open_target.mem_nhds (c.map_source hx))).mdifferentiableAt (by simp))
    (hcj _ (c.map_source hx))
  obtain ⟨β, hβ, ht⟩ := hermitian_coordinate_norm_scale incY h e hy
    (hiY.mdifferentiable (by simp) (g x))
    ((heR.contMDiffAt (e.open_source.mem_nhds hy)).mdifferentiableAt (by simp))
    ((heiR.contMDiffAt (e.open_target.mem_nhds (e.map_source hy))).mdifferentiableAt (by simp))
    ((heφ.contMDiffAt (e.open_target.mem_nhds (e.map_source hy))).mdifferentiableAt (by simp))
    (hej _ (e.map_source hy))
  have heD := (heR.contMDiffAt (e.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
  have hbounds := hermitian_coordinate_comparison incX incY h c.symm e g (c x) α β ε
    hci (by simpa only [c.left_inv hx] using hg)
    (by simpa only [c.left_inv hx] using heD) hs
    (by
      have heq := congrArg (fun y : Y ↦ ∀ v : TangentSpace 𝓘(ℝ, Fin s → ℝ) y,
        leafPullbackHermitianNorm incY h y v = β *
          ‖(tangentSpaceCastModel (realModel 1) (e y))
            (mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel 1) e y v)‖)
        (congrArg g (c.left_inv hx))
      exact heq.mpr ht)
    (by
      have heq := congrArg (fun y : X ↦ ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) y,
        (1-ε) * leafPullbackHermitianNorm incX h y v ≤
          leafPullbackHermitianNorm incY h (g y)
            (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g y v) ∧
        leafPullbackHermitianNorm incY h (g y)
            (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g y v) ≤
          (1+ε) * leafPullbackHermitianNorm incX h y v) (c.left_inv hx)
      exact heq.mpr hbound)
  intro v w hv hw
  have hu := (hbounds v).2
  have hl := (hbounds w).1
  rw [hv, mul_one] at hu
  rw [hw, mul_one] at hl
  have hK : 0 ≤ (1 + ε) / (1 - ε) := div_nonneg (by linarith) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hl hK
  have hcancel : (1 + ε) / (1 - ε) * ((1 - ε) * α) = (1 + ε) * α := by
    field_simp [ne_of_gt (sub_pos.mpr hε₁)]
  rw [hcancel] at hmul
  apply (mul_le_mul_iff_right₀ hβ).mp
  calc
    β * ‖fderiv ℝ (e ∘ g ∘ c.symm) (c x) v‖ ≤ (1 + ε) * α := hu
    _ ≤ (1 + ε) / (1 - ε) * (β * ‖fderiv ℝ (e ∘ g ∘ c.symm) (c x) w‖) := hmul
    _ = β * ((1 + ε) / (1 - ε) * ‖fderiv ℝ (e ∘ g ∘ c.symm) (c x) w‖) := by ring

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- Real `C¹` regularity in native real atlases is preserved by compatible complex atlas upgrades.
(Demailly, I §3.C, p. 23) -/
theorem native_complex_upgrade_contMDiffOn
    {r s k l d : ℕ} {X Y M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (Fin s → ℝ) Y]
    [IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {incX : X → M} {incY : Y → M}
    (U : NativeLeafComplexUpgrade (d := d) (r := r) k incX) (V : NativeLeafComplexUpgrade (d := d) (r := s) l incY)
    {g : X → Y} {W : Set X}
    (hg : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) 1 g W) :
    letI := U.charts
    letI := V.charts
    ContMDiffOn (realModel k) (realModel l) 1 g W := by
  let := U.charts
  let := V.charts
  obtain ⟨_, hU⟩ := native_complex_upgrade_identity_mdifferentiable U
  obtain ⟨hV, _⟩ := native_complex_upgrade_identity_mdifferentiable V
  simpa only [Function.id_comp, Function.comp_id, Set.preimage_id] using
    ((hV.of_le (by simp)).comp_contMDiffOn hg).comp
      (hU.of_le (by simp)).contMDiffOn (fun _ h ↦ h)

end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
open Set
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- Pulling a real `C¹` expanding-plaque comparison back by holomorphic iterates preserves positive
orientation and gives distortion at most `(1 + ε) / (1 - ε)`. (Ghys, p. 590) -/
theorem native_comparison_pullback_bounds
    {d : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : Biholomorph d d M M} {S : InvariantRealTangentSplitting f.toReal}
    (L : RankOneNativeLeaves f S) (hmetric : HermitianTangentMetricCore d M)
    (x y : M) (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hε₁ : ε < 1) :
    letI := L.identification.unstableTopology x
    letI := L.identification.unstableCharts x
    letI := (L.complexUnstable x).charts
    letI := L.identification.unstableTopology y
    letI := L.identification.unstableCharts y
    letI := (L.complexUnstable y).charts
    letI := L.identification.unstableTopology ((f^[k]) x)
    letI := L.identification.unstableCharts ((f^[k]) x)
    letI := (L.complexUnstable ((f^[k]) x)).charts
    letI := L.identification.unstableTopology ((f^[k]) y)
    letI := L.identification.unstableCharts ((f^[k]) y)
    letI := (L.complexUnstable ((f^[k]) y)).charts
    ∀ (π : OpenPartialHomeomorph (UnstableAsymptoticLeaf f.toHomeomorph ((f^[k]) x))
      (UnstableAsymptoticLeaf f.toHomeomorph ((f^[k]) y)))
    (_hπ : ContMDiffOn (L.uModel ((f^[k]) x)) (L.uModel ((f^[k]) y)) 1 π π.source)
    (_hπi : ContMDiffOn (L.uModel ((f^[k]) y)) (L.uModel ((f^[k]) x)) 1 π.symm π.target)
    (W : Set (UnstableAsymptoticLeaf f.toHomeomorph x))
    (_hW : L.iterateUnstable k x '' W ⊆ π.source)
    (_hd : ∀ z ∈ L.iterateUnstable k x '' W,
      0 < (fderiv ℝ ((chartAt (ComplexModel 1) (π z)) ∘ π ∘
        (chartAt (ComplexModel 1) z).symm) (chartAt (ComplexModel 1) z z)).det)
    (_hbound : ∀ z ∈ L.iterateUnstable k x '' W,
      ∀ v : TangentSpace (L.uModel ((f^[k]) x)) z,
        (1 - ε) * leafPullbackHermitianNorm Subtype.val hmetric z v ≤
          leafPullbackHermitianNorm Subtype.val hmetric (π z)
            (mfderiv (L.uModel ((f^[k]) x)) (L.uModel ((f^[k]) y)) π z v) ∧
        leafPullbackHermitianNorm Subtype.val hmetric (π z)
            (mfderiv (L.uModel ((f^[k]) x)) (L.uModel ((f^[k]) y)) π z v) ≤
          (1 + ε) * leafPullbackHermitianNorm Subtype.val hmetric z v),
    let P := (L.iterateUnstable k x).toHomeomorph.toOpenPartialHomeomorph
    let Q := (L.iterateUnstable k y).symm.toHomeomorph.toOpenPartialHomeomorph
    let G := P.trans (π.trans Q)
    W ⊆ G.source ∧
    ContMDiffOn (realModel 1) (realModel 1) 1 G G.source ∧
    ContMDiffOn (realModel 1) (realModel 1) 1 G.symm G.target ∧
    ∀ z ∈ W,
      0 < (fderiv ℝ ((chartAt (ComplexModel 1) (G z)) ∘ G ∘
        (chartAt (ComplexModel 1) z).symm) (chartAt (ComplexModel 1) z z)).det ∧
      ∀ v w : ComplexModel 1, ‖v‖ = 1 → ‖w‖ = 1 →
        ‖fderiv ℝ ((chartAt (ComplexModel 1) (G z)) ∘ G ∘
          (chartAt (ComplexModel 1) z).symm) (chartAt (ComplexModel 1) z z) v‖ ≤
        ((1 + ε) / (1 - ε)) *
        ‖fderiv ℝ ((chartAt (ComplexModel 1) (G z)) ∘ G ∘
          (chartAt (ComplexModel 1) z).symm) (chartAt (ComplexModel 1) z z) w‖ := by
  let := L.identification.unstableTopology x
  let := L.identification.unstableCharts x
  let := (L.complexUnstable x).charts
  let := L.identification.unstableTopology y
  let := L.identification.unstableCharts y
  let := (L.complexUnstable y).charts
  let := L.identification.unstableTopology ((f^[k]) x)
  let := L.identification.unstableCharts ((f^[k]) x)
  let := (L.complexUnstable ((f^[k]) x)).charts
  let := L.identification.unstableTopology ((f^[k]) y)
  let := L.identification.unstableCharts ((f^[k]) y)
  let := (L.complexUnstable ((f^[k]) y)).charts
  let := (L.unstable ((f^[k]) x)).smoothAtlas
  let := (L.unstable ((f^[k]) y)).smoothAtlas
  let := (L.complexUnstable x).complex_manifold
  let := (L.complexUnstable y).complex_manifold
  intro π hπ hπi W hW hd hbound
  let P := (L.iterateUnstable k x).toHomeomorph.toOpenPartialHomeomorph
  let Q := (L.iterateUnstable k y).symm.toHomeomorph.toOpenPartialHomeomorph
  let G := P.trans (π.trans Q)
  have hpc := native_complex_upgrade_contMDiffOn
    (L.complexUnstable ((f^[k]) x)) (L.complexUnstable ((f^[k]) y)) hπ
  have hpic := native_complex_upgrade_contMDiffOn
    (L.complexUnstable ((f^[k]) y)) (L.complexUnstable ((f^[k]) x)) hπi
  obtain ⟨hFx, hFxi⟩ := native_unstable_iterate_holomorphic L k x
  obtain ⟨hFy, hFyi⟩ := native_unstable_iterate_holomorphic L k y
  have hP : ContMDiffOn (complexModel 1) (complexModel 1) ∞ P P.source := hFx.contMDiffOn
  have hPi : ContMDiffOn (complexModel 1) (complexModel 1) ∞ P.symm P.target := hFxi.contMDiffOn
  have hQ : ContMDiffOn (complexModel 1) (complexModel 1) ∞ Q Q.source := hFyi.contMDiffOn
  have hQi : ContMDiffOn (complexModel 1) (complexModel 1) ∞ Q.symm Q.target := hFy.contMDiffOn
  have hs : W ⊆ G.source := fun z hz ↦ ⟨mem_univ _, hW ⟨z, hz, rfl⟩, mem_univ _⟩
  refine ⟨hs, ?_, ?_, ?_⟩
  · exact ((contMDiffOn_complex_to_real_local hQ).of_le (by simp) |>.comp' hpc).comp'
      ((contMDiffOn_complex_to_real_local hP).of_le (by simp))
  · exact ((contMDiffOn_complex_to_real_local hPi).of_le (by simp)).comp'
      (hpic.comp' ((contMDiffOn_complex_to_real_local hQi).of_le (by simp)))
  · intro z hz
    have hzW : L.iterateUnstable k x z ∈ L.iterateUnstable k x '' W := ⟨z, hz, rfl⟩
    apply native_holomorphic_conjugation_bounds P π Q hP hPi hQ hQi hpc (hs hz) (hd _ hzW)
    exact native_comparison_coordinate_distortion
      (L.unstable ((f^[k]) x)).inclusion_smooth (L.unstable ((f^[k]) y)).inclusion_smooth
      (L.complexUnstable ((f^[k]) x)) (L.complexUnstable ((f^[k]) y)) hmetric
      ((hπ.contMDiffAt (π.open_source.mem_nhds (hW hzW))).mdifferentiableAt one_ne_zero)
      ε hε hε₁ (hbound _ hzW)

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold ENNReal
attribute [local instance] complex_isManifold_real
universe u


end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- Pulling an expanding comparison back by an inverse iterate contracts its error in intrinsic
Hermitian distance. (Ghys, Prop. 2.2, pp. 589–590) -/
theorem native_pullback_comparison_error
    {d : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : Biholomorph d d M M} {S : InvariantRealTangentSplitting f.toReal}
    (L : RankOneNativeLeaves f S) (hmetric : HermitianTangentMetricCore d M)
    (x y : M) (k : ℕ) (c δ : ℝ) (hc : 0 < c)
    (hbound : ∀ z (v : TangentSpace (realModel d) z),
      v ∈ S.unstable.toDistribution z →
      givenHermitianNorm hmetric ((f.symm^[k]) z)
        (mfderiv (realModel d) (realModel d) (f.symm^[k]) z v) ≤
          c * givenHermitianNorm hmetric z v) :
    letI := L.identification.unstableTopology x
    letI := L.identification.unstableCharts x
    letI := L.identification.unstableTopology y
    letI := L.identification.unstableCharts y
    letI := L.identification.unstableTopology ((f^[k]) x)
    letI := L.identification.unstableCharts ((f^[k]) x)
    letI := L.identification.unstableTopology ((f^[k]) y)
    letI := L.identification.unstableCharts ((f^[k]) y)
    ∀ (h : UnstableAsymptoticLeaf f.toHomeomorph x → UnstableAsymptoticLeaf f.toHomeomorph y) (π : UnstableAsymptoticLeaf f.toHomeomorph ((f^[k]) x) → UnstableAsymptoticLeaf f.toHomeomorph ((f^[k]) y)) (z : UnstableAsymptoticLeaf f.toHomeomorph x),
      intrinsicHermitianLeafEDist (r := (L.unstable ((f^[k]) y)).rank) Subtype.val hmetric
        (π (L.iterateUnstable k x z)) (L.iterateUnstable k y (h z)) ≤
          ENNReal.ofReal δ →
      intrinsicHermitianLeafEDist (r := (L.unstable y).rank) Subtype.val hmetric
        ((L.iterateUnstable k y).symm (π (L.iterateUnstable k x z))) (h z) ≤
          ENNReal.ofReal (c * δ) := by
  let := L.identification.unstableTopology x
  let := L.identification.unstableCharts x
  let := L.identification.unstableTopology y
  let := L.identification.unstableCharts y
  let := L.identification.unstableTopology ((f^[k]) x)
  let := L.identification.unstableCharts ((f^[k]) x)
  let := L.identification.unstableTopology ((f^[k]) y)
  let := L.identification.unstableCharts ((f^[k]) y)
  intro h π z herr
  have he (w : UnstableAsymptoticLeaf f.toHomeomorph ((f^[k]) y)) :
      ((L.iterateUnstable k y).symm w).val = (f.symm^[k]) w.val := by
    have h := L.iterateUnstable_points k y ((L.iterateUnstable k y).symm w)
    rw [(L.iterateUnstable k y).apply_symm_apply] at h
    have hinv : Function.LeftInverse f.symm f := f.symm_apply_apply
    have h' := congrArg (f.symm^[k]) h
    rw [hinv.iterate k _] at h'
    exact h'.symm
  have hc' := native_unstable_intrinsic_contraction f S.unstable.toDistribution
    ((f^[k]) y) y (L.unstable ((f^[k]) y)) (L.unstable y) hmetric k c hc hbound
    (L.iterateUnstable k y).symm he
    (π (L.iterateUnstable k x z)) (L.iterateUnstable k y (h z))
  simp only [Diffeomorph.symm_apply_apply] at hc'
  refine hc'.trans ?_
  rw [ENNReal.ofReal_mul hc.le]
  exact mul_le_mul' le_rfl herr

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped _root_.Topology
namespace StableHolonomyProof

open Filter


theorem distortion_of_two_sided_scaled_norm_bounds
    (L : ℂ →L[ℝ] ℂ) (a b ε : ℝ) (hb : 0 < b) (hε : 0 ≤ ε) (hε₁ : ε < 1)
    (hlower : ∀ v : ℂ, (1 - ε) * a * ‖v‖ ≤ b * ‖L v‖)
    (hupper : ∀ v : ℂ, b * ‖L v‖ ≤ (1 + ε) * a * ‖v‖)
    (v w : ℂ) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖L v‖ ≤ ((1 + ε) / (1 - ε)) * ‖L w‖ := by
  have hd : 0 < 1 - ε := sub_pos.mpr hε₁
  have hK : 0 ≤ (1 + ε) / (1 - ε) := div_nonneg (by linarith) hd.le
  have hu := hupper v
  have hl := hlower w
  rw [hv, mul_one] at hu
  rw [hw, mul_one] at hl
  have hmul := mul_le_mul_of_nonneg_left hl hK
  have hcancel : (1 + ε) / (1 - ε) * ((1 - ε) * a) = (1 + ε) * a := by
    field_simp
  rw [hcancel] at hmul
  apply (mul_le_mul_iff_right₀ hb).mp
  calc
    b * ‖L v‖ ≤ (1 + ε) * a := hu
    _ ≤ (1 + ε) / (1 - ε) * (b * ‖L w‖) := hmul
    _ = b * (((1 + ε) / (1 - ε)) * ‖L w‖) := by ring


theorem distortion_ratio_ge_one {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε < 1) :
    1 ≤ (1 + ε) / (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hε₁)).mpr
  linarith


theorem distortion_ratio_tendsto {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ (1 + ε n) / (1 - ε n)) atTop (𝓝 1) := by
  have hc : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hraw := (hc.add hε).div (hc.sub hε) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hlim : (1 : ℝ) + 0 = 1 := by ring
  have hlim' : (1 : ℝ) - 0 = 1 := by ring
  rw [hlim, hlim', div_one] at hraw
  exact hraw.congr' (Filter.Eventually.of_forall (fun n ↦ by rfl))

end StableHolonomyProof
end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped _root_.Topology ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- An expanding comparison on a closed native unstable disk implies holomorphicity at every
interior point of the holonomy source. (Ghys, Prop. 2.2, p. 590) -/
theorem native_comparison_on_disk_holomorphic_at
    (planarCriterion :
    ∀ (U : Set ℂ) (_hU : IsOpen U) (_hne : U.Nonempty) (_hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (_hFs : ∀ n, (F n).source = U) (_hgs : g.source = U)
    (_hF : ∀ n, ContDiffOn ℝ 1 (F n) U)
    (_hFi : ∀ n, ContDiffOn ℝ 1 (F n).symm (F n).target)
    (_hd : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (F n) A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det)
    (K : ℕ → ℝ) (_hK : ∀ n, 1 ≤ K n) (_hKt : Tendsto K atTop (𝓝 1))
    (_hDist : ∀ n z, z ∈ U → ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖)
    (_hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U),
    DifferentiableOn ℂ g U)
    {d : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : Biholomorph d d M M} {S : InvariantRealTangentSplitting f.toReal}
    (L : RankOneNativeLeaves f S) (hmetric : HermitianTangentMetricCore d M)
    (hh : IsSmoothHermitianTangentMetric hmetric) (hA : HermitianAllTimeAnosov f hmetric S)
    (x y : M) :
    letI (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableTopology a
    letI (a : M) : ChartedSpace (Fin (L.unstable a).rank → ℝ) (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableCharts a
    letI (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f.toHomeomorph a) := (L.complexUnstable a).charts
    ∀ (g : OpenPartialHomeomorph (UnstableAsymptoticLeaf f.toHomeomorph x) (UnstableAsymptoticLeaf f.toHomeomorph y)) (W : Set (UnstableAsymptoticLeaf f.toHomeomorph x)),
      L.ComparisonOnDisk hmetric x y g W →
      ∀ z ∈ interior W, z ∈ g.source →
        ContMDiffAt (complexModel 1) (complexModel 1) ∞ g z := by
  let (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableTopology a
  let (a : M) : ChartedSpace (Fin (L.unstable a).rank → ℝ) (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableCharts a
  let (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f.toHomeomorph a) := (L.complexUnstable a).charts
  let (a : M) : IsManifold (L.uModel a) ∞ (UnstableAsymptoticLeaf f.toHomeomorph a) := (L.unstable a).smoothAtlas
  let (a : M) : IsManifold (complexModel 1) ∞ (UnstableAsymptoticLeaf f.toHomeomorph a) := (L.complexUnstable a).complex_manifold
  let (a : M) : T2Space (UnstableAsymptoticLeaf f.toHomeomorph a) := (L.unstable a).hausdorff
  intro g W hcomp z hz hzg
  obtain ⟨ε, δ, hε0, hδ0, hεt, hδt, N, hN⟩ := hcomp
  obtain ⟨C, expansion, hC, hexpansion, _, hInv⟩ := hA
  let kn (n : ℕ) := n + N + 1
  have hkn : Tendsto kn atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat N)
  have hπs (n : ℕ) := hN (kn n) (by dsimp [kn]; omega)
  let π (n : ℕ) := Classical.choose (hπs n)
  have hp (n : ℕ) := Classical.choose_spec (hπs n)
  let G (n : ℕ) : OpenPartialHomeomorph (UnstableAsymptoticLeaf f.toHomeomorph x) (UnstableAsymptoticLeaf f.toHomeomorph y) :=
    (L.iterateUnstable (kn n) x).toHomeomorph.toOpenPartialHomeomorph.trans
      ((π n).trans (L.iterateUnstable (kn n) y).symm.toHomeomorph.toOpenPartialHomeomorph)
  have hbounded (n : ℕ) (w : M) (v : TangentSpace (realModel d) w)
      (hv : v ∈ S.unstable.toDistribution w) :
      givenHermitianNorm hmetric ((f.symm^[kn n]) w)
        (mfderiv (realModel d) (realModel d) (f.symm^[kn n]) w v) ≤
          C * givenHermitianNorm hmetric w v := by
    have hp : expansion ^ (-(kn n : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ hexpansion.le (by omega)
    apply (hInv (kn n) (by dsimp [kn]; omega) w v hv).trans
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)
  have herr : ∀ᶠ n in atTop, ∀ w ∈ interior W,
      intrinsicHermitianLeafEDist (r := (L.unstable y).rank) Subtype.val hmetric
        (G n w) (g w) ≤ ENNReal.ofReal (C * δ (kn n)) := by
    apply Eventually.of_forall
    intro n w hw
    have hw' : L.iterateUnstable (kn n) x w ∈ L.iterateUnstable (kn n) x '' W :=
      ⟨w, interior_subset hw, rfl⟩
    have he := (hp n).2.2.2.2.2.2 _ hw'
    have he' : intrinsicHermitianLeafEDist
        (r := (L.unstable ((f^[kn n]) y)).rank) Subtype.val hmetric
        (π n (L.iterateUnstable (kn n) x w)) (L.iterateUnstable (kn n) y (g w)) ≤
          ENNReal.ofReal (δ (kn n)) := by
      change intrinsicHermitianLeafEDist (r := (L.unstable ((f^[kn n]) y)).rank)
        Subtype.val hmetric (π n (L.iterateUnstable (kn n) x w))
        (L.iterateUnstable (kn n) y (g ((L.iterateUnstable (kn n) x).symm
          (L.iterateUnstable (kn n) x w)))) ≤ ENNReal.ofReal (δ (kn n)) at he
      simpa only [Diffeomorph.symm_apply_apply] using he
    exact native_pullback_comparison_error L hmetric x y (kn n) C (δ (kn n)) hC
      (hbounded n) g (π n) w he'
  have hdt : Tendsto (fun n ↦ C * δ (kn n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hδt.comp hkn)
  have hKt := StableHolonomyProof.distortion_ratio_tendsto (hεt.comp hkn)
  apply native_hermitian_conformal_limit_at planarCriterion (L.unstable y).inclusion_smooth
    (L.complexUnstable y) hmetric hh g G z (interior W) hzg (isOpen_interior.mem_nhds hz)
    (fun n ↦ C * δ (kn n)) (fun n ↦ (1 + ε (kn n)) / (1 - ε (kn n))) hdt hKt herr
  have hsmall : ∀ᶠ n in atTop, ε (kn n) < 1 :=
    (hεt.comp hkn).eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hsmall] with n hn
  obtain ⟨hsrc, hsm, hsmi, hb⟩ := native_comparison_pullback_bounds L hmetric x y (kn n)
    (ε (kn n)) (hε0 _) hn (π n) (hp n).2.1 (hp n).2.2.1 W (hp n).1
      (hp n).2.2.2.2.1 (hp n).2.2.2.2.2.1
  exact ⟨hsm, hsmi, StableHolonomyProof.distortion_ratio_ge_one (hε0 _) hn,
    fun w hw ↦ ⟨hsrc (interior_subset hw), hb w (interior_subset hw)⟩⟩

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter
open _root_.Metric
open scoped _root_.Topology
universe u

/-- Every neighborhood in a complex curve contains a closed coordinate disk about its center, with
the center in the disk's intrinsic interior. (Ghys, p. 589) -/
theorem small_native_complex_disk
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 1) X]
    (x : X) {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ r : ℝ, 0 < r ∧
      closedBall (chartAt (ComplexModel 1) x x) r ⊆ (chartAt (ComplexModel 1) x).target ∧
      (chartAt (ComplexModel 1) x).symm '' closedBall (chartAt (ComplexModel 1) x x) r ⊆ N ∧
      x ∈ interior ((chartAt (ComplexModel 1) x).symm ''
        closedBall (chartAt (ComplexModel 1) x x) r) := by
  let c := chartAt (ComplexModel 1) x
  have hx : x ∈ c.source := ChartedSpace.mem_chart_source x
  have ht : c x ∈ c.target := c.map_source hx
  have hn : c.target ∩ c.symm ⁻¹' N ∈ 𝓝 (c x) :=
    inter_mem (c.open_target.mem_nhds ht)
      ((c.symm.continuousAt ht).preimage_mem_nhds (by simpa only [c.left_inv hx] using hN))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε/2, half_pos hε, ?_, ?_, ?_⟩
  · intro a ha
    exact (hball (mem_ball.mpr ((mem_closedBall.mp ha).trans_lt (half_lt_self hε)))).1
  · rintro z ⟨a, ha, rfl⟩
    exact (hball (mem_ball.mpr ((mem_closedBall.mp ha).trans_lt (half_lt_self hε)))).2
  · apply mem_interior_iff_mem_nhds.mpr
    have hm := c.symm.image_mem_nhds ht (Metric.ball_mem_nhds (c x) (half_pos hε))
    rw [c.left_inv hx] at hm
    exact Filter.mem_of_superset hm (image_mono ball_subset_closedBall)

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped _root_.Topology ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- Every pointed map with the germ of a local stable-path representative in the comparison
presentation is holomorphic at its marked point. (Ghys, pp. 589–590) -/
theorem native_representative_holomorphic_at
    (planarCriterion :
    ∀ (U : Set ℂ) (_hU : IsOpen U) (_hne : U.Nonempty) (_hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (_hFs : ∀ n, (F n).source = U) (_hgs : g.source = U)
    (_hF : ∀ n, ContDiffOn ℝ 1 (F n) U)
    (_hFi : ∀ n, ContDiffOn ℝ 1 (F n).symm (F n).target)
    (_hd : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (F n) A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det)
    (K : ℕ → ℝ) (_hK : ∀ n, 1 ≤ K n) (_hKt : Tendsto K atTop (𝓝 1))
    (_hDist : ∀ n z, z ∈ U → ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖)
    (_hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U),
    DifferentiableOn ℂ g U)
    {d : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : Biholomorph d d M M} {S : InvariantRealTangentSplitting f.toReal}
    (L : RankOneNativeLeaves f S) (hmetric : HermitianTangentMetricCore d M)
    (hh : IsSmoothHermitianTangentMetric hmetric) (hA : HermitianAllTimeAnosov f hmetric S)
    (hL : L.ComparisonProperty hmetric) :
    letI := L.realAmbientCharts
    letI (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableTopology a
    letI (a : M) : ChartedSpace (Fin (L.unstable a).rank → ℝ) (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableCharts a
    letI (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f.toHomeomorph a) := (L.complexUnstable a).charts
    ∀ q : Quotient L.foliation.stablePartition,
    letI := L.foliation.stableTopology q
    ∀ (x y : IntrinsicFoliationLeaf L.foliation.stablePartition q) (γ : Path x y)
    (e : PathHolonomyRepresentative L.foliation γ 0 1)
    (g : OpenPartialHomeomorph (UnstableAsymptoticLeaf f.toHomeomorph (γ 0).val)
      (UnstableAsymptoticLeaf f.toHomeomorph (γ 1).val)),
      L.uPoint (γ 0).val ∈ g.source → g (L.uPoint (γ 0).val) = L.uPoint (γ 1).val →
      (∀ᶠ z in 𝓝 (L.uPoint (γ 0).val), g z = L.holonomyRepresentative γ e z) →
      ContMDiffAt (complexModel 1) (complexModel 1) ∞ g (L.uPoint (γ 0).val) := by
  let := L.realAmbientCharts
  let (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableTopology a
  let (a : M) : ChartedSpace (Fin (L.unstable a).rank → ℝ) (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableCharts a
  let (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f.toHomeomorph a) := (L.complexUnstable a).charts
  intro q
  let := L.foliation.stableTopology q
  intro x y γ e g hgs hgp hgerm
  obtain ⟨N, hNo, hNx, hNs, hNC⟩ := hL q x y γ e g hgs hgp hgerm
  obtain ⟨r, hr, hrt, hWN, hi⟩ := small_native_complex_disk
    (X := UnstableAsymptoticLeaf f.toHomeomorph (γ 0).val) (L.uPoint (γ 0).val) (hNo.mem_nhds hNx)
  let c := chartAt (M := UnstableAsymptoticLeaf f.toHomeomorph (γ 0).val) (ComplexModel 1) (L.uPoint (γ 0).val)
  let W := c.symm '' Metric.closedBall (c (L.uPoint (γ 0).val)) r
  have hW : L.IsComplexClosedDisk (γ 0).val W :=
    ⟨c, ChartedSpace.chart_mem_atlas (M := UnstableAsymptoticLeaf f.toHomeomorph (γ 0).val) _, c (L.uPoint (γ 0).val), r, hr, hrt, rfl⟩
  exact native_comparison_on_disk_holomorphic_at planarCriterion L hmetric hh hA
    (γ 0).val (γ 1).val g W (hNC W hW hWN hi) _ hi hgs

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped _root_.Topology ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real

/-- The comparison presentation's transported representative is holomorphic at its source mark. -/
theorem native_actual_representative_holomorphic_at
    (planarCriterion :
    ∀ (U : Set ℂ) (_hU : IsOpen U) (_hne : U.Nonempty) (_hc : IsConnected U)
    (F : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (_hFs : ∀ n, (F n).source = U) (_hgs : g.source = U)
    (_hF : ∀ n, ContDiffOn ℝ 1 (F n) U)
    (_hFi : ∀ n, ContDiffOn ℝ 1 (F n).symm (F n).target)
    (_hd : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (F n) A.toContinuousLinearMap z ∧ 0 < A.toContinuousLinearMap.det)
    (K : ℕ → ℝ) (_hK : ∀ n, 1 ≤ K n) (_hKt : Tendsto K atTop (𝓝 1))
    (_hDist : ∀ n z, z ∈ U → ∀ v w : ℂ, ‖v‖ = 1 → ‖w‖ = 1 →
      ‖fderiv ℝ (F n) z v‖ ≤ K n * ‖fderiv ℝ (F n) z w‖)
    (_hconv : TendstoLocallyUniformlyOn (fun n z ↦ F n z) g atTop U),
    DifferentiableOn ℂ g U)
    {d : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : Biholomorph d d M M} {S : InvariantRealTangentSplitting f.toReal}
    (L : RankOneNativeLeaves f S) (hmetric : HermitianTangentMetricCore d M)
    (hh : IsSmoothHermitianTangentMetric hmetric) (hA : HermitianAllTimeAnosov f hmetric S)
    (hL : L.ComparisonProperty hmetric) :
    letI := L.realAmbientCharts
    letI (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableTopology a
    letI (a : M) : ChartedSpace (Fin (L.unstable a).rank → ℝ) (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableCharts a
    letI (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f.toHomeomorph a) := (L.complexUnstable a).charts
    ∀ q : Quotient L.foliation.stablePartition,
    letI := L.foliation.stableTopology q
    ∀ (x y : IntrinsicFoliationLeaf L.foliation.stablePartition q) (γ : Path x y)
    (e : PathHolonomyRepresentative L.foliation γ 0 1),
      let g := L.identification.transportUnstableLocalMap (γ 0).val (γ 1).val e.map
      ContMDiffAt (complexModel 1) (complexModel 1) ∞ g (L.uPoint (γ 0).val) := by
  let := L.realAmbientCharts
  let (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableTopology a
  let (a : M) : ChartedSpace (Fin (L.unstable a).rank → ℝ) (UnstableAsymptoticLeaf f.toHomeomorph a) := L.identification.unstableCharts a
  let (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f.toHomeomorph a) := (L.complexUnstable a).charts
  intro q
  let := L.foliation.stableTopology q
  intro x y γ e
  apply native_representative_holomorphic_at planarCriterion L hmetric hh hA hL q x y γ e
  · simp only [NativeTransverseAsymptoticIdentification.transportUnstableLocalMap,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.preimage_univ]
    refine ⟨⟨Set.mem_univ _, ?_⟩, Set.mem_univ _⟩
    change (L.identification.unstableClassHomeomorph (γ 0).val).symm
      ((L.identification.unstableClassHomeomorph (γ 0).val)
        (L.foliation.uPoint (γ 0).val)) ∈ e.map.source
    rw [Homeomorph.symm_apply_apply]
    exact e.source_point
  · change L.unstableClass (γ 1).val
      (e.map ((L.unstableClass (γ 0).val).symm (L.unstableClass (γ 0).val
        (L.foliation.uPoint (γ 0).val)))) = _
    rw [Homeomorph.symm_apply_apply, e.map_point]
    rfl
  · exact Eventually.of_forall (fun _ ↦ rfl)

end HolomorphicAnosov.Ghys
