import HolomorphicAnosov.Geometry.ContinuousOriginalFrameNorms
import HolomorphicAnosov.Analysis.MovingAlmostIsometryG18
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import HolomorphicAnosov.Paper.Ghys.NativeUnstableComplexRankOneFromRealRankTwo
import HolomorphicAnosov.Geometry.NativePlaqueTubeDerivativeG18
import HolomorphicAnosov.Geometry.ContinuousComplexRankOneSubbundle
import HolomorphicAnosov.Geometry.ComplexDerivativeRangeOfRealCharts
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity


noncomputable section
namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
/-- An injective complex derivative has positive real determinant in the same complex coordinate model. (Demailly, I §3.C.) -/
theorem complex_model_derivative_det_pos
    {n : ℕ} {f : ComplexModel n → ComplexModel n} {z : ComplexModel n}
    (hf : DifferentiableAt ℂ f z) (hi : Function.Injective (fderiv ℂ f z)) :
    0 < (fderiv ℝ f z).det := by
  rw [(hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change 0 < LinearMap.det ((fderiv ℂ f z).toLinearMap.restrictScalars ℝ)
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  apply Complex.normSq_pos.mpr
  intro hzero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) (LinearMap.ker_eq_bot.mpr hi)

/-- A holomorphic coordinate homeomorphism with holomorphic inverse preserves the complex orientation. (Demailly, I §3.C.) -/
theorem holomorphic_coordinate_det_pos
    {n : ℕ} (e : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n))
    (he : ContMDiffOn (complexModel n) (complexModel n) ∞ e e.source)
    (hi : ContMDiffOn (complexModel n) (complexModel n) ∞ e.symm e.target)
    {z : ComplexModel n} (hz : z ∈ e.source) : 0 < (fderiv ℝ e z).det := by
  have hm : e.MDifferentiable (complexModel n) (complexModel n) :=
    ⟨he.mdifferentiableOn (by simp), hi.mdifferentiableOn (by simp)⟩
  apply complex_model_derivative_det_pos
  · exact (mdifferentiableAt_iff_differentiableAt.mp (hm.mdifferentiableAt hz))
  · have h := hm.mfderiv_injective hz
    rw [mfderiv_eq_fderiv] at h
    change Function.Injective (fderiv ℂ e z) at h
    exact h

end HolomorphicAnosov.Ghys

noncomputable section
open Filter
open scoped _root_.Topology
namespace HolomorphicAnosov

/-- Every complex-linear coordinate equivalence preserves canonical real orientation. -/
theorem complex_equiv_real_det_pos_g18 {n : ℕ}
    (S : ComplexModel n ≃L[ℂ] ComplexModel n) :
    0 < (S.restrictScalars ℝ).toContinuousLinearMap.det := by
  change 0 < LinearMap.det (S.toLinearEquiv.toLinearMap.restrictScalars ℝ)
  rw [LinearMap.det_restrictScalars,Algebra.norm_complex_eq]
  apply Complex.normSq_pos.mpr
  intro hzero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero)
    (LinearMap.ker_eq_bot.mpr S.injective)

/-- Changing source and target complex frames preserves positivity of the real coefficient determinant, including when the map itself is merely real linear. -/
theorem real_det_pos_complex_frame_change_g18 {n : ℕ}
    (C : ComplexModel n →L[ℝ] ComplexModel n) (hC : 0 < C.det)
    (S T : ComplexModel n ≃L[ℂ] ComplexModel n) :
    0 < ((T.restrictScalars ℝ).toContinuousLinearMap.comp
      (C.comp (S.restrictScalars ℝ).toContinuousLinearMap)).det := by
  change 0 < LinearMap.det ((T.restrictScalars ℝ).toLinearEquiv.toLinearMap.comp
    (C.toLinearMap.comp (S.restrictScalars ℝ).toLinearEquiv.toLinearMap))
  rw [LinearMap.det_comp,LinearMap.det_comp]
  exact mul_pos (complex_equiv_real_det_pos_g18 T)
    (mul_pos hC (complex_equiv_real_det_pos_g18 S))

/-- A continuous real coefficient map equal to identity at the diagonal eventually has positive determinant in every choice of source and target complex frames. -/
theorem moving_complex_frame_orientation_g18 {n : ℕ} {B : Type*} [TopologicalSpace B]
    (C : B → ComplexModel n →L[ℝ] ComplexModel n) {t₀ : B}
    (hC : ContinuousAt C t₀) (hC₀ : C t₀ = ContinuousLinearMap.id ℝ (ComplexModel n)) :
    ∀ᶠ t in 𝓝 t₀, ∀ S T : ComplexModel n ≃L[ℂ] ComplexModel n,
      0 < ((T.restrictScalars ℝ).toContinuousLinearMap.comp
        ((C t).comp (S.restrictScalars ℝ).toContinuousLinearMap)).det := by
  have hd : ContinuousAt (fun t ↦ (C t).det) t₀ :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hC
  have hpos : 0 < (C t₀).det := by
    rw [hC₀]
    change 0 < LinearMap.det (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)
    rw [LinearMap.det_id]
    exact zero_lt_one
  filter_upwards [continuousAt_const.eventually_lt hd hpos] with t ht
  exact real_det_pos_complex_frame_change_g18 (C t) ht

/-- The differentiated inclusion square transfers orientation from a physical complex-frame coefficient to the real coordinate derivative. The two vertical maps are complex-linear changes of basis, but the horizontal map may be merely real linear. -/
theorem real_det_pos_of_complex_frame_square_g18 {n : ℕ}
    (R C : ComplexModel n →L[ℝ] ComplexModel n)
    (S T : ComplexModel n ≃L[ℂ] ComplexModel n)
    (hsquare : (T.restrictScalars ℝ).toContinuousLinearMap.comp R =
      C.comp (S.restrictScalars ℝ).toContinuousLinearMap)
    (hC : 0 < C.det) : 0 < R.det := by
  have hd := congrArg ContinuousLinearMap.det hsquare
  change LinearMap.det ((T.restrictScalars ℝ).toLinearEquiv.toLinearMap.comp
      R.toLinearMap) =
    LinearMap.det (C.toLinearMap.comp
      (S.restrictScalars ℝ).toLinearEquiv.toLinearMap) at hd
  rw [LinearMap.det_comp, LinearMap.det_comp] at hd
  have hprod : 0 < (T.restrictScalars ℝ).toContinuousLinearMap.det * R.det :=
    hd ▸ mul_pos hC (complex_equiv_real_det_pos_g18 S)
  exact (mul_pos_iff_of_pos_left (complex_equiv_real_det_pos_g18 T)).mp hprod

/-- A moving physical coefficient equal to identity at the diagonal gives canonical positive orientation for every coordinate derivative satisfying the actual differentiated inclusion square. -/
theorem moving_complex_frame_square_orientation_g18 {n : ℕ} {B : Type*}
    [TopologicalSpace B]
    (C : B → ComplexModel n →L[ℝ] ComplexModel n) {t₀ : B}
    (hC : ContinuousAt C t₀) (hC₀ : C t₀ = ContinuousLinearMap.id ℝ (ComplexModel n)) :
    ∀ᶠ t in 𝓝 t₀, ∀ (R : ComplexModel n →L[ℝ] ComplexModel n)
      (S T : ComplexModel n ≃L[ℂ] ComplexModel n),
      (T.restrictScalars ℝ).toContinuousLinearMap.comp R =
        (C t).comp (S.restrictScalars ℝ).toContinuousLinearMap → 0 < R.det := by
  have hd : ContinuousAt (fun t ↦ (C t).det) t₀ :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hC
  have hpos : 0 < (C t₀).det := by
    rw [hC₀]
    change 0 < LinearMap.det (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)
    rw [LinearMap.det_id]
    exact zero_lt_one
  filter_upwards [continuousAt_const.eventually_lt hd hpos] with t ht R S T hsquare
  exact real_det_pos_of_complex_frame_square_g18 R (C t) S T hsquare ht

end HolomorphicAnosov

end


noncomputable section
open Set Bundle
open scoped ContDiff Manifold _root_.Topology
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
universe u v

/-- An intrinsic complex inclusion derivative identifies its chart model with the actual complex tangent subspace. Composing this identification with any complex subbundle frame gives a complex-linear change of coordinates, preserving exactly the included tangent vector. -/
theorem intrinsic_complex_frame_equiv_g18
    {n d : ℕ} {X : Type u} {M : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : X → M) (x : X)
    (hinj : Function.Injective (mfderiv (complexModel n) (complexModel d) inc x))
    (S : Submodule ℂ (TangentSpace (complexModel d) (inc x)))
    (hrange : (mfderiv (complexModel n) (complexModel d) inc x).range = S)
    (frame : S ≃L[ℂ] ComplexModel n) :
    ∃ e : ComplexModel n ≃L[ℂ] ComplexModel n, ∀ v,
      (frame.symm (e v)).val = mfderiv (complexModel n) (complexModel d) inc x
        ((tangentSpaceCastModel (complexModel n) x).symm v) := by
  let D := mfderiv (complexModel n) (complexModel d) inc x
  let A := D.comp (tangentSpaceCastModel (complexModel n) x).symm.toContinuousLinearMap
  have hA (v : ComplexModel n) : A v ∈ S := by
    rw [← hrange]
    exact ⟨(tangentSpaceCastModel (complexModel n) x).symm v,rfl⟩
  let Ac : ComplexModel n →L[ℂ] S := A.codRestrict S hA
  have hbij : Function.Bijective Ac := by
    constructor
    · intro v w hvw
      apply (tangentSpaceCastModel (complexModel n) x).symm.injective
      apply hinj
      exact congrArg Subtype.val hvw
    · intro w
      have hw : w.val ∈ D.range := by rw [hrange]; exact w.property
      obtain ⟨v,hv⟩ := hw
      refine ⟨(tangentSpaceCastModel (complexModel n) x) v,Subtype.ext ?_⟩
      change D ((tangentSpaceCastModel (complexModel n) x).symm
        ((tangentSpaceCastModel (complexModel n) x) v)) = w.val
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact hv
  let C : ComplexModel n →L[ℂ] ComplexModel n := frame.toContinuousLinearMap.comp Ac
  have hCbij : Function.Bijective C := frame.bijective.comp hbij
  let a : ComplexModel n ≃L[ℂ] ComplexModel n :=
    (LinearEquiv.ofBijective C.toLinearMap hCbij).toContinuousLinearEquivOfContinuous C.continuous
  refine ⟨a,?_⟩
  intro v
  change (frame.symm (frame (Ac v))).val = _
  rw [frame.symm_apply_apply]
  rfl

/-- Equality of the original real tangent images gives equality of complex inclusion image and complex distribution, through the same native realification. The cross-atlas derivative theorem supplies the left equality in applications. -/
theorem complex_range_eq_of_realification_g18
    {d : ℕ} {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (x : M) (S T : Submodule ℂ (TangentSpace (complexModel d) x))
    (h : (S.restrictScalars ℝ).map (complexTangentToReal d x).toLinearEquiv.toLinearMap =
      (T.restrictScalars ℝ).map (complexTangentToReal d x).toLinearEquiv.toLinearMap) : S = T := by
  have heq := Submodule.map_injective_of_injective (complexTangentToReal d x).injective h
  ext v
  exact SetLike.ext_iff.mp heq v

/-- The real derivative in the preferred complex charts is exactly the native real tangent derivative expressed in those same chart models. -/
theorem real_chart_derivative_native_g18
    {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    (p : X → Y) (x : X) (hp : MDifferentiableAt (realModel n) (realModel n) p x)
    (v : ComplexModel n) :
    mfderiv (realModel n) (realModel n) p x
      (complexTangentToReal n x ((tangentSpaceCastModel (complexModel n) x).symm v)) =
    complexTangentToReal n (p x)
      ((tangentSpaceCastModel (complexModel n) (p x)).symm
        (fderiv ℝ ((chartAt (ComplexModel n) (p x)) ∘ p ∘
          (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x) v)) := by
  rw [hp.mfderiv]
  simp only [realModel,modelWithCornersSelf_coe,Set.range_id,fderivWithin_univ]
  rfl

/-- An physical derivative identity gives the complex-frame inclusion square for the real derivative in the intrinsic complex charts.. -/
theorem intrinsic_complex_frame_derivative_square_g18
    {n d : ℕ} {X Y M : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (incX : X → M) (incY : Y → M) (p : X → Y) (x : X)
    (hx : MDifferentiableAt (complexModel n) (complexModel d) incX x)
    (hy : MDifferentiableAt (complexModel n) (complexModel d) incY (p x))
    (hp : MDifferentiableAt (realModel n) (realModel n) p x)
    (SX : Submodule ℂ (TangentSpace (complexModel d) (incX x)))
    (SY : Submodule ℂ (TangentSpace (complexModel d) (incY (p x))))
    (frameX : SX ≃L[ℂ] ComplexModel n) (frameY : SY ≃L[ℂ] ComplexModel n)
    (s t : ComplexModel n ≃L[ℂ] ComplexModel n)
    (hs : ∀ v, (frameX.symm (s v)).val =
      mfderiv (complexModel n) (complexModel d) incX x
        ((tangentSpaceCastModel (complexModel n) x).symm v))
    (ht : ∀ v, (frameY.symm (t v)).val =
      mfderiv (complexModel n) (complexModel d) incY (p x)
        ((tangentSpaceCastModel (complexModel n) (p x)).symm v))
    (A : TangentSpace (realModel d) (incX x) →L[ℝ]
      TangentSpace (realModel d) (incY (p x)))
    (C : ComplexModel n →L[ℝ] ComplexModel n)
    (hC : ∀ v, complexTangentToReal d (incY (p x)) (frameY.symm (C v)).val =
      A (complexTangentToReal d (incX x) (frameX.symm v).val))
    (hA : ∀ v, A (mfderiv (realModel n) (realModel d) incX x v) =
      mfderiv (realModel n) (realModel d) incY (p x)
        (mfderiv (realModel n) (realModel n) p x v)) :
    (t.restrictScalars ℝ).toContinuousLinearMap.comp
      (fderiv ℝ ((chartAt (ComplexModel n) (p x)) ∘ p ∘
        (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x)) =
      C.comp (s.restrictScalars ℝ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change t ((fderiv ℝ ((chartAt (ComplexModel n) (p x)) ∘ p ∘
    (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x)) v) = C (s v)
  apply frameY.symm.injective
  apply Subtype.val_injective
  apply (complexTangentToReal d (incY (p x))).injective
  rw [ht,hC,hs]
  rw [← mfderiv_complex_to_real hy,← mfderiv_complex_to_real hx,hA,
    real_chart_derivative_native_g18 p x hp v]


end HolomorphicAnosov


end

noncomputable section
open Set Bundle
open scoped ContDiff Manifold _root_.Topology
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- A genuine complex subbundle frame is jointly continuous in the native tangent bundle, using precisely the induced topology in the subbundle definition. -/
theorem complex_frame_total_continuous_g18
    {d r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x)) :
    letI : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∀ e : Trivialization (ComplexModel r)
      (TotalSpace.proj (F := ComplexModel r) (E := fun x ↦ ↥(S x))),
    ∀ he : e.IsLinear ℂ, letI := he
    Continuous (fun z : e.baseSet × ComplexModel r ↦
      (⟨z.1.val,((e.linearEquivAt ℂ z.1.val z.1.prop).symm z.2).val⟩ :
        TangentBundle (complexModel d) M)) := by
  let : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  intro e he
  let := he
  have h := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
    (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)
    (fun p : e.baseSet × ComplexModel r ↦ e.mem_target.mpr p.1.prop)
  have h' : Continuous (fun p : e.baseSet × ComplexModel r ↦
      (⟨p.1.val,(e.linearEquivAt ℂ p.1.val p.1.prop).symm p.2⟩ :
        TotalSpace (ComplexModel r) (fun x ↦ ↥(S x)))) := by
    convert h using 1
    funext p
    exact e.toPretrivialization.mk_symm p.1.prop p.2
  exact continuous_induced_dom.comp h'

/-- Physical operators preserving the actual complex subspace have genuine real coefficient operators in a chosen complex frame. -/
theorem complex_frame_coefficient_exists_g18
    {d r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (x y : M) (s : S x ≃ₗ[ℂ] ComplexModel r) (t : S y ≃ₗ[ℂ] ComplexModel r)
    (A : TangentSpace (realModel d) x →L[ℝ] TangentSpace (realModel d) y)
    (hA : ∀ v : S x, (complexTangentToReal d y).symm
      (A (complexTangentToReal d x v.val)) ∈ S y) :
    ∃ C : ComplexModel r →L[ℝ] ComplexModel r, ∀ v,
      complexTangentToReal d y (t.symm (C v)).val =
        A (complexTangentToReal d x (s.symm v).val) := by
  let B : S x →ₗ[ℝ] S y :=
    (((complexTangentToReal d y).symm.toLinearEquiv.toLinearMap.comp
      A.toLinearMap).comp ((complexTangentToReal d x).toLinearEquiv.toLinearMap.comp
        ((S x).subtype.restrictScalars ℝ))).codRestrict ((S y).restrictScalars ℝ) hA
  let C : ComplexModel r →ₗ[ℝ] ComplexModel r :=
    (t.restrictScalars ℝ).toLinearMap.comp (B.comp (s.symm.restrictScalars ℝ).toLinearMap)
  refine ⟨C.toContinuousLinearMap,?_⟩
  intro v
  change complexTangentToReal d y (t.symm (t (B (s.symm v)))).val = _
  rw [t.symm_apply_apply]
  exact (complexTangentToReal d y).apply_symm_apply _

/-- Continuity of actual physical frame images gives continuity of their real coefficient operator in the genuine complex subbundle frame. -/
theorem complex_frame_coefficient_continuous_g18
    {d r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x)) :
    letI : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∀ e : Trivialization (ComplexModel r)
      (TotalSpace.proj (F := ComplexModel r) (E := fun x ↦ ↥(S x))),
    ∀ he : e.IsLinear ℂ, letI := he
    ∀ {B : Type*} [TopologicalSpace B] (σ τ : B → e.baseSet)
      (A : ∀ b, TangentSpace (realModel d) (σ b).val →L[ℝ]
        TangentSpace (realModel d) (τ b).val)
      (C : B → ComplexModel r →L[ℝ] ComplexModel r),
    (∀ b v, complexTangentToReal d (τ b).val
      (((e.linearEquivAt ℂ (τ b).val (τ b).prop).symm (C b v)).val) =
        A b (complexTangentToReal d (σ b).val
          (((e.linearEquivAt ℂ (σ b).val (σ b).prop).symm v).val))) →
    Continuous (fun z : B × ComplexModel r ↦
      (⟨(τ z.1).val,A z.1 (complexTangentToReal d (σ z.1).val
        (((e.linearEquivAt ℂ (σ z.1).val (σ z.1).prop).symm z.2).val))⟩ :
          TangentBundle (realModel d) M)) → Continuous C := by
  let : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  intro e he
  let := he
  intro B _ σ τ A C hC hA
  have hcomplex := continuous_complexTangentToReal_symm.comp hA
  have hsub : Continuous (fun z : B × ComplexModel r ↦
      (⟨(τ z.1).val,(e.linearEquivAt ℂ (τ z.1).val (τ z.1).prop).symm
        (C z.1 z.2)⟩ : TotalSpace (ComplexModel r) (fun x ↦ ↥(S x)))) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun z : B × ComplexModel r ↦
      (⟨(τ z.1).val,((e.linearEquivAt ℂ (τ z.1).val (τ z.1).prop).symm
        (C z.1 z.2)).val⟩ : TangentBundle (complexModel d) M))
    apply hcomplex.congr
    intro z
    dsimp only [Function.comp_apply]
    congr 1
    exact ((complexTangentToReal d (τ z.1).val).symm_apply_eq).mpr (hC z.1 z.2).symm
  have hcoord := (e.continuousOn.comp_continuous hsub
    (fun z ↦ e.mem_source.mpr (τ z.1).prop)).snd
  have hc : Continuous (fun z : B × ComplexModel r ↦ C z.1 z.2) := by
    convert hcoord using 1
    funext z
    exact ((e.linearEquivAt ℂ (τ z.1).val (τ z.1).prop).apply_symm_apply _).symm
  apply continuous_clm_apply.mpr
  intro v
  exact hc.comp (continuous_id.prodMk continuous_const)


end HolomorphicAnosov
end

noncomputable section
open Set Bundle
open scoped ContDiff Manifold _root_.Topology
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real


/-- Actual tangent-chart transport has continuous images of the genuine complex subbundle frame. This specializes the coordinate-operator continuity theorem to native complex realification, with the original physical operator unchanged. -/
theorem physical_complex_frame_continuous_g18
    {d r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x)) :
    letI : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∀ e : Trivialization (ComplexModel r)
      (TotalSpace.proj (F := ComplexModel r) (E := fun x ↦ ↥(S x))),
    ∀ he : e.IsLinear ℂ, letI := he
    ∀ {B : Type*} [TopologicalSpace B] (anchor : M)
      (σ τ : B → e.baseSet), Continuous σ → Continuous τ →
    ∀ (hσ : ∀ b, (σ b).val ∈ (trivializationAt (ComplexModel d)
          (TangentSpace (realModel d)) anchor).baseSet)
      (hτ : ∀ b, (τ b).val ∈ (trivializationAt (ComplexModel d)
          (TangentSpace (realModel d)) anchor).baseSet)
      (V : B → ComplexModel d →L[ℝ] ComplexModel d), Continuous V →
    let tr := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) anchor
    let A : ∀ b, TangentSpace (realModel d) (σ b).val →L[ℝ]
        TangentSpace (realModel d) (τ b).val := fun b ↦
      (tr.continuousLinearEquivAt ℝ (τ b).val (hτ b)).symm.toContinuousLinearMap.comp
        ((V b).comp (tr.continuousLinearEquivAt ℝ (σ b).val (hσ b)).toContinuousLinearMap)
    Continuous (fun z : B × ComplexModel r ↦
      (⟨(τ z.1).val,A z.1 (complexTangentToReal d (σ z.1).val
        (((e.linearEquivAt ℂ (σ z.1).val (σ z.1).prop).symm z.2).val))⟩ :
          TangentBundle (realModel d) M)) := by
  let : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  intro e he
  let := he
  intro B _ anchor σ τ hσcont hτcont hσ hτ V hV
  dsimp only
  have hv := continuous_complexTangentToReal.comp
    ((complex_frame_total_continuous_g18 S e he).comp
      ((hσcont.comp continuous_fst).prodMk continuous_snd))
  exact tangent_chart_operator_continuous_g18 anchor
    (fun z : B × ComplexModel r ↦ (σ z.1).val) (fun z ↦ (τ z.1).val)
    ((continuous_subtype_val.comp hτcont).comp continuous_fst)
    (fun z ↦ hσ z.1) (fun z ↦ hτ z.1)
    (fun z ↦ V z.1) (hV.comp continuous_fst)
    (fun z ↦ complexTangentToReal d (σ z.1).val
      (((e.linearEquivAt ℂ (σ z.1).val (σ z.1).prop).symm z.2).val)) hv

/-- Continuous physical operators preserving the true complex tangent spaces have continuous real frame coefficients. A literal identity on the marked frame gives positive real determinant on a neighborhood of the marked parameter. -/
theorem physical_complex_frame_orientation_g18
    {d r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x)) :
    letI : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∀ e : Trivialization (ComplexModel r)
      (TotalSpace.proj (F := ComplexModel r) (E := fun x ↦ ↥(S x))),
    ∀ he : e.IsLinear ℂ, letI := he
    ∀ {B : Type*} [TopologicalSpace B] (σ τ : B → e.baseSet)
      (A : ∀ b, TangentSpace (realModel d) (σ b).val →L[ℝ]
        TangentSpace (realModel d) (τ b).val) (b₀ : B),
    (∀ b (v : S (σ b).val), (complexTangentToReal d (τ b).val).symm
      (A b (complexTangentToReal d (σ b).val v.val)) ∈ S (τ b).val) →
    Continuous (fun z : B × ComplexModel r ↦
      (⟨(τ z.1).val,A z.1 (complexTangentToReal d (σ z.1).val
        (((e.linearEquivAt ℂ (σ z.1).val (σ z.1).prop).symm z.2).val))⟩ :
          TangentBundle (realModel d) M)) →
    (∀ v, A b₀ (complexTangentToReal d (σ b₀).val
        (((e.linearEquivAt ℂ (σ b₀).val (σ b₀).prop).symm v).val)) =
      complexTangentToReal d (τ b₀).val
        (((e.linearEquivAt ℂ (τ b₀).val (τ b₀).prop).symm v).val)) →
    ∃ C : B → ComplexModel r →L[ℝ] ComplexModel r,
      Continuous C ∧ (∀ b v, complexTangentToReal d (τ b).val
        (((e.linearEquivAt ℂ (τ b).val (τ b).prop).symm (C b v)).val) =
          A b (complexTangentToReal d (σ b).val
            (((e.linearEquivAt ℂ (σ b).val (σ b).prop).symm v).val))) ∧
      C b₀ = ContinuousLinearMap.id ℝ (ComplexModel r) ∧
      ∀ᶠ b in 𝓝 b₀, 0 < (C b).det := by
  let : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  intro e he
  let := he
  intro B _ σ τ A b₀ hpres hcont hdiag
  choose C hC using fun b ↦ complex_frame_coefficient_exists_g18 S (σ b).val (τ b).val
    (e.linearEquivAt ℂ (σ b).val (σ b).prop)
    (e.linearEquivAt ℂ (τ b).val (τ b).prop) (A b) (hpres b)
  have hc := complex_frame_coefficient_continuous_g18 S e he σ τ A C hC hcont
  have hid : C b₀ = ContinuousLinearMap.id ℝ (ComplexModel r) := by
    apply ContinuousLinearMap.ext
    intro v
    apply (e.linearEquivAt ℂ (τ b₀).val (τ b₀).prop).symm.injective
    apply Subtype.val_injective
    apply (complexTangentToReal d (τ b₀).val).injective
    exact (hC b₀ v).trans (hdiag v)
  refine ⟨C,hc,hC,hid,?_⟩
  have hdet := ContinuousLinearMap.continuous_det.comp hc
  have hpos : 0 < (C b₀).det := by
    rw [hid]
    change 0 < LinearMap.det (LinearMap.id : ComplexModel r →ₗ[ℝ] ComplexModel r)
    rw [LinearMap.det_id]
    exact zero_lt_one
  exact continuousAt_const.eventually_lt hdet.continuousAt hpos


/-- Reuse the orientation frame's physical continuity for original metric norm bounds. -/
theorem complex_frame_original_norm_g18
    {d r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (P : RealTangentDistribution (realModel d) M)
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hS : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = P x)
    (g : ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (TangentSpace (realModel d) : M → Type _)) :
    letI : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∀ e : Trivialization (ComplexModel r)
      (TotalSpace.proj (F := ComplexModel r) (E := fun x ↦ ↥(S x))),
    ∀ he : e.IsLinear ℂ, letI := he
    letI : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {B : Type*} [TopologicalSpace B] (σ τ : B → e.baseSet), Continuous σ →
    ∀ (A : ∀ t, TangentSpace (realModel d) (σ t).val →L[ℝ]
        TangentSpace (realModel d) (τ t).val),
    Continuous (fun z : B × ComplexModel r ↦
      (⟨(τ z.1).val,A z.1 (complexTangentToReal d (σ z.1).val
        (((e.linearEquivAt ℂ (σ z.1).val (σ z.1).prop).symm z.2).val))⟩ :
          TangentBundle (realModel d) M)) →
    ∀ t₀ : B, (τ t₀).val = (σ t₀).val →
    (∀ v, A t₀ (complexTangentToReal d (σ t₀).val
        (((e.linearEquivAt ℂ (σ t₀).val (σ t₀).prop).symm v).val)) =
      complexTangentToReal d (τ t₀).val
        (((e.linearEquivAt ℂ (τ t₀).val (τ t₀).prop).symm v).val)) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 t₀, ∀ v : P (σ t).val,
      (1-ε)*‖v‖ ≤ ‖A t v.val‖ ∧ ‖A t v.val‖ ≤ (1+ε)*‖v‖ := by
  let : TopologicalSpace (TotalSpace (ComplexModel r) (fun x ↦ ↥(S x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  intro e he
  let := he
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  intro B _ σ τ hσ A hphysical t₀ hbase hdiag ε hε
  let F : ∀ t : B, ComplexModel r ≃ₗ[ℝ] P (σ t).val := fun t ↦
    ((e.linearEquivAt ℂ (σ t).val (σ t).prop).symm.restrictScalars ℝ).trans
      (((complexTangentToReal d (σ t).val).toLinearEquiv.submoduleMap
        ((S (σ t).val).restrictScalars ℝ)).trans (LinearEquiv.ofEq _ _ (hS _)))
  let A' : ∀ t : B, P (σ t).val →L[ℝ] TangentSpace (realModel d) (τ t).val :=
    fun t ↦ (A t).comp (P (σ t).val).subtypeL
  have hv := continuous_complexTangentToReal.comp
    ((complex_frame_total_continuous_g18 S e he).comp
      ((hσ.comp continuous_fst).prodMk continuous_snd))
  have hs : Continuous (fun z : B × ComplexModel r ↦ ‖F z.1 z.2‖) :=
    FixedBlockEstimates.Native.continuous_original_norm g
      (fun z : B × ComplexModel r ↦ (σ z.1).val)
      (fun z ↦ (F z.1 z.2).val) hv
  have ht : Continuous (fun z : B × ComplexModel r ↦ ‖A' z.1 (F z.1 z.2)‖) :=
    FixedBlockEstimates.Native.continuous_original_norm g
      (fun z : B × ComplexModel r ↦ (τ z.1).val)
      (fun z ↦ A' z.1 (F z.1 z.2)) hphysical
  have hisom (v : P (σ t₀).val) : ‖A' t₀ v‖ = ‖v‖ := by
    obtain ⟨w,rfl⟩ := (F t₀).surjective v
    change ‖A t₀ (complexTangentToReal d (σ t₀).val
      (((e.linearEquivAt ℂ (σ t₀).val (σ t₀).prop).symm w).val))‖ = _
    rw [hdiag]
    change ‖complexTangentToReal d (τ t₀).val
      (((e.linearEquivAt ℂ (τ t₀).val (τ t₀).prop).symm w).val)‖ =
      ‖complexTangentToReal d (σ t₀).val
      (((e.linearEquivAt ℂ (σ t₀).val (σ t₀).prop).symm w).val)‖
    exact congrArg (fun z : e.baseSet ↦ ‖complexTangentToReal d z.val
      (((e.linearEquivAt ℂ z.val z.prop).symm w).val)‖) (Subtype.ext hbase)
  exact moving_isometry_eventually_norm_bounds_g18 F A' hs ht t₀ hisom hε


end HolomorphicAnosov
namespace HolomorphicAnosov.HPS
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {Dist : RealTangentDistribution 𝓘(ℝ,E) M}
  {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
  {F : LeafPartition Dist ι L r} {x : M} {d : ℕ}
  {Φ : FiniteC1NativePlaqueFamily F x d} {n : ℕ}

/-- The actual native zero-normal projection is the identity on its physical unstable distribution. This is vector equality in the original tangent fiber, stronger than equality of norms and sufficient for the coefficient diagonal. -/
theorem native_physical_projection_identity_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (q : Φ.family.centerDomain) (u : Fin d → ℝ)
    (hu : u ∈ Metric.ball 0 Φ.family.radius)
    (v : TangentSpace 𝓘(ℝ,E) ((Φ.family.plaque q).param u))
    (hv : v ∈ Dist ((Φ.family.plaque q).param u)) :
    let p := (Φ.family.plaque q).param u
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) Φ.family.receivingAnchor
    ∀ hp : p ∈ tr.baseSet,
    let J := tr.continuousLinearEquivAt ℝ p hp
    J.symm (plaqueMetricProjection
      (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate q u))
      (fderiv ℝ (H.coordinate q) u) (J v)) = v := by
  dsimp only
  intro hp
  have hdom : u ∈ (Φ.family.plaque q).domain := by rw [Φ.family.domain_eq]; exact hu
  have hP := ((Φ.family.plaque q).smooth u hdom).contMDiffAt
    ((Φ.family.plaque q).domain_open.mem_nhds hdom)
  have heq : H.coordinate q =ᶠ[𝓝 u]
      ((extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor) ∘ (Φ.family.plaque q).param) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hu] with w hw
    exact H.coordinate_eq q hw
  have hid := plaque_physical_projection_identity_g18 g Φ.family.receivingAnchor
    (Φ.family.plaque q).param u (hP.mdifferentiableAt (by simp))
    ((Φ.family.plaque q).immersed u hdom) (Φ.family.receiving_domain q u hu) v
    (by rw [(Φ.family.plaque q).tangent u hdom]; exact hv)
  rw [H.coordinate_eq q hu,heq.fderiv_eq]
  exact hid

end HolomorphicAnosov.HPS
open Set Bundle
open scoped Manifold ContDiff _root_.Topology
namespace HolomorphicAnosov
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Undoing the receiving tangent chart in the derivative of a native plaque projection gives a vector in the actual physical tangent range of that plaque. -/
theorem physical_projection_range_g18
    (anchor : M) (P : V → M) (B : E → V) (w v : E)
    (hP : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,E) P (B w))
    (hB : DifferentiableAt ℝ B w)
    (hx : P (B w) ∈ (extChartAt 𝓘(ℝ,E) anchor).source) :
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
    let hx' : P (B w) ∈ tr.baseSet := by
      simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
    let J := tr.continuousLinearEquivAt ℝ (P (B w)) hx'
    J.symm (fderiv ℝ ((extChartAt 𝓘(ℝ,E) anchor) ∘ P ∘ B) w v) ∈
      (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) P (B w)).range := by
  dsimp only
  let ca := extChartAt 𝓘(ℝ,E) anchor
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
  have hx' : P (B w) ∈ tr.baseSet := by
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
  let J := tr.continuousLinearEquivAt ℝ (P (B w)) hx'
  have hJ : J.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca (P (B w)) := by
    rw [show J.toContinuousLinearMap = tr.continuousLinearMapAt ℝ (P (B w)) from
      tr.coe_continuousLinearEquivAt_eq' hx']
    exact TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [extChartAt_source] using hx)
  have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) ca (P (B w)) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hf : fderiv ℝ (ca ∘ P ∘ B) w = J.toContinuousLinearMap.comp
      ((mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) P (B w)).comp (fderiv ℝ B w)) := by
    rw [← mfderiv_eq_fderiv,hJ,
      mfderiv_comp w hc (hP.comp w hB.mdifferentiableAt),
      mfderiv_comp w hP hB.mdifferentiableAt,mfderiv_eq_fderiv]
    rfl
  refine ⟨fderiv ℝ B w v,?_⟩
  change _ = J.symm (fderiv ℝ (ca ∘ P ∘ B) w v)
  rw [hf]
  exact (J.symm_apply_apply _).symm

end HolomorphicAnosov

namespace HolomorphicAnosov.HPS
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {Dist : RealTangentDistribution 𝓘(ℝ,E) M}
  {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
  {F : LeafPartition Dist ι L r} {x : M} {d : ℕ}
  {Φ : FiniteC1NativePlaqueFamily F x d} {n : ℕ}

omit [FiniteDimensional ℝ E] in
/-- Every actual coordinate projection into a native plaque differentiates into its actual physical distribution, after undoing the receiving tangent chart. -/
theorem native_physical_projection_range_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n) (q : Φ.family.centerDomain)
    (B : E → Fin d → ℝ) (w v : E) (hB : DifferentiableAt ℝ B w)
    (hu : B w ∈ Metric.ball 0 Φ.family.radius) :
    let p := (Φ.family.plaque q).param (B w)
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) Φ.family.receivingAnchor
    ∀ hp : p ∈ tr.baseSet,
      (tr.continuousLinearEquivAt ℝ p hp).symm
        (fderiv ℝ (fun z ↦ H.coordinate q (B z)) w v) ∈ Dist p := by
  dsimp only
  intro hp
  have hdom : B w ∈ (Φ.family.plaque q).domain := by rw [Φ.family.domain_eq]; exact hu
  have hP := ((Φ.family.plaque q).smooth (B w) hdom).contMDiffAt
    ((Φ.family.plaque q).domain_open.mem_nhds hdom)
  have heq : (fun z ↦ H.coordinate q (B z)) =ᶠ[𝓝 w]
      ((extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor) ∘ (Φ.family.plaque q).param ∘ B) := by
    filter_upwards [hB.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hu)] with z hz
    exact H.coordinate_eq q hz
  rw [heq.fderiv_eq]
  have h := HolomorphicAnosov.physical_projection_range_g18 Φ.family.receivingAnchor
    (Φ.family.plaque q).param B w v (hP.mdifferentiableAt (by simp)) hB
    (Φ.family.receiving_domain q (B w) hu)
  rw [(Φ.family.plaque q).tangent (B w) hdom] at h
  exact h

end HolomorphicAnosov.HPS
open Set Bundle
open scoped ContDiff Manifold _root_.Topology
namespace HolomorphicAnosov

/-- The locally trivial frame of a genuine complex line subbundle has exactly one complex coordinate. -/
theorem complex_rank_one_frame_g18
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x, Module.finrank ℂ (S.toDistribution x) = 1) (x : M) :
    letI : TopologicalSpace (TotalSpace (ComplexModel 1) (fun y ↦ ↥(S.toDistribution y))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∃ e : Trivialization (ComplexModel 1)
      (TotalSpace.proj (F := ComplexModel 1) (E := fun y ↦ ↥(S.toDistribution y))),
      x ∈ e.baseSet ∧ e.IsLinear ℂ := by
  obtain ⟨r,e,hx,he⟩ := S.locally_trivial x
  let : TopologicalSpace (TotalSpace (ComplexModel r) (fun y ↦ ↥(S.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let := he
  have hr : r = 1 := by
    have h := (e.linearEquivAt ℂ x hx).finrank_eq
    rw [hS x] at h
    simpa using h.symm
  subst r
  exact ⟨e,hx,he⟩

/-- Membership in a realified complex subspace is equivalent to membership after the native inverse realification. -/
theorem complex_subspace_mem_of_realification_g18
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (x : M) (S : Submodule ℂ (TangentSpace (complexModel d) x))
    (P : Submodule ℝ (TangentSpace (realModel d) x))
    (hSP : (S.restrictScalars ℝ).map (complexTangentToReal d x).toLinearEquiv.toLinearMap = P)
    (v : TangentSpace (realModel d) x) (hv : v ∈ P) :
    (complexTangentToReal d x).symm v ∈ S := by
  rw [← hSP] at hv
  obtain ⟨w,hw,hweq⟩ := hv
  change complexTangentToReal d x w = v at hweq
  rw [← hweq,ContinuousLinearEquiv.symm_apply_apply]
  exact hw

end HolomorphicAnosov
namespace HolomorphicAnosov.HPS
universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel m) M] [IsManifold (complexModel m) ∞ M]
attribute [local instance] complex_isManifold_real
variable {Dist : RealTangentDistribution (realModel m) M}
  {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
  {F : LeafPartition Dist ι L r} {x : M} {d : ℕ}
  {Φ : FiniteC1NativePlaqueFamily F x d} {n : ℕ}
variable (g : ContMDiffRiemannianMetric (realModel m) ∞ (ComplexModel m)
  (TangentSpace (realModel m) : M → Type _))
variable (S : ∀ p : M, Submodule ℂ (TangentSpace (complexModel m) p)) (s : ℕ)
local instance nativeOrientationFrameTopology : TopologicalSpace
    (TotalSpace (ComplexModel s) (fun p : M ↦ ↥(S p))) :=
  TopologicalSpace.induced
    (fun z ↦ (⟨z.proj,z.snd.val⟩ : TangentBundle (complexModel m) M)) inferInstance
variable (frame : Trivialization (ComplexModel s)
  (TotalSpace.proj (F := ComplexModel s) (E := fun p : M ↦ ↥(S p))))
variable [hframe : frame.IsLinear ℂ]

/-- The actual zero-normal operator sends each marked complex frame vector to that same frame vector, even with separately named source and receiving points. -/
theorem native_complex_frame_diagonal_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (hS : ∀ p, ((S p).restrictScalars ℝ).map
      (complexTangentToReal m p).toLinearEquiv.toLinearMap = Dist p)
    (q : Φ.family.centerDomain) (u : Fin d → ℝ)
    (hu : u ∈ Metric.ball 0 Φ.family.radius)
    (a b : M) (ha : a = (Φ.family.plaque q).param u)
    (hb : b = (Φ.family.plaque q).param u)
    (hfa : a ∈ frame.baseSet) (hfb : b ∈ frame.baseSet) :
    let tr := trivializationAt (ComplexModel m) (TangentSpace (realModel m))
      Φ.family.receivingAnchor
    ∀ hga : a ∈ tr.baseSet, ∀ hgb : b ∈ tr.baseSet, ∀ v : ComplexModel s,
      (tr.continuousLinearEquivAt ℝ b hgb).symm
        (plaqueMetricProjection
          (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate q u))
          (fderiv ℝ (H.coordinate q) u)
          ((tr.continuousLinearEquivAt ℝ a hga)
            (complexTangentToReal m a (((frame.linearEquivAt ℂ a hfa).symm v).val)))) =
        complexTangentToReal m b (((frame.linearEquivAt ℂ b hfb).symm v).val) := by
  subst a
  subst b
  dsimp only
  intro hga hgb v
  apply native_physical_projection_identity_g18 H g q u hu _ ?_ hga
  rw [← hS]
  exact ⟨((frame.linearEquivAt ℂ _ hfa).symm v).val,
    ((frame.linearEquivAt ℂ _ hfa).symm v).property,rfl⟩




/-- One ambient open neighborhood gives original-metric norm bounds and positive real determinant for the actual native inverse projection in the fixed complex subbundle frame, uniformly over nearby receiving labels and source points. The exact physical coefficient identity is retained for the intrinsic complex-chart derivative square. -/
theorem native_physical_projection_open_control_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (hS : ∀ p, ((S p).restrictScalars ℝ).map
      (complexTangentToReal m p).toLinearEquiv.toLinearMap = Dist p)
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Q : TopologicalSpace.Opens Φ.family.centerDomain)
    (W : Set (ComplexModel m)) (hW : IsOpen W)
    (e : Q → OpenPartialHomeomorph ((Fin d → ℝ) × K) (ComplexModel m))
    (ht : ∀ q, (e q).target = W)
    (he : ∀ q, ContDiffOn ℝ 1 (e q).symm (e q).target)
    (hbase : ∀ q, ∀ z ∈ (e q).source, z.1 ∈ Metric.ball 0 Φ.family.radius)
    (hc : ContinuousOn (fun z : Q × ComplexModel m ↦ (e z.1).symm z.2) (univ ×ˢ W))
    (hd : ContinuousOn (fun z : Q × ComplexModel m ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ W))
    (q₀ : Q) (hpframe : q₀.val.val ∈ frame.baseSet)
    (hpchart : q₀.val.val ∈ (extChartAt (realModel m) Φ.family.receivingAnchor).source)
    (hptarget : extChartAt (realModel m) Φ.family.receivingAnchor q₀.val.val ∈ W)
    (hinv₀ : (e q₀).symm (extChartAt (realModel m) Φ.family.receivingAnchor q₀.val.val) = 0)
    (hderiv₀ : HasFDerivAt (fun w ↦ H.coordinate q₀.val ((e q₀).symm w).1)
      (plaqueMetricProjection
        (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate q₀.val 0))
        (fderiv ℝ (H.coordinate q₀.val) 0))
      (extChartAt (realModel m) Φ.family.receivingAnchor q₀.val.val))
    (ε : ℝ) (hε : 0 < ε) :
    let ca := extChartAt (realModel m) Φ.family.receivingAnchor
    let tr := trivializationAt (ComplexModel m) (TangentSpace (realModel m))
      Φ.family.receivingAnchor
    let τ : Q → M → M := fun q x ↦ (Φ.family.plaque q.val).param ((e q).symm (ca x)).1
    let V : Q → M → ComplexModel m →L[ℝ] ComplexModel m := fun q x ↦
      fderiv ℝ (fun w ↦ H.coordinate q.val ((e q).symm w).1) (ca x)
    ∃ A : Set M, IsOpen A ∧ q₀.val.val ∈ A ∧ A ⊆ ca.source ∩ ca ⁻¹' W ∧
      ∀ q : Q, q.val.val ∈ A → ∀ x ∈ A,
        ∃ (hxf : x ∈ frame.baseSet) (hyf : τ q x ∈ frame.baseSet)
          (hx : x ∈ tr.baseSet) (hy : τ q x ∈ tr.baseSet)
          (C : ComplexModel s →L[ℝ] ComplexModel s),
          0 < C.det ∧ (∀ v,
            complexTangentToReal m (τ q x)
              (((frame.linearEquivAt ℂ (τ q x) hyf).symm (C v)).val) =
            (tr.continuousLinearEquivAt ℝ (τ q x) hy).symm
              (V q x ((tr.continuousLinearEquivAt ℝ x hx)
                (complexTangentToReal m x
                  (((frame.linearEquivAt ℂ x hxf).symm v).val))))) ∧
          ∀ v : Dist x,
            let av := (tr.continuousLinearEquivAt ℝ (τ q x) hy).symm
              (V q x ((tr.continuousLinearEquivAt ℝ x hx) v.val))
            (1-ε)*Real.sqrt (g.inner x v.val v.val) ≤
                Real.sqrt (g.inner (τ q x) av av) ∧
              Real.sqrt (g.inner (τ q x) av av) ≤
                (1+ε)*Real.sqrt (g.inner x v.val v.val) := by
  dsimp only
  let ca := extChartAt (realModel m) Φ.family.receivingAnchor
  let tr := trivializationAt (ComplexModel m) (TangentSpace (realModel m))
    Φ.family.receivingAnchor
  let Ux : Set M := frame.baseSet ∩ (ca.source ∩ ca ⁻¹' W)
  have hUx : IsOpen Ux := frame.open_baseSet.inter
    ((continuousOn_extChartAt (I := realModel m) Φ.family.receivingAnchor).isOpen_inter_preimage
      (isOpen_extChartAt_source _) hW)
  let Ω₀ : Set (Q × M) := univ ×ˢ Ux
  have hΩ₀ : IsOpen Ω₀ := isOpen_univ.prod hUx
  let t₀ : Ω₀ := ⟨(q₀,q₀.val.val),mem_univ _,hpframe,hpchart,hptarget⟩
  let coords : Ω₀ → Q × ComplexModel m := fun t ↦ (t.val.1,ca t.val.2)
  have hcoords : Continuous coords :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuousOn_extChartAt (I := realModel m) Φ.family.receivingAnchor).comp_continuous
        (continuous_snd.comp continuous_subtype_val) (fun t ↦ t.property.2.2.1))
  have hmaps : ∀ t : Ω₀, coords t ∈ univ ×ˢ W := fun t ↦ ⟨mem_univ _,t.property.2.2.2⟩
  have hinv : Continuous (fun t : Ω₀ ↦ (e t.val.1).symm (ca t.val.2)) :=
    hc.comp_continuous hcoords hmaps
  have hu : ∀ t : Ω₀, ((e t.val.1).symm (ca t.val.2)).1 ∈ Metric.ball 0 Φ.family.radius := by
    intro t
    exact hbase t.val.1 _ ((e t.val.1).map_target (by rw [ht]; exact t.property.2.2.2))
  let τ₀ : Ω₀ → M := fun t ↦ (Φ.family.plaque t.val.1.val).param
    ((e t.val.1).symm (ca t.val.2)).1
  have hτ₀ : Continuous τ₀ := Φ.family.jointly_continuous.comp
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (hinv.fst.subtype_mk hu))
  have hτcenter : τ₀ t₀ = q₀.val.val := by
    change (Φ.family.plaque q₀.val).param ((e q₀).symm (ca q₀.val.val)).1 = _
    rw [hinv₀]
    exact (Φ.family.plaque q₀.val).centered
  let Ω : Set Ω₀ := τ₀ ⁻¹' frame.baseSet
  have hΩ : IsOpen Ω := frame.open_baseSet.preimage hτ₀
  let b₀ : Ω := ⟨t₀,show τ₀ t₀ ∈ frame.baseSet by rw [hτcenter]; exact hpframe⟩
  let q : Ω → Q := fun t ↦ t.val.val.1
  let σ : Ω → frame.baseSet := fun t ↦ ⟨t.val.val.2,t.val.property.2.1⟩
  let τ : Ω → frame.baseSet := fun t ↦ ⟨τ₀ t.val,t.property⟩
  let V : Ω → ComplexModel m →L[ℝ] ComplexModel m := fun t ↦
    fderiv ℝ (fun w ↦ H.coordinate (q t).val ((e (q t)).symm w).1) (ca (σ t).val)
  have hσ : Continuous σ :=
    (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have hτ : Continuous τ := (hτ₀.comp continuous_subtype_val).subtype_mk _
  have hV : Continuous V :=
    ((native_inverse_projection_derivative_continuous_g18 H Q W e ht he hbase hc hd).comp_continuous
      hcoords hmaps).comp continuous_subtype_val
  have hσtr : ∀ t : Ω, (σ t).val ∈ tr.baseSet := by
    intro t
    simpa only [tr,ca,σ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      t.val.property.2.2.1
  have hτtr : ∀ t : Ω, (τ t).val ∈ tr.baseSet := by
    intro t
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      Φ.family.receiving_domain (q t).val _ (hu t.val)
  let Aphys : ∀ t : Ω, TangentSpace (realModel m) (σ t).val →L[ℝ]
      TangentSpace (realModel m) (τ t).val := fun t ↦
    (tr.continuousLinearEquivAt ℝ (τ t).val (hτtr t)).symm.toContinuousLinearMap.comp
      ((V t).comp (tr.continuousLinearEquivAt ℝ (σ t).val (hσtr t)).toContinuousLinearMap)
  have hpres (t : Ω) (v : S (σ t).val) :
      (complexTangentToReal m (τ t).val).symm
        (Aphys t (complexTangentToReal m (σ t).val v.val)) ∈ S (τ t).val := by
    apply complex_subspace_mem_of_realification_g18 _ _ _ (hS _) _
    have htgt : ca (σ t).val ∈ (e (q t)).target := by rw [ht]; exact t.val.property.2.2.2
    have hB := ((he (q t)).contDiffAt ((e (q t)).open_target.mem_nhds htgt)).differentiableAt
      (by simp : (1 : WithTop ℕ∞) ≠ 0)
    exact native_physical_projection_range_g18 H (q t).val
      (fun w ↦ ((e (q t)).symm w).1) (ca (σ t).val)
      ((tr.continuousLinearEquivAt ℝ (σ t).val (hσtr t))
        (complexTangentToReal m (σ t).val v.val)) hB.fst (hu t.val) (hτtr t)
  have hphysical := physical_complex_frame_continuous_g18 S frame hframe
    Φ.family.receivingAnchor σ τ hσ hτ hσtr hτtr V hV
  have hdiag (v : ComplexModel s) :
      Aphys b₀ (complexTangentToReal m (σ b₀).val
        (((frame.linearEquivAt ℂ (σ b₀).val (σ b₀).prop).symm v).val)) =
      complexTangentToReal m (τ b₀).val
        (((frame.linearEquivAt ℂ (τ b₀).val (τ b₀).prop).symm v).val) := by
    dsimp only [Aphys,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    have hV₀ : V b₀ = plaqueMetricProjection
        (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate q₀.val 0))
        (fderiv ℝ (H.coordinate q₀.val) 0) := hderiv₀.fderiv
    rw [hV₀]
    exact native_complex_frame_diagonal_g18 g S s frame H hS q₀.val 0
      (Metric.mem_ball_self Φ.family.radius_pos) (σ b₀).val (τ b₀).val
      (Φ.family.plaque q₀.val).centered.symm
      (hτcenter.trans (Φ.family.plaque q₀.val).centered.symm)
      (σ b₀).prop (τ b₀).prop (hσtr b₀) (hτtr b₀) v
  obtain ⟨C,hC,hcoeff,hCid,hpos⟩ :=
    physical_complex_frame_orientation_g18 S frame hframe σ τ Aphys b₀ hpres hphysical hdiag
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel m) x) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm := complex_frame_original_norm_g18 Dist S hS g frame hframe
    σ τ hσ Aphys hphysical b₀ hτcenter hdiag ε hε
  obtain ⟨T,hpoint,hTopen,hb₀⟩ := eventually_nhds_iff.mp (hpos.and hnorm)
  let inclusion : Ω → Q × M := fun t ↦ t.val.val
  let τQ : Q → M → M := fun q x ↦
    (Φ.family.plaque q.val).param ((e q).symm (ca x)).1
  let VQ : Q → M → ComplexModel m →L[ℝ] ComplexModel m := fun q x ↦
    fderiv ℝ (fun w ↦ H.coordinate q.val ((e q).symm w).1) (ca x)
  let result : Q × M → Prop := fun z ↦
        ∃ (hxf : z.2 ∈ frame.baseSet) (hyf : τQ z.1 z.2 ∈ frame.baseSet)
          (hx : z.2 ∈ tr.baseSet) (hy : τQ z.1 z.2 ∈ tr.baseSet)
          (C : ComplexModel s →L[ℝ] ComplexModel s),
          0 < C.det ∧ (∀ v,
            complexTangentToReal m (τQ z.1 z.2)
              (((frame.linearEquivAt ℂ (τQ z.1 z.2) hyf).symm (C v)).val) =
            (tr.continuousLinearEquivAt ℝ (τQ z.1 z.2) hy).symm
              (VQ z.1 z.2 ((tr.continuousLinearEquivAt ℝ z.2 hx)
                (complexTangentToReal m z.2
                  (((frame.linearEquivAt ℂ z.2 hxf).symm v).val))))) ∧
          ∀ v : Dist z.2,
            let av := (tr.continuousLinearEquivAt ℝ (τQ z.1 z.2) hy).symm
              (VQ z.1 z.2 ((tr.continuousLinearEquivAt ℝ z.2 hx) v.val))
            (1-ε)*Real.sqrt (g.inner z.2 v.val v.val) ≤
                Real.sqrt (g.inner (τQ z.1 z.2) av av) ∧
              Real.sqrt (g.inner (τQ z.1 z.2) av av) ≤
                (1+ε)*Real.sqrt (g.inner z.2 v.val v.val)
  have hresult (t : Ω) (htT : t ∈ T) : result (inclusion t) := by
    refine ⟨(σ t).prop,(τ t).prop,hσtr t,hτtr t,C t,(hpoint t htT).1,hcoeff t,?_⟩
    intro v
    have hv := (hpoint t htT).2 v
    change (1-ε)*‖v.val‖ ≤ _ ∧ _ ≤ (1+ε)*‖v.val‖ at hv
    dsimp only [Aphys,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe] at hv
    rw [norm_eq_sqrt_real_inner,norm_eq_sqrt_real_inner] at hv
    exact hv
  have himage : IsOpen (inclusion '' T) :=
    (hΩ₀.isOpenEmbedding_subtypeVal.comp hΩ.isOpenEmbedding_subtypeVal).isOpenMap _ hTopen
  have hnhds : inclusion '' T ∈ 𝓝 (q₀,q₀.val.val) := himage.mem_nhds ⟨b₀,hb₀,rfl⟩
  have hrel : ∀ᶠ z : Q × M in 𝓝 (q₀,q₀.val.val), result z := by
    filter_upwards [hnhds] with z hz
    obtain ⟨t,ht,heq⟩ := hz
    exact heq ▸ hresult t ht
  obtain ⟨A,hA,hqA,hAG,hAR⟩ := open_label_relation_localization_g18
    (fun q : Q ↦ q.val.val)
    (Φ.family.centerDomain_open.isOpenEmbedding_subtypeVal.comp
      Q.isOpen.isOpenEmbedding_subtypeVal) q₀
    (fun q x ↦ result (q,x)) hrel Ux hUx ⟨hpframe,hpchart,hptarget⟩
  exact ⟨A,hA,hqA,fun _ hx ↦ (hAG hx).2,hAR⟩


/-- One ambient open neighborhood gives positive real determinant for the actual native inverse projection in the fixed complex subbundle frame, uniformly over nearby receiving labels and source points. The exact physical coefficient identity is retained for the intrinsic complex-chart derivative square. -/
theorem native_physical_projection_open_orientation_g18
    (H : FiniteOrderNativePlaqueCoherence Φ n)
    (hS : ∀ p, ((S p).restrictScalars ℝ).map
      (complexTangentToReal m p).toLinearEquiv.toLinearMap = Dist p)
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Q : TopologicalSpace.Opens Φ.family.centerDomain)
    (W : Set (ComplexModel m)) (hW : IsOpen W)
    (e : Q → OpenPartialHomeomorph ((Fin d → ℝ) × K) (ComplexModel m))
    (ht : ∀ q, (e q).target = W)
    (he : ∀ q, ContDiffOn ℝ 1 (e q).symm (e q).target)
    (hbase : ∀ q, ∀ z ∈ (e q).source, z.1 ∈ Metric.ball 0 Φ.family.radius)
    (hc : ContinuousOn (fun z : Q × ComplexModel m ↦ (e z.1).symm z.2) (univ ×ˢ W))
    (hd : ContinuousOn (fun z : Q × ComplexModel m ↦ fderiv ℝ (e z.1).symm z.2) (univ ×ˢ W))
    (q₀ : Q) (hpframe : q₀.val.val ∈ frame.baseSet)
    (hpchart : q₀.val.val ∈ (extChartAt (realModel m) Φ.family.receivingAnchor).source)
    (hptarget : extChartAt (realModel m) Φ.family.receivingAnchor q₀.val.val ∈ W)
    (hinv₀ : (e q₀).symm (extChartAt (realModel m) Φ.family.receivingAnchor q₀.val.val) = 0)
    (hderiv₀ : HasFDerivAt (fun w ↦ H.coordinate q₀.val ((e q₀).symm w).1)
      (plaqueMetricProjection
        (originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate q₀.val 0))
        (fderiv ℝ (H.coordinate q₀.val) 0))
      (extChartAt (realModel m) Φ.family.receivingAnchor q₀.val.val)) :
    let ca := extChartAt (realModel m) Φ.family.receivingAnchor
    let tr := trivializationAt (ComplexModel m) (TangentSpace (realModel m))
      Φ.family.receivingAnchor
    let τ : Q → M → M := fun q x ↦ (Φ.family.plaque q.val).param ((e q).symm (ca x)).1
    let V : Q → M → ComplexModel m →L[ℝ] ComplexModel m := fun q x ↦
      fderiv ℝ (fun w ↦ H.coordinate q.val ((e q).symm w).1) (ca x)
    ∃ A : Set M, IsOpen A ∧ q₀.val.val ∈ A ∧ A ⊆ ca.source ∩ ca ⁻¹' W ∧
      ∀ q : Q, q.val.val ∈ A → ∀ x ∈ A,
        ∃ (hxf : x ∈ frame.baseSet) (hyf : τ q x ∈ frame.baseSet)
          (hx : x ∈ tr.baseSet) (hy : τ q x ∈ tr.baseSet)
          (C : ComplexModel s →L[ℝ] ComplexModel s),
          0 < C.det ∧ ∀ v,
            complexTangentToReal m (τ q x)
              (((frame.linearEquivAt ℂ (τ q x) hyf).symm (C v)).val) =
            (tr.continuousLinearEquivAt ℝ (τ q x) hy).symm
              (V q x ((tr.continuousLinearEquivAt ℝ x hx)
                (complexTangentToReal m x
                  (((frame.linearEquivAt ℂ x hxf).symm v).val)))) := by
  obtain ⟨A,hA,hp,hsub,hcontrol⟩ := native_physical_projection_open_control_g18 g S s frame
    H hS Q W hW e ht he hbase hc hd q₀ hpframe hpchart hptarget hinv₀ hderiv₀ 1 zero_lt_one
  refine ⟨A,hA,hp,hsub,?_⟩
  intro q hq x hx
  obtain ⟨hxf,hyf,hx,hy,C,hpos,hcoeff,_⟩ := hcontrol q hq x hx
  exact ⟨hxf,hyf,hx,hy,C,hpos,hcoeff⟩

end HolomorphicAnosov.HPS
end



namespace HolomorphicAnosov
/-- Positive determinant in the genuine complex tangent frame gives the exact canonical orientation inequality in the intrinsic preferred complex charts. All frame changes are obtained from the actual immersion derivative and its range. -/
theorem intrinsic_orientation_of_physical_coefficient_g18
    {n d : ℕ} {X Y M : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (incX : X → M) (incY : Y → M) (p : X → Y) (x : X)
    (hx : MDifferentiableAt (complexModel n) (complexModel d) incX x)
    (hy : MDifferentiableAt (complexModel n) (complexModel d) incY (p x))
    (hp : MDifferentiableAt (realModel n) (realModel n) p x)
    (hxi : Function.Injective (mfderiv (complexModel n) (complexModel d) incX x))
    (hyi : Function.Injective (mfderiv (complexModel n) (complexModel d) incY (p x)))
    (SX : Submodule ℂ (TangentSpace (complexModel d) (incX x)))
    (SY : Submodule ℂ (TangentSpace (complexModel d) (incY (p x))))
    (hXS : (mfderiv (complexModel n) (complexModel d) incX x).range = SX)
    (hYS : (mfderiv (complexModel n) (complexModel d) incY (p x)).range = SY)
    (frameX : SX ≃ₗ[ℂ] ComplexModel n) (frameY : SY ≃ₗ[ℂ] ComplexModel n)
    (A : TangentSpace (realModel d) (incX x) →L[ℝ]
      TangentSpace (realModel d) (incY (p x)))
    (C : ComplexModel n →L[ℝ] ComplexModel n) (hCpos : 0 < C.det)
    (hC : ∀ v, complexTangentToReal d (incY (p x)) (frameY.symm (C v)).val =
      A (complexTangentToReal d (incX x) (frameX.symm v).val))
    (hA : ∀ v, A (mfderiv (realModel n) (realModel d) incX x v) =
      mfderiv (realModel n) (realModel d) incY (p x)
        (mfderiv (realModel n) (realModel n) p x v)) :
    0 < LinearMap.det
      (fderiv ℝ ((chartAt (ComplexModel n) (p x)) ∘ p ∘
        (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x)).toLinearMap := by
  obtain ⟨s,hs⟩ := intrinsic_complex_frame_equiv_g18 incX x hxi SX hXS
    frameX.toContinuousLinearEquiv
  obtain ⟨t,ht⟩ := intrinsic_complex_frame_equiv_g18 incY (p x) hyi SY hYS
    frameY.toContinuousLinearEquiv
  have hsq := intrinsic_complex_frame_derivative_square_g18 incX incY p x hx hy hp SX SY
    frameX.toContinuousLinearEquiv frameY.toContinuousLinearEquiv s t hs ht A C hC hA
  exact real_det_pos_of_complex_frame_square_g18 _ C s t hsq hCpos

end HolomorphicAnosov


namespace HolomorphicAnosov
open scoped Manifold ContDiff _root_.Topology
attribute [local instance] complex_isManifold_real
universe u
/-- A native complex upgrade's actual complex inclusion image is the given complex subspace whenever their realifications are the original native tangent range. Compatibility is obtained directly from both stored atlas directions. -/
theorem native_upgrade_complex_range_g18
    {r n d : ℕ} {X M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [IsManifold 𝓘(ℝ,Fin r → ℝ) ∞ X]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : X → M) (U : NativeLeafComplexUpgrade (d := d) (r := r) n inc) (x : X)
    (hreal : MDifferentiableAt 𝓘(ℝ,Fin r → ℝ) (realModel d) inc x)
    (S : Submodule ℂ (TangentSpace (complexModel d) (inc x)))
    (hS : (S.restrictScalars ℝ).map (complexTangentToReal d (inc x)).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) inc x).range) :
    letI := U.charts
    (mfderiv (complexModel n) (complexModel d) inc x).range = S := by
  let := U.charts
  let := U.complex_manifold
  have hcompat := Ghys.native_complex_upgrade_identity_mdifferentiable U
  apply complex_range_eq_of_realification_g18
  exact (complexDerivative_range_of_compatible_real_charts
    (hcompat.1.mdifferentiableAt (by simp)) (hcompat.2.mdifferentiableAt (by simp))
    (U.inclusion_holomorphic.mdifferentiableAt (by simp)) hreal).trans hS.symm

/-- Specialization of canonical orientation transfer to two genuine native complex leaf upgrades. The original real tangent ranges and the true complex subbundle realifications determine the complex tangent frames without another rank or atlas hypothesis. -/
theorem native_upgrade_orientation_g18
    {rx ry n d : ℕ} {X Y M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin rx → ℝ) X]
    [IsManifold 𝓘(ℝ,Fin rx → ℝ) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (Fin ry → ℝ) Y]
    [IsManifold 𝓘(ℝ,Fin ry → ℝ) ∞ Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (incX : X → M) (incY : Y → M)
    (UX : NativeLeafComplexUpgrade (d := d) (r := rx) n incX)
    (UY : NativeLeafComplexUpgrade (d := d) (r := ry) n incY)
    (p : X → Y) (x : X)
    (hx : MDifferentiableAt 𝓘(ℝ,Fin rx → ℝ) (realModel d) incX x)
    (hy : MDifferentiableAt 𝓘(ℝ,Fin ry → ℝ) (realModel d) incY (p x))
    (SX : Submodule ℂ (TangentSpace (complexModel d) (incX x)))
    (SY : Submodule ℂ (TangentSpace (complexModel d) (incY (p x))))
    (hXS : (SX.restrictScalars ℝ).map (complexTangentToReal d (incX x)).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ,Fin rx → ℝ) (realModel d) incX x).range)
    (hYS : (SY.restrictScalars ℝ).map (complexTangentToReal d (incY (p x))).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ,Fin ry → ℝ) (realModel d) incY (p x)).range)
    (frameX : SX ≃ₗ[ℂ] ComplexModel n) (frameY : SY ≃ₗ[ℂ] ComplexModel n)
    (A : TangentSpace (realModel d) (incX x) →L[ℝ]
      TangentSpace (realModel d) (incY (p x)))
    (C : ComplexModel n →L[ℝ] ComplexModel n) (hCpos : 0 < C.det)
    (hC : ∀ v, complexTangentToReal d (incY (p x)) (frameY.symm (C v)).val =
      A (complexTangentToReal d (incX x) (frameX.symm v).val)) :
    letI := UX.charts
    letI := UY.charts
    ∀ _hp : MDifferentiableAt (realModel n) (realModel n) p x,
    (∀ v, A (mfderiv (realModel n) (realModel d) incX x v) =
      mfderiv (realModel n) (realModel d) incY (p x)
        (mfderiv (realModel n) (realModel n) p x v)) →
    0 < LinearMap.det
      (fderiv ℝ ((chartAt (ComplexModel n) (p x)) ∘ p ∘
        (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x)).toLinearMap := by
  let := UX.charts
  let := UY.charts
  intro hp hA
  exact intrinsic_orientation_of_physical_coefficient_g18 incX incY p x
    (UX.inclusion_holomorphic.mdifferentiableAt (by simp))
    (UY.inclusion_holomorphic.mdifferentiableAt (by simp)) hp
    ((UX.inclusion_immersion x).mfderiv_injective (by simp))
    ((UY.inclusion_immersion (p x)).mfderiv_injective (by simp)) SX SY
    (native_upgrade_complex_range_g18 incX UX x hx SX hXS)
    (native_upgrade_complex_range_g18 incY UY (p x) hy SY hYS)
    frameX frameY A C hCpos hC hA

/-- Specialization of canonical orientation transfer to two genuine native complex leaf upgrades. The original real tangent ranges and the true complex subbundle realifications determine the complex tangent frames without another rank or atlas hypothesis. -/
theorem native_upgrade_orientation_from_original_g18
    {rx ry n d : ℕ} {X Y M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin rx → ℝ) X]
    [IsManifold 𝓘(ℝ,Fin rx → ℝ) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (Fin ry → ℝ) Y]
    [IsManifold 𝓘(ℝ,Fin ry → ℝ) ∞ Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (incX : X → M) (incY : Y → M)
    (UX : NativeLeafComplexUpgrade (d := d) (r := rx) n incX)
    (UY : NativeLeafComplexUpgrade (d := d) (r := ry) n incY)
    (p : X → Y) (x : X)
    (hp : MDifferentiableAt 𝓘(ℝ,Fin rx → ℝ) 𝓘(ℝ,Fin ry → ℝ) p x)
    (hx : MDifferentiableAt 𝓘(ℝ,Fin rx → ℝ) (realModel d) incX x)
    (hy : MDifferentiableAt 𝓘(ℝ,Fin ry → ℝ) (realModel d) incY (p x))
    (SX : Submodule ℂ (TangentSpace (complexModel d) (incX x)))
    (SY : Submodule ℂ (TangentSpace (complexModel d) (incY (p x))))
    (hXS : (SX.restrictScalars ℝ).map (complexTangentToReal d (incX x)).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ,Fin rx → ℝ) (realModel d) incX x).range)
    (hYS : (SY.restrictScalars ℝ).map (complexTangentToReal d (incY (p x))).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ,Fin ry → ℝ) (realModel d) incY (p x)).range)
    (frameX : SX ≃ₗ[ℂ] ComplexModel n) (frameY : SY ≃ₗ[ℂ] ComplexModel n)
    (A : TangentSpace (realModel d) (incX x) →L[ℝ]
      TangentSpace (realModel d) (incY (p x)))
    (C : ComplexModel n →L[ℝ] ComplexModel n) (hCpos : 0 < C.det)
    (hC : ∀ v, complexTangentToReal d (incY (p x)) (frameY.symm (C v)).val =
      A (complexTangentToReal d (incX x) (frameX.symm v).val))
    (hA : ∀ v, A (mfderiv 𝓘(ℝ,Fin rx → ℝ) (realModel d) incX x v) =
      mfderiv 𝓘(ℝ,Fin ry → ℝ) (realModel d) incY (p x)
        (mfderiv 𝓘(ℝ,Fin rx → ℝ) 𝓘(ℝ,Fin ry → ℝ) p x v)) :
    letI := UX.charts
    letI := UY.charts
    0 < LinearMap.det
      (fderiv ℝ ((chartAt (ComplexModel n) (p x)) ∘ p ∘
        (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x)).toLinearMap := by
  let := UX.charts
  let := UY.charts
  let := UX.complex_manifold
  let := UY.complex_manifold
  have hcx := Ghys.native_complex_upgrade_identity_mdifferentiable UX
  have hcy := Ghys.native_complex_upgrade_identity_mdifferentiable UY
  have hbackX : MDifferentiableAt (realModel n) 𝓘(ℝ,Fin rx → ℝ) (id : X → X) x :=
    hcx.2.mdifferentiableAt (by simp)
  have hbackY : MDifferentiableAt (realModel n) 𝓘(ℝ,Fin ry → ℝ) (id : Y → Y) (p x) :=
    hcy.2.mdifferentiableAt (by simp)
  have hforwardY : MDifferentiableAt 𝓘(ℝ,Fin ry → ℝ) (realModel n) (id : Y → Y) (p x) :=
    hcy.1.mdifferentiableAt (by simp)
  have hp' : MDifferentiableAt (realModel n) (realModel n) p x := by
    simpa only [Function.comp_id,Function.id_comp] using
      hforwardY.comp x (hp.comp x hbackX)
  apply native_upgrade_orientation_g18 incX incY UX UY p x hx hy SX SY hXS hYS
    frameX frameY A C hCpos hC hp'
  intro v
  have hincX := mfderiv_comp (I := realModel n) (I' := 𝓘(ℝ,Fin rx → ℝ))
    (I'' := realModel d) x hx hbackX
  simp only [Function.comp_id,id_eq] at hincX
  rw [hincX,ContinuousLinearMap.comp_apply,hA]
  have hleft := mfderiv_comp (I := realModel n) (I' := 𝓘(ℝ,Fin rx → ℝ))
    (I'' := 𝓘(ℝ,Fin ry → ℝ)) x hp hbackX
  have hright := mfderiv_comp (I := realModel n) (I' := realModel n)
    (I'' := 𝓘(ℝ,Fin ry → ℝ)) x hbackY hp'
  simp only [Function.comp_id,id_eq] at hleft
  simp only [Function.id_comp,id_eq] at hright
  have hincY := mfderiv_comp (I := realModel n) (I' := 𝓘(ℝ,Fin ry → ℝ))
    (I'' := realModel d) (p x) hy hbackY
  simp only [Function.comp_id,id_eq] at hincY
  rw [hincY,ContinuousLinearMap.comp_apply]
  apply congrArg (mfderiv 𝓘(ℝ,Fin ry → ℝ) (realModel d) incY (p x))
  exact congrArg (fun D ↦ D v) (hleft.symm.trans hright)

end HolomorphicAnosov





/-! This section provides reusable local inverse-function constructions for manifold maps. -/

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07ManifoldInverseFunction

noncomputable section

theorem euclidean_inverse_one_g18
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {S : Set E} (hS : IsOpen S) {a : E} (ha : a ∈ S)
    (hg : ContDiffOn ℝ 1 g S) (e : E ≃L[ℝ] F)
    (he : HasFDerivAt g e.toContinuousLinearMap a) :
    ∃ p : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F 1,
      a ∈ p.source ∧ p.source ⊆ S ∧ (p : E → F) = g := by
  have hga := hg.contDiffAt (hS.mem_nhds ha)
  let p := hga.toOpenPartialHomeomorph g he (by simp)
  have hd := (hga.continuousAt_fderiv (by simp))
  have hi : (fderiv ℝ g a).IsInvertible := by
    rw [he.fderiv]
    exact ⟨e, rfl⟩
  obtain ⟨R, hR, hRo, haR⟩ := mem_nhds_iff.mp (hd hi.eventually_nhds)
  let q := p.restr (S ∩ R)
  have hqo : q.source = p.source ∩ (S ∩ R) := p.restr_source' _ (hS.inter hRo)
  have hqg : (q : E → F) = g := rfl
  have hqS : q.source ⊆ S := by rw [hqo]; exact fun _ h ↦ h.2.1
  have hqsm : ContDiffOn ℝ 1 q q.source := by rw [hqg]; exact hg.mono hqS
  have hqinv : ContDiffOn ℝ 1 q.symm q.target := by
    intro y hy
    have hx := q.map_target hy
    have hxS := hqS hx
    have hxi : (fderiv ℝ g (q.symm y)).IsInvertible := hR (by
      rw [hqo] at hx
      exact hx.2.2)
    obtain ⟨b, hb⟩ := hxi
    have hder : HasFDerivAt q b.toContinuousLinearMap (q.symm y) := by
      rw [hqg, hb]
      exact (hg.contDiffAt (hS.mem_nhds hxS)).differentiableAt (by simp) |>.hasFDerivAt
    exact (q.contDiffAt_symm hy hder
      (hqsm.contDiffAt (q.open_source.mem_nhds hx))).contDiffWithinAt
  refine ⟨{ toPartialEquiv := q.toPartialEquiv
            open_source := q.open_source
            open_target := q.open_target
            contMDiffOn_toFun := hqsm.contMDiffOn
            contMDiffOn_invFun := hqinv.contMDiffOn }, ?_, hqS, hqg⟩
  rw [hqo]
  exact ⟨hga.mem_toOpenPartialHomeomorph_source he (by simp), ha, haR⟩

end
end HolomorphicAnosov.W07ManifoldInverseFunction

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07ManifoldInverseFunction

noncomputable section

/-- On boundaryless finite-dimensional real manifolds, a smooth map whose actual differential is invertible has a smooth partial inverse through the given point. Its source lies in the prescribed original open smoothness domain and its forward map agrees with the original map. -/
theorem exists_partialDiffeomorph_one_g18
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {K : Type*} [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
    [I.Boundaryless] [J.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    {f : M → N} {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hf : ContMDiffOn I J 1 f U)
    (a : TangentSpace I x ≃L[ℝ] TangentSpace J (f x))
    (ha : mfderiv I J f x = a.toContinuousLinearMap) :
    ∃ p : PartialDiffeomorph I J M N 1,
      x ∈ p.source ∧ p.source ⊆ U ∧ EqOn f p p.source := by
  let A : PartialDiffeomorph I 𝓘(ℝ, E) M E 1 :=
    { toPartialEquiv := extChartAt I x
      open_source := isOpen_extChartAt_source x
      open_target := isOpen_extChartAt_target x
      contMDiffOn_toFun := by simpa only [extChartAt_source] using
        (contMDiffOn_extChartAt (I := I) (x := x) (n := 1))
      contMDiffOn_invFun := contMDiffOn_extChartAt_symm x }
  let B : PartialDiffeomorph J 𝓘(ℝ, F) N F 1 :=
    { toPartialEquiv := extChartAt J (f x)
      open_source := isOpen_extChartAt_source (f x)
      open_target := isOpen_extChartAt_target (f x)
      contMDiffOn_toFun := by simpa only [extChartAt_source] using
        (contMDiffOn_extChartAt (I := J) (x := f x) (n := 1))
      contMDiffOn_invFun := contMDiffOn_extChartAt_symm (f x) }
  let W := U ∩ f ⁻¹' B.source
  have hW : IsOpen W := hf.continuousOn.isOpen_inter_preimage hU B.open_source
  have hxW : x ∈ W := ⟨hx, mem_extChartAt_source (f x)⟩
  let S := A.target ∩ A.symm ⁻¹' W
  have hS : IsOpen S := A.toOpenPartialHomeomorph.symm.isOpen_inter_preimage hW
  have hc : A x ∈ S := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change (extChartAt I x).symm ((extChartAt I x) x) ∈ W
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact hxW
  let g : E → F := B ∘ f ∘ A.symm
  have hAS : MapsTo A.symm S U := fun _ hz ↦ hz.2.1
  have hBf : MapsTo (f ∘ A.symm) S B.source := fun _ hz ↦ hz.2.2
  have hg : ContDiffOn ℝ 1 g S := by
    apply ContMDiffOn.contDiffOn
    exact B.contMDiffOn_toFun.comp
      (hf.comp (A.contMDiffOn_invFun.mono inter_subset_left) hAS) hBf
  have hfx := hf.contMDiffAt (hU.mem_nhds hx)
  let c := (tangentSpaceCastModel I x).symm.trans (a.trans (tangentSpaceCastModel J (f x)))
  have hcder : HasFDerivAt g c.toContinuousLinearMap (A x) := by
    have hder := (hfx.mdifferentiableAt (by simp)).hasMFDerivAt
    rw [ha] at hder
    have hh := hder.2
    rw [I.range_eq_univ] at hh
    exact hh.hasFDerivAt (by simp)
  obtain ⟨P, hxP, hPS, hPg⟩ := euclidean_inverse_one_g18 hS hc hg c hcder
  let Q := (A.trans P).trans B.symm
  refine ⟨Q, ?_, ?_, ?_⟩
  · change (x ∈ A.source ∧ A x ∈ P.source) ∧ P (A x) ∈ B.target
    refine ⟨⟨mem_extChartAt_source x, hxP⟩, ?_⟩
    rw [hPg]
    change (extChartAt J (f x)) (f ((extChartAt I x).symm ((extChartAt I x) x))) ∈
      (extChartAt J (f x)).target
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact mem_extChartAt_target (f x)
  · intro z hz
    change (z ∈ A.source ∧ A z ∈ P.source) ∧ P (A z) ∈ B.target at hz
    have h := (hPS hz.1.2).2.1
    change (extChartAt I x).symm ((extChartAt I x) z) ∈ U at h
    rwa [(extChartAt I x).left_inv hz.1.1] at h
  · intro z hz
    change (z ∈ A.source ∧ A z ∈ P.source) ∧ P (A z) ∈ B.target at hz
    change f z = B.symm (P (A z))
    rw [hPg]
    change f z = (extChartAt J (f x)).symm
      ((extChartAt J (f x)) (f ((extChartAt I x).symm ((extChartAt I x) z))))
    rw [(extChartAt I x).left_inv hz.1.1]
    have h := (hPS hz.1.2).2.2
    change f ((extChartAt I x).symm ((extChartAt I x) z)) ∈ B.source at h
    rw [(extChartAt I x).left_inv hz.1.1] at h
    exact ((extChartAt J (f x)).left_inv h).symm

end
end HolomorphicAnosov.W07ManifoldInverseFunction


namespace HolomorphicAnosov
open Filter
/-- Compatible local C1 inverses glue on an injective open domain to the partial homeomorphism with exactly that source; its inverse remains C1. -/
theorem injective_local_c1_partial_homeomorph_g18
    {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace X] [ChartedSpace E X] [Nonempty X]
    [TopologicalSpace Y] [ChartedSpace F Y]
    (f : X → Y) (O : Set X) (hO : IsOpen O)
    (hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f O) (hinj : InjOn f O)
    (hlocal : ∀ x ∈ O, ∃ p : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) X Y 1,
      x ∈ p.source ∧ p.source ⊆ O ∧ EqOn f p p.source) :
    ∃ q : OpenPartialHomeomorph X Y, q.source = O ∧ (q : X → Y) = f ∧
      ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) 1 q q.source ∧
      ContMDiffOn 𝓘(ℝ,F) 𝓘(ℝ,E) 1 q.symm q.target := by
  have htop : IsLocalHomeomorphOn f O := IsLocalHomeomorphOn.mk f O (by
    intro x hx
    obtain ⟨p,hp,_,he⟩ := hlocal x hx
    exact ⟨p.toOpenPartialHomeomorph,hp,he⟩)
  have hopen : IsOpenMap (O.domRestrict f) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    have hval := hO.isOpenEmbedding_subtypeVal.map_nhds_eq x
    have hfmap := htop.map_nhds_eq x.property
    change 𝓝 (f x.val) ≤ Filter.map (f ∘ Subtype.val) (𝓝 x)
    rw [← Filter.map_map,hval,hfmap]
  let q : OpenPartialHomeomorph X Y := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hinj.toPartialEquiv f O) hf.continuousOn hopen hO
  refine ⟨q,rfl,rfl,hf,?_⟩
  intro y hy
  have hx : q.symm y ∈ O := q.map_target hy
  obtain ⟨p,hxp,hpO,hpeq⟩ := hlocal (q.symm y) hx
  have hyp : y ∈ p.target := by
    have h := p.toOpenPartialHomeomorph.map_source hxp
    change p.toPartialEquiv (q.symm y) ∈ p.target at h
    rw [← hpeq hxp] at h
    exact q.right_inv hy ▸ h
  have heq : q.symm =ᶠ[𝓝 y] p.toPartialEquiv.symm := by
    filter_upwards [q.open_target.mem_nhds hy,p.open_target.mem_nhds hyp] with z hzq hzp
    apply hinj (q.map_target hzq) (hpO (p.toOpenPartialHomeomorph.map_target hzp))
    change q (q.symm z) = f (p.toPartialEquiv.symm z)
    rw [q.right_inv hzq]
    change z = f (p.toOpenPartialHomeomorph.symm z)
    rw [hpeq (p.toOpenPartialHomeomorph.map_target hzp)]
    exact (p.toOpenPartialHomeomorph.right_inv hzp).symm
  exact ((p.contMDiffOn_invFun.contMDiffAt (p.open_target.mem_nhds hyp)).congr_of_eventuallyEq
    heq).contMDiffWithinAt

end HolomorphicAnosov

namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
/-- A nonzero determinant in the preferred complex charts gives an invertible actual real tangent derivative, via the tangent model casts. -/
theorem native_chart_det_invertible_g18
    {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    (f : X → Y) (x : X)
    (hf : MDifferentiableAt (realModel n) (realModel n) f x)
    (hdet : LinearMap.det (fderiv ℝ
      ((chartAt (ComplexModel n) (f x)) ∘ f ∘ (chartAt (ComplexModel n) x).symm)
      (chartAt (ComplexModel n) x x)).toLinearMap ≠ 0) :
    ∃ a : TangentSpace (realModel n) x ≃L[ℝ] TangentSpace (realModel n) (f x),
      mfderiv (realModel n) (realModel n) f x = a.toContinuousLinearMap := by
  let D := fderiv ℝ ((chartAt (ComplexModel n) (f x)) ∘ f ∘
    (chartAt (ComplexModel n) x).symm) (chartAt (ComplexModel n) x x)
  let e := D.toContinuousLinearEquivOfDetNeZero hdet
  let a := (tangentSpaceCastModel (realModel n) x).trans
    (e.trans (tangentSpaceCastModel (realModel n) (f x)).symm)
  refine ⟨a,?_⟩
  rw [hf.mfderiv]
  simp only [realModel,modelWithCornersSelf_coe,Set.range_id,fderivWithin_univ]
  rfl

end HolomorphicAnosov

namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
universe u
/-- On two genuine native complex leaf upgrades, an original-real C1 map with positive preferred complex-chart determinant and injective open domain is the forward map of an open partial homeomorphism with exactly that source. Both it and its inverse are C1 in the ORIGINAL real native atlases. -/
theorem native_positive_injective_c1_partial_homeomorph_g18
    {rx ry n d : ℕ} {X Y M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin rx → ℝ) X]
    [IsManifold 𝓘(ℝ,Fin rx → ℝ) ∞ X] [Nonempty X]
    [TopologicalSpace Y] [ChartedSpace (Fin ry → ℝ) Y]
    [IsManifold 𝓘(ℝ,Fin ry → ℝ) ∞ Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (incX : X → M) (incY : Y → M)
    (UX : NativeLeafComplexUpgrade (d := d) (r := rx) n incX)
    (UY : NativeLeafComplexUpgrade (d := d) (r := ry) n incY)
    (f : X → Y) (O : Set X) (hO : IsOpen O)
    (hf : ContMDiffOn 𝓘(ℝ,Fin rx → ℝ) 𝓘(ℝ,Fin ry → ℝ) 1 f O)
    (hinj : InjOn f O) :
    letI := UX.charts
    letI := UY.charts
    (∀ x ∈ O, 0 < LinearMap.det (fderiv ℝ
      ((chartAt (ComplexModel n) (f x)) ∘ f ∘ (chartAt (ComplexModel n) x).symm)
      (chartAt (ComplexModel n) x x)).toLinearMap) →
    ∃ q : OpenPartialHomeomorph X Y, q.source = O ∧ (q : X → Y) = f ∧
      ContMDiffOn 𝓘(ℝ,Fin rx → ℝ) 𝓘(ℝ,Fin ry → ℝ) 1 q q.source ∧
      ContMDiffOn 𝓘(ℝ,Fin ry → ℝ) 𝓘(ℝ,Fin rx → ℝ) 1 q.symm q.target := by
  let := UX.charts
  let := UY.charts
  let := UX.complex_manifold
  let := UY.complex_manifold
  intro hdet
  have hcx := Ghys.native_complex_upgrade_identity_mdifferentiable UX
  have hcy := Ghys.native_complex_upgrade_identity_mdifferentiable UY
  have hXf := hcx.1.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hXb := hcx.2.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hYf := hcy.1.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hYb := hcy.2.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hfc : ContMDiffOn (realModel n) (realModel n) 1 f O := by
    simpa only [Function.comp_id,Function.id_comp,Set.preimage_id] using
      hYf.comp_contMDiffOn (hf.comp hXb.contMDiffOn (fun _ hx ↦ hx))
  obtain ⟨q,hqO,hqf,hqsm,hqinv⟩ :=
      injective_local_c1_partial_homeomorph_g18 f O hO hfc hinj (by
        intro x hx
        obtain ⟨a,ha⟩ := native_chart_det_invertible_g18 f x
          ((hfc.contMDiffAt (hO.mem_nhds hx)).mdifferentiableAt (by simp))
          (ne_of_gt (hdet x hx))
        exact W07ManifoldInverseFunction.exists_partialDiffeomorph_one_g18 hO hx hfc a ha)
  refine ⟨q,hqO,hqf,hqf ▸ hqO ▸ hf,?_⟩
  simpa only [Function.comp_id,Function.id_comp,Set.preimage_id] using
    hXb.comp_contMDiffOn (hqinv.comp hYf.contMDiffOn (fun _ hx ↦ hx))

end HolomorphicAnosov


noncomputable section
open Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- A holomorphic change of source and receiving coordinates preserves the positive real determinant of a real C1 map. All maps are the coordinate maps of the given complex atlas. -/
theorem positive_in_holomorphic_charts_g18
    {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsManifold (complexModel n) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsManifold (complexModel n) ∞ Y]
    (eX : OpenPartialHomeomorph X (ComplexModel n))
    (eY : OpenPartialHomeomorph Y (ComplexModel n))
    (hX : eX ∈ IsManifold.maximalAtlas (complexModel n) ∞ X)
    (hY : eY ∈ IsManifold.maximalAtlas (complexModel n) ∞ Y)
    (f : X → Y) (x : X) (hx : x ∈ eX.source) (hy : f x ∈ eY.source)
    (hf : ContMDiffAt (realModel n) (realModel n) 1 f x)
    (hdet : 0 < (fderiv ℝ
      ((chartAt (ComplexModel n) (f x)) ∘ f ∘ (chartAt (ComplexModel n) x).symm)
      (chartAt (ComplexModel n) x x)).det) :
    ContDiffAt ℝ 1 (eY ∘ f ∘ eX.symm) (eX x) ∧
      0 < (fderiv ℝ (eY ∘ f ∘ eX.symm) (eX x)).det := by
  let cx := chartAt (ComplexModel n) x
  let cy := chartAt (ComplexModel n) (f x)
  let a := eX.symm.trans cx
  let b := cy.symm.trans eY
  have ha : eX x ∈ a.source := ⟨eX.map_source hx,by
    change eX.symm (eX x) ∈ cx.source
    rw [eX.left_inv hx]
    exact mem_chart_source _ _⟩
  have hb : cy (f x) ∈ b.source := ⟨cy.map_source (mem_chart_source _ _),by
    change cy.symm (cy (f x)) ∈ eY.source
    rw [cy.left_inv (mem_chart_source _ _)]
    exact hy⟩
  have haAtlas : a ∈ IsManifold.maximalAtlas (complexModel n) ∞ (ComplexModel n) := by
    apply a.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_chart (I := complexModel n)).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hX).mono (fun _ hz ↦ hz.1))
        (fun _ hz ↦ hz.2)
    · exact (contMDiffOn_of_mem_maximalAtlas hX).comp
        ((contMDiffOn_chart_symm (I := complexModel n)).mono (fun _ hz ↦ hz.1))
        (fun _ hz ↦ hz.2)
  have hbAtlas : b ∈ IsManifold.maximalAtlas (complexModel n) ∞ (ComplexModel n) := by
    apply b.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hY).comp
        ((contMDiffOn_chart_symm (I := complexModel n)).mono (fun _ hz ↦ hz.1))
        (fun _ hz ↦ hz.2)
    · exact (contMDiffOn_chart (I := complexModel n)).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hY).mono (fun _ hz ↦ hz.1))
        (fun _ hz ↦ hz.2)
  have haSmooth : ContDiffAt ℝ 1 a (eX x) :=
    ((contMDiffAt_iff_contDiffAt.mp (contMDiffAt_of_mem_maximalAtlas haAtlas ha)).restrict_scalars ℝ).of_le (by simp)
  have hbSmooth : ContDiffAt ℝ 1 b (cy (f x)) :=
    ((contMDiffAt_iff_contDiffAt.mp (contMDiffAt_of_mem_maximalAtlas hbAtlas hb)).restrict_scalars ℝ).of_le (by simp)
  have haPos := Ghys.holomorphic_coordinate_det_pos a
    (contMDiffOn_of_mem_maximalAtlas haAtlas) (contMDiffOn_symm_of_mem_maximalAtlas haAtlas) ha
  have hbPos := Ghys.holomorphic_coordinate_det_pos b
    (contMDiffOn_of_mem_maximalAtlas hbAtlas) (contMDiffOn_symm_of_mem_maximalAtlas hbAtlas) hb
  let R : ComplexModel n → ComplexModel n := cy ∘ f ∘ cx.symm
  have hR : ContDiffAt ℝ 1 R (cx x) := by
    have hc : ContMDiffAt (realModel n) (realModel n) 1 cy (f x) :=
      (contMDiffOn_chart (I := realModel n)).contMDiffAt
        (cy.open_source.mem_nhds (mem_chart_source _ _))
    have hci : ContMDiffAt (realModel n) (realModel n) 1 cx.symm (cx x) :=
      (contMDiffOn_chart_symm (I := realModel n)).contMDiffAt
        (cx.open_target.mem_nhds (cx.map_source (mem_chart_source _ _)))
    have hff : ContMDiffAt (realModel n) (realModel n) 1 f (cx.symm (cx x)) := by
      rwa [cx.left_inv (mem_chart_source _ _)]
    have hh := (hc.comp x hf)
    have hh' : ContMDiffAt (realModel n) (realModel n) 1 (cy ∘ f) (cx.symm (cx x)) := by
      rwa [cx.left_inv (mem_chart_source _ _)]
    exact contMDiffAt_iff_contDiffAt.mp (hh'.comp (cx x) hci)
  have hax : a (eX x) = cx x := by change cx (eX.symm (eX x)) = _; rw [eX.left_inv hx]
  have hRx : R (cx x) = cy (f x) := by change cy (f (cx.symm (cx x))) = _; rw [cx.left_inv (mem_chart_source _ _)]
  have hRa : ContDiffAt ℝ 1 R (a (eX x)) := by simpa only [hax] using hR
  have hbRa : ContDiffAt ℝ 1 b ((R ∘ a) (eX x)) := by
    simpa only [Function.comp_apply,hax,hRx] using hbSmooth
  have hcomp : ContDiffAt ℝ 1 (b ∘ R ∘ a) (eX x) :=
    hbRa.comp (eX x) (hRa.comp (eX x) haSmooth)
  have heq : (eY ∘ f ∘ eX.symm) =ᶠ[𝓝 (eX x)] (b ∘ R ∘ a) := by
    have hnearX : ∀ᶠ z in 𝓝 (eX x), eX.symm z ∈ cx.source :=
      (eX.continuousAt_symm (eX.map_source hx)) (cx.open_source.mem_nhds (by
        simpa only [eX.left_inv hx] using mem_chart_source (ComplexModel n) x))
    have hnearY : ∀ᶠ z in 𝓝 (eX x), f (eX.symm z) ∈ cy.source :=
      ((show ContinuousAt f (eX.symm (eX x)) by simpa only [eX.left_inv hx] using hf.continuousAt).comp
        (eX.continuousAt_symm (eX.map_source hx)))
        (cy.open_source.mem_nhds (by
          change f (eX.symm (eX x)) ∈ cy.source
          rw [eX.left_inv hx]
          exact mem_chart_source _ _))
    filter_upwards [hnearX,hnearY] with z hzX hzY
    change eY (f (eX.symm z)) = eY (cy.symm (cy (f (cx.symm (cx (eX.symm z))))))
    rw [cx.left_inv hzX,cy.left_inv hzY]
  refine ⟨hcomp.congr_of_eventuallyEq heq,?_⟩
  rw [heq.fderiv_eq]
  rw [fderiv_comp _ (hbRa.differentiableAt (by simp))
    ((hRa.comp (eX x) haSmooth).differentiableAt (by simp)),
    fderiv_comp _ (hRa.differentiableAt (by simp)) (haSmooth.differentiableAt (by simp))]
  change 0 < LinearMap.det ((fderiv ℝ b ((R ∘ a) (eX x))).toLinearMap.comp
    ((fderiv ℝ R (a (eX x))).toLinearMap.comp (fderiv ℝ a (eX x)).toLinearMap))
  rw [LinearMap.det_comp,LinearMap.det_comp]
  simp only [Function.comp_apply,hax,hRx]
  exact mul_pos hbPos (mul_pos hdet haPos)
end HolomorphicAnosov

namespace HolomorphicAnosov
/-- Pull back an actual holomorphic chart along a holomorphic homeomorphism. -/
theorem holomorphic_pullback_chart_g18
    {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsManifold (complexModel n) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsManifold (complexModel n) ∞ Y]
    (e : X ≃ₜ Y)
    (he : ContMDiff (complexModel n) (complexModel n) ∞ e)
    (hi : ContMDiff (complexModel n) (complexModel n) ∞ e.symm)
    (c : OpenPartialHomeomorph X (ComplexModel n))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel n) ∞ X) :
    e.symm.toOpenPartialHomeomorph.trans c ∈
      IsManifold.maximalAtlas (complexModel n) ∞ Y := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas hc).comp hi.contMDiffOn (fun _ hz ↦ hz.2)
  · exact he.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hc).mono (fun _ hz ↦ hz.1))

/-- The preceding coordinate transport holds on the whole specified guarded coordinate domain, so it applies to the complete buffered open disk. -/
theorem positive_in_holomorphic_charts_on_g18
    {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsManifold (complexModel n) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsManifold (complexModel n) ∞ Y]
    (eX : OpenPartialHomeomorph X (ComplexModel n))
    (eY : OpenPartialHomeomorph Y (ComplexModel n))
    (hX : eX ∈ IsManifold.maximalAtlas (complexModel n) ∞ X)
    (hY : eY ∈ IsManifold.maximalAtlas (complexModel n) ∞ Y)
    (f : X → Y) (D : Set (ComplexModel n))
    (hguard : ∀ z ∈ D, z ∈ eX.target ∧ f (eX.symm z) ∈ eY.source)
    (hf : ∀ z ∈ D, ContMDiffAt (realModel n) (realModel n) 1 f (eX.symm z))
    (hdet : ∀ z ∈ D, 0 < (fderiv ℝ
      ((chartAt (ComplexModel n) (f (eX.symm z))) ∘ f ∘
        (chartAt (ComplexModel n) (eX.symm z)).symm)
      (chartAt (ComplexModel n) (eX.symm z) (eX.symm z))).det) :
    ContDiffOn ℝ 1 (eY ∘ f ∘ eX.symm) D ∧
      ∀ z ∈ D, 0 < (fderiv ℝ (eY ∘ f ∘ eX.symm) z).det := by
  have hpoint (z) (hz : z ∈ D) := positive_in_holomorphic_charts_g18
    eX eY hX hY f (eX.symm z) (eX.map_target (hguard z hz).1) (hguard z hz).2
    (hf z hz) (hdet z hz)
  constructor
  · intro z hz
    have hh := (hpoint z hz).1
    rw [eX.right_inv (hguard z hz).1] at hh
    exact hh.contDiffWithinAt
  · intro z hz
    simpa only [eX.right_inv (hguard z hz).1] using (hpoint z hz).2
end HolomorphicAnosov

namespace HolomorphicAnosov
universe u
/-- A native upgrade transports an original-real C1 map to its realified complex atlases at the same point,. -/
theorem native_upgrade_real_c1_at_g18
    {rx ry n d : ℕ} {X Y M : Type u}
    [TopologicalSpace X] [ChartedSpace (Fin rx → ℝ) X]
    [IsManifold 𝓘(ℝ,Fin rx → ℝ) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (Fin ry → ℝ) Y]
    [IsManifold 𝓘(ℝ,Fin ry → ℝ) ∞ Y]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (incX : X → M) (incY : Y → M)
    (UX : NativeLeafComplexUpgrade (d := d) (r := rx) n incX)
    (UY : NativeLeafComplexUpgrade (d := d) (r := ry) n incY)
    (f : X → Y) (x : X)
    (hf : ContMDiffAt 𝓘(ℝ,Fin rx → ℝ) 𝓘(ℝ,Fin ry → ℝ) 1 f x) :
    letI := UX.charts
    letI := UY.charts
    ContMDiffAt (realModel n) (realModel n) 1 f x := by
  let := UX.charts
  let := UY.charts
  have hcx := Ghys.native_complex_upgrade_identity_mdifferentiable UX
  have hcy := Ghys.native_complex_upgrade_identity_mdifferentiable UY
  have hXb := hcx.2.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hYf := hcy.1.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  simpa only [Function.comp_id,Function.id_comp] using
    (hYf (f x)).comp x (hf.comp x (hXb x))
end HolomorphicAnosov

namespace HolomorphicAnosov
/-- The transported charts produce exactly the pulled comparison coordinate map, with the entire original source-chart target unchanged. -/
theorem holomorphic_pullback_chart_formula_g18
    {n : ℕ} {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (iX : X ≃ₜ X') (iY : Y ≃ₜ Y')
    (cX : OpenPartialHomeomorph X (ComplexModel n))
    (cY : OpenPartialHomeomorph Y (ComplexModel n)) (f : X' → Y') :
    let eX := iX.symm.toOpenPartialHomeomorph.trans cX
    let eY := iY.symm.toOpenPartialHomeomorph.trans cY
    eX.target = cX.target ∧
      (eY ∘ f ∘ eX.symm) = cY ∘ iY.symm ∘ f ∘ iX ∘ cX.symm := by
  constructor
  · simp only [OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target,Set.preimage_univ,Set.inter_univ]
  · rfl
end HolomorphicAnosov

