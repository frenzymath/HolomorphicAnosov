import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

















open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

universe u
noncomputable section

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
variable [IsManifold (complexModel d) ∞ X]

attribute [local instance] complex_isManifold_real





def hermitianBoundsIterate (f : Biholomorph d d X X) (n : ℕ) : Biholomorph d d X X :=
  { toEquiv :=
      { toFun := (f : X → X)^[n]
        invFun := (f.symm : X → X)^[n]
        left_inv := f.left_inv.iterate n
        right_inv := f.right_inv.iterate n }
    contMDiff_toFun := f.contMDiff_toFun.iterate n
    contMDiff_invFun := f.symm.contMDiff_toFun.iterate n }





def hermitianBoundsDerivative (f : Biholomorph d d X X) (n : ℕ) (x : X) :
    TangentSpace (complexModel d) x ≃L[ℂ]
      TangentSpace (complexModel d) (hermitianBoundsIterate f n x) :=
  (hermitianBoundsIterate f n).mfderivToContinuousLinearEquiv (by simp) x





def hermitianBoundsNorm (h : HermitianTangentMetricCore d X) (x : X)
    (v : TangentSpace (complexModel d) x) : ℝ :=
  Real.sqrt ((h x).inner v v).re





def fibreNormOperator {V W : Type*} [AddCommGroup V] [Module ℂ V]
    (p : V → ℝ) (q : W → ℝ) (P : Submodule ℂ V) (L : V → W) : ℝ :=
  sSup {a : ℝ | ∃ v : V, v ∈ P ∧ p v ≤ 1 ∧ a = q (L v)}




def fibreNormConorm {V W : Type*} [AddCommGroup V] [Module ℂ V]
    (p : V → ℝ) (q : W → ℝ) (P : Submodule ℂ V) (L : V → W) : ℝ :=
  sInf {a : ℝ | ∃ v : V, v ∈ P ∧ p v = 1 ∧ a = q (L v)}


end
end HolomorphicAnosov











noncomputable section
namespace HolomorphicAnosov.HermitianFibreAlgebra
open scoped ContDiff
universe u

section Core
variable {E : Type u} [AddCommGroup E] [Module ℂ E]


def coreLength (h : InnerProductSpace.Core ℂ E) (v : E) : ℝ :=
  Real.sqrt (h.inner v v).re



def coreComplexSeminorm (h : InnerProductSpace.Core ℂ E) : Seminorm ℂ E :=
  letI : InnerProductSpace.Core ℂ E := h
  letI : Norm E := InnerProductSpace.Core.toNorm (𝕜 := ℂ)
  Seminorm.of (coreLength h)
    (h.toNormedSpaceCore.norm_triangle) (h.toNormedSpaceCore.norm_smul)


theorem coreComplexSeminorm_apply (h : InnerProductSpace.Core ℂ E) (v : E) :
    coreComplexSeminorm h v = coreLength h v := rfl


theorem coreLength_nonneg (h : InnerProductSpace.Core ℂ E) (v : E) :
    0 ≤ coreLength h v := Real.sqrt_nonneg _


theorem coreLength_eq_zero_iff (h : InnerProductSpace.Core ℂ E) (v : E) :
    coreLength h v = 0 ↔ v = 0 := by
  let : InnerProductSpace.Core ℂ E := h
  let : Norm E := InnerProductSpace.Core.toNorm (𝕜 := ℂ)
  exact h.toNormedSpaceCore.norm_eq_zero_iff v


theorem coreLength_pos (h : InnerProductSpace.Core ℂ E) {v : E} (hv : v ≠ 0) :
    0 < coreLength h v := by
  apply lt_of_le_of_ne (coreLength_nonneg h v)
  simpa only [ne_eq, eq_comm] using (coreLength_eq_zero_iff h v).not.mpr hv


theorem coreLength_zero (h : InnerProductSpace.Core ℂ E) : coreLength h 0 = 0 :=
  (coreLength_eq_zero_iff h 0).mpr rfl


theorem coreLength_complex_smul (h : InnerProductSpace.Core ℂ E) (a : ℂ) (v : E) :
    coreLength h (a • v) = ‖a‖ * coreLength h v :=
  (coreComplexSeminorm h).smul' a v


theorem coreLength_add_le (h : InnerProductSpace.Core ℂ E) (v w : E) :
    coreLength h (v + w) ≤ coreLength h v + coreLength h w :=
  (coreComplexSeminorm h).add_le' v w

variable [SMul ℝ E] [IsScalarTower ℝ ℂ E]


def coreRealSeminorm (h : InnerProductSpace.Core ℂ E) : Seminorm ℝ E :=
  (coreComplexSeminorm h).restrictScalars ℝ


theorem coreRealSeminorm_apply (h : InnerProductSpace.Core ℂ E) (v : E) :
    coreRealSeminorm h v = coreLength h v := rfl


theorem coreLength_real_smul (h : InnerProductSpace.Core ℂ E) (a : ℝ) (v : E) :
    coreLength h (a • v) = |a| * coreLength h v := by
  have hs := (coreRealSeminorm h).smul' a v
  change coreLength h (a • v) = ‖a‖ * coreLength h v at hs
  simpa only [Real.norm_eq_abs] using hs

end Core

section Tangent
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]


def hermitianBoundsRealSeminorm (h : HermitianTangentMetricCore d X) (x : X) :
    Seminorm ℝ (TangentSpace (complexModel d) x) := coreRealSeminorm (h x)


theorem hermitianBoundsRealSeminorm_apply (h : HermitianTangentMetricCore d X) (x : X)
    (v : TangentSpace (complexModel d) x) :
    hermitianBoundsRealSeminorm h x v = hermitianBoundsNorm h x v := rfl


theorem hermitianBoundsRealSeminorm_coe (h : HermitianTangentMetricCore d X) (x : X) :
    (hermitianBoundsRealSeminorm h x : TangentSpace (complexModel d) x → ℝ) =
      hermitianBoundsNorm h x := rfl


theorem hermitianBoundsNorm_fibre_laws (h : HermitianTangentMetricCore d X) (x : X) :
    hermitianBoundsNorm h x 0 = 0 ∧
    (∀ v, 0 ≤ hermitianBoundsNorm h x v) ∧
    (∀ v, hermitianBoundsNorm h x v = 0 ↔ v = 0) ∧
    (∀ v, v ≠ 0 → 0 < hermitianBoundsNorm h x v) ∧
    (∀ (a : ℝ) v, hermitianBoundsNorm h x (a • v) = |a| * hermitianBoundsNorm h x v) ∧
    (∀ (a : ℂ) v, hermitianBoundsNorm h x (a • v) = ‖a‖ * hermitianBoundsNorm h x v) ∧
    (∀ v w, hermitianBoundsNorm h x (v + w) ≤
      hermitianBoundsNorm h x v + hermitianBoundsNorm h x w) :=
  ⟨coreLength_zero (h x), coreLength_nonneg (h x), coreLength_eq_zero_iff (h x),
    fun _ hv ↦ coreLength_pos (h x) hv, coreLength_real_smul (h x),
    coreLength_complex_smul (h x), coreLength_add_le (h x)⟩

end Tangent


end HolomorphicAnosov.HermitianFibreAlgebra










noncomputable section
open scoped ContDiff Topology _root_.Topology
namespace HolomorphicAnosov.NativeSplittingPreparation
universe u

section Original
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  (S U : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
  (hsplit : ∀ x, IsCompl (S x) (U x))



def stableProjection (x : X) :
    TangentSpace (complexModel d) x →L[ℂ] TangentSpace (complexModel d) x :=
  ((S x).projection (U x) (hsplit x)).toContinuousLinearMap


def unstableProjection (x : X) :
    TangentSpace (complexModel d) x →L[ℂ] TangentSpace (complexModel d) x :=
  ((U x).projection (S x) (hsplit x).symm).toContinuousLinearMap


theorem projections_mem (x : X) (v : TangentSpace (complexModel d) x) :
    stableProjection S U hsplit x v ∈ S x ∧
      unstableProjection S U hsplit x v ∈ U x :=
  ⟨Submodule.projection_apply_mem (hsplit x) v,
    Submodule.projection_apply_mem (hsplit x).symm v⟩


theorem projections_add (x : X) (v : TangentSpace (complexModel d) x) :
    stableProjection S U hsplit x v + unstableProjection S U hsplit x v = v :=
  Submodule.projection_add_projection_eq_self (hsplit x) v


theorem projections_summand_laws (x : X) :
    (∀ v, v ∈ S x → stableProjection S U hsplit x v = v) ∧
    (∀ v, v ∈ U x → stableProjection S U hsplit x v = 0) ∧
    (∀ v, v ∈ U x → unstableProjection S U hsplit x v = v) ∧
    (∀ v, v ∈ S x → unstableProjection S U hsplit x v = 0) :=
  ⟨fun _ hv ↦ Submodule.projection_apply_of_mem_left (hsplit x) hv,
    fun _ hv ↦ Submodule.projection_apply_of_mem_right (hsplit x) hv,
    fun _ hv ↦ Submodule.projection_apply_of_mem_left (hsplit x).symm hv,
    fun _ hv ↦ Submodule.projection_apply_of_mem_right (hsplit x).symm hv⟩

end Original

section NativeRealification
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [IsManifold (complexModel d) ∞ X]
attribute [local instance] complex_isManifold_real
variable (S U : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
  (hsplit : ∀ x, IsCompl (S x) (U x))
  (RS RU : ContinuousRealTangentSubbundle (realModel d) X)
  (hS : ∀ x, ((S x).restrictScalars ℝ).map
    (complexTangentToReal d x).toLinearEquiv.toLinearMap = RS.toDistribution x)
  (hU : ∀ x, ((U x).restrictScalars ℝ).map
    (complexTangentToReal d x).toLinearEquiv.toLinearMap = RU.toDistribution x)

include S U hsplit hS hU in


theorem original_real_subbundles_isCompl (x : X) :
    IsCompl (RS.toDistribution x) (RU.toDistribution x) := by
  rw [← hS x, ← hU x]
  apply Submodule.isCompl_map
  exact (Submodule.isCompl_restrictScalars_iff ℝ).mpr (hsplit x)



theorem original_projection_realification (x : X)
    (v : TangentSpace (complexModel d) x) :
    (complexTangentToReal d x) (stableProjection S U hsplit x v) =
      (RS.toDistribution x).projection (RU.toDistribution x)
        (original_real_subbundles_isCompl S U hsplit RS RU hS hU x)
        ((complexTangentToReal d x) v) := by
  let e := complexTangentToReal d x
  let ps := stableProjection S U hsplit x v
  let pu := unstableProjection S U hsplit x v
  have hs : e ps ∈ RS.toDistribution x := by
    rw [← hS x]
    exact ⟨ps, (projections_mem S U hsplit x v).1, rfl⟩
  have hu : e pu ∈ RU.toDistribution x := by
    rw [← hU x]
    exact ⟨pu, (projections_mem S U hsplit x v).2, rfl⟩
  have hsum : e ps + e pu = e v := by
    rw [← map_add]
    exact congrArg e (projections_add S U hsplit x v)
  change e ps = _
  conv_rhs => rw [← hsum]
  rw [map_add, Submodule.projection_apply_of_mem_left _ hs,
    Submodule.projection_apply_of_mem_right _ hu, add_zero]

end NativeRealification

section FixedFrames
variable {B V W : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]





theorem continuous_frame_inverse (e : B → V ≃L[ℝ] W)
    (he : Continuous (fun x ↦ (e x : V →L[ℝ] W))) :
    Continuous (fun x ↦ ((e x).symm : W →L[ℝ] V)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hinv : ContinuousAt (ContinuousLinearMap.inverse : (V →L[ℝ] W) → W →L[ℝ] V)
      (e x : V →L[ℝ] W) :=
    (contDiffAt_map_inverse (n := 0) (e x)).continuousAt
  simpa only [Function.comp_def, ContinuousLinearMap.inverse_equiv] using
    hinv.comp (f := fun y : B ↦ (e y : V →L[ℝ] W)) he.continuousAt


theorem continuous_frame_inverse_apply (e : B → V ≃L[ℝ] W)
    (he : Continuous (fun x ↦ (e x : V →L[ℝ] W))) :
    Continuous (fun z : B × W ↦ (e z.1).symm z.2) :=
  ((continuous_frame_inverse e he).comp continuous_fst).clm_apply continuous_snd

end FixedFrames

section PairedFrames
variable {B Vₛ Vᵤ W : Type*} [TopologicalSpace B]
  [NormedAddCommGroup Vₛ] [NormedSpace ℝ Vₛ] [CompleteSpace Vₛ]
  [NormedAddCommGroup Vᵤ] [NormedSpace ℝ Vᵤ] [CompleteSpace Vᵤ]
  [NormedAddCommGroup W] [NormedSpace ℝ W]



def firstFrameProjection (e : (Vₛ × Vᵤ) ≃L[ℝ] W) (v : W) : W :=
  e ((e.symm v).1, 0)



theorem continuous_firstFrameProjection
    (e : B → (Vₛ × Vᵤ) ≃L[ℝ] W)
    (he : Continuous (fun x ↦ (e x : (Vₛ × Vᵤ) →L[ℝ] W))) :
    Continuous (fun z : B × W ↦ firstFrameProjection (e z.1) z.2) := by
  have hi := continuous_frame_inverse_apply e he
  exact (he.comp continuous_fst).clm_apply (hi.fst.prodMk continuous_const)

omit [CompleteSpace Vₛ] [CompleteSpace Vᵤ] in

theorem frameProjection_add (e : (Vₛ × Vᵤ) ≃L[ℝ] W) (v : W) :
    firstFrameProjection e v + e (0, (e.symm v).2) = v := by
  rw [firstFrameProjection, ← map_add]
  simp

end PairedFrames

section Synthesis
variable {B Vₛ Vᵤ W : Type*} [TopologicalSpace B]
  [NormedAddCommGroup Vₛ] [NormedSpace ℝ Vₛ] [FiniteDimensional ℝ Vₛ]
  [NormedAddCommGroup Vᵤ] [NormedSpace ℝ Vᵤ] [FiniteDimensional ℝ Vᵤ]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]



def pairedFrameEquiv (jₛ : Vₛ →L[ℝ] W) (jᵤ : Vᵤ →L[ℝ] W)
    (hₛ : Function.Injective jₛ) (hᵤ : Function.Injective jᵤ)
    (hc : IsCompl jₛ.toLinearMap.range jᵤ.toLinearMap.range) : (Vₛ × Vᵤ) ≃L[ℝ] W :=
  (((LinearEquiv.ofInjective jₛ.toLinearMap hₛ).prodCongr
      (LinearEquiv.ofInjective jᵤ.toLinearMap hᵤ)).trans
    (Submodule.prodEquivOfIsCompl _ _ hc)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ W] in

theorem pairedFrameEquiv_apply (jₛ : Vₛ →L[ℝ] W) (jᵤ : Vᵤ →L[ℝ] W)
    (hₛ : Function.Injective jₛ) (hᵤ : Function.Injective jᵤ)
    (hc : IsCompl jₛ.toLinearMap.range jᵤ.toLinearMap.range) (v : Vₛ × Vᵤ) :
    pairedFrameEquiv jₛ jᵤ hₛ hᵤ hc v = jₛ v.1 + jᵤ v.2 := rfl

omit [FiniteDimensional ℝ W] in


theorem continuous_pairedFrameEquiv
    (jₛ : B → Vₛ →L[ℝ] W) (jᵤ : B → Vᵤ →L[ℝ] W)
    (hₛ : ∀ x, Function.Injective (jₛ x)) (hᵤ : ∀ x, Function.Injective (jᵤ x))
    (hc : ∀ x, IsCompl (jₛ x).toLinearMap.range (jᵤ x).toLinearMap.range)
    (hscont : Continuous jₛ) (hucont : Continuous jᵤ) :
    Continuous (fun x ↦ (pairedFrameEquiv (jₛ x) (jᵤ x) (hₛ x) (hᵤ x) (hc x) :
      (Vₛ × Vᵤ) →L[ℝ] W)) := by
  apply continuous_clm_apply.mpr
  intro v
  exact (hscont.clm_apply continuous_const).add (hucont.clm_apply continuous_const)

omit [FiniteDimensional ℝ W] in


theorem firstFrameProjection_eq_projection
    (jₛ : Vₛ →L[ℝ] W) (jᵤ : Vᵤ →L[ℝ] W)
    (hₛ : Function.Injective jₛ) (hᵤ : Function.Injective jᵤ)
    (hc : IsCompl jₛ.toLinearMap.range jᵤ.toLinearMap.range) (v : W) :
    firstFrameProjection (pairedFrameEquiv jₛ jᵤ hₛ hᵤ hc) v =
      jₛ.toLinearMap.range.projection jᵤ.toLinearMap.range hc v := by
  let e := pairedFrameEquiv jₛ jᵤ hₛ hᵤ hc
  have hsum : jₛ (e.symm v).1 + jᵤ (e.symm v).2 = v := e.apply_symm_apply v
  have hs : jₛ (e.symm v).1 ∈ jₛ.toLinearMap.range := ⟨_, rfl⟩
  have hu : jᵤ (e.symm v).2 ∈ jᵤ.toLinearMap.range := ⟨_, rfl⟩
  change e ((e.symm v).1, 0) = _
  rw [pairedFrameEquiv_apply]
  simp only [map_zero, add_zero]
  conv_rhs => rw [← hsum]
  rw [map_add, Submodule.projection_apply_of_mem_left hc hs,
    Submodule.projection_apply_of_mem_right hc hu, add_zero]

omit [FiniteDimensional ℝ W] in


theorem continuous_projection_from_frames
    (jₛ : B → Vₛ →L[ℝ] W) (jᵤ : B → Vᵤ →L[ℝ] W)
    (hₛ : ∀ x, Function.Injective (jₛ x)) (hᵤ : ∀ x, Function.Injective (jᵤ x))
    (hc : ∀ x, IsCompl (jₛ x).toLinearMap.range (jᵤ x).toLinearMap.range)
    (hscont : Continuous jₛ) (hucont : Continuous jᵤ) :
    Continuous (fun z : B × W ↦
      (jₛ z.1).toLinearMap.range.projection (jᵤ z.1).toLinearMap.range (hc z.1) z.2) := by
  have h := continuous_firstFrameProjection
    (fun x ↦ pairedFrameEquiv (jₛ x) (jᵤ x) (hₛ x) (hᵤ x) (hc x))
    (continuous_pairedFrameEquiv jₛ jᵤ hₛ hᵤ hc hscont hucont)
  simpa only [firstFrameProjection_eq_projection] using h

end Synthesis

section NativeFrames
open Set Bundle
variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace X]
  (I : ModelWithCorners ℝ E H) [ChartedSpace H X] [IsManifold I ∞ X]

omit [FiniteDimensional ℝ E] in




theorem exists_native_coordinate_frame
    (R : ContinuousRealTangentSubbundle I X) (x : X) :
    ∃ r : ℕ,
    ∃ (O : Set X), IsOpen O ∧ x ∈ O ∧
    ∃ (a : Trivialization E (TotalSpace.proj (F := E) (E := TangentSpace I))),
    a = trivializationAt E (TangentSpace I) x ∧
    ∃ (_ha : a.IsLinear ℝ),
    ∃ (hO : O ⊆ a.baseSet),
    ∃ j : O → (Fin r → ℝ) →L[ℝ] E,
      Continuous j ∧ (∀ y, Function.Injective (j y)) ∧
      ∀ y, (j y).toLinearMap.range =
        (R.toDistribution y.val).map (a.linearEquivAt ℝ y.val (hO y.property)).toLinearMap := by
  obtain ⟨r, hr⟩ := R.locally_trivial x
  let : TopologicalSpace (TotalSpace (Fin r → ℝ)
      (fun y : X ↦ ↥(R.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
  obtain ⟨e, hx, he⟩ := hr
  let := he
  let a := trivializationAt E (TangentSpace I) x
  let O := e.baseSet ∩ a.baseSet
  have hO : O ⊆ a.baseSet := fun _ hy ↦ hy.2
  let j : O → (Fin r → ℝ) →L[ℝ] E := fun y ↦
    (((a.linearEquivAt ℝ y.val y.property.2).toLinearMap.comp
      (R.toDistribution y.val).subtype).comp
      (e.linearEquivAt ℝ y.val y.property.1).symm.toLinearMap).toContinuousLinearMap
  refine ⟨r, O, e.open_baseSet.inter a.open_baseSet,
    ⟨hx, mem_baseSet_trivializationAt E (TangentSpace I) x⟩, a, rfl,
    inferInstance, hO, j, ?_, ?_, ?_⟩
  · apply continuous_clm_apply.mpr
    intro v
    have hframe : Continuous (fun y : O ↦
        (⟨y.val, e.symm y.val v⟩ :
          TotalSpace (Fin r → ℝ) (fun z : X ↦ ↥(R.toDistribution z)))) :=
      e.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun y ↦ ⟨y.property.1, mem_univ _⟩)
    have hincl : Continuous (fun y : O ↦
        (⟨y.val, (e.symm y.val v).val⟩ : TangentBundle I X)) :=
      continuous_induced_dom.comp hframe
    have hcoord := (a.continuousOn.comp_continuous hincl
      (fun y ↦ a.mem_source.mpr y.property.2)).snd
    simpa [j, LinearEquiv.coe_coe] using hcoord
  · intro y
    exact (a.linearEquivAt ℝ y.val y.property.2).injective.comp
      (Subtype.val_injective.comp (e.linearEquivAt ℝ y.val y.property.1).symm.injective)
  · intro y
    change ((((a.linearEquivAt ℝ y.val y.property.2).toLinearMap.comp
      (R.toDistribution y.val).subtype).comp
      (e.linearEquivAt ℝ y.val y.property.1).symm.toLinearMap).range) = _
    simp [LinearMap.range_comp]

omit [FiniteDimensional ℝ E] in



theorem exists_native_paired_coordinate_frames
    (RS RU : ContinuousRealTangentSubbundle I X)
    (hc : ∀ x, IsCompl (RS.toDistribution x) (RU.toDistribution x)) (x : X) :
    ∃ r t : ℕ,
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧
    ∃ (a : Trivialization E (TotalSpace.proj (F := E) (E := TangentSpace I))),
    a = trivializationAt E (TangentSpace I) x ∧
    ∃ (_ha : a.IsLinear ℝ),
    ∃ hO : O ⊆ a.baseSet,
    ∃ (js : O → (Fin r → ℝ) →L[ℝ] E) (ju : O → (Fin t → ℝ) →L[ℝ] E),
      Continuous js ∧ Continuous ju ∧
      (∀ y, Function.Injective (js y)) ∧ (∀ y, Function.Injective (ju y)) ∧
      (∀ y, (js y).toLinearMap.range = (RS.toDistribution y.val).map
        (a.linearEquivAt ℝ y.val (hO y.property)).toLinearMap) ∧
      (∀ y, (ju y).toLinearMap.range = (RU.toDistribution y.val).map
        (a.linearEquivAt ℝ y.val (hO y.property)).toLinearMap) ∧
      ∀ y, IsCompl (js y).toLinearMap.range (ju y).toLinearMap.range := by
  obtain ⟨r, Os, hOs, hxs, a, haeq, ha, hsO, js, hscont, hsinj, hsrange⟩ :=
    exists_native_coordinate_frame I RS x
  obtain ⟨t, Ou, hOu, hxu, b, hbeq, hb, huO, ju, hucont, huinj, hurange⟩ :=
    exists_native_coordinate_frame I RU x
  subst a
  subst b
  let a := trivializationAt E (TangentSpace I) x
  let O := Os ∩ Ou
  let fs : O → Os := fun y ↦ ⟨y.val, y.property.1⟩
  let fu : O → Ou := fun y ↦ ⟨y.val, y.property.2⟩
  have hfs : Continuous fs := continuous_subtype_val.subtype_mk _
  have hfu : Continuous fu := continuous_subtype_val.subtype_mk _
  have hO : O ⊆ a.baseSet := fun _ hy ↦ hsO hy.1
  refine ⟨r, t, O, hOs.inter hOu, ⟨hxs, hxu⟩, a, rfl, inferInstance, hO,
    js ∘ fs, ju ∘ fu, hscont.comp hfs, hucont.comp hfu,
    fun y ↦ hsinj (fs y), fun y ↦ huinj (fu y), ?_, ?_, ?_⟩
  · intro y
    exact hsrange (fs y)
  · intro y
    exact hurange (fu y)
  · intro y
    dsimp only [Function.comp_apply]
    rw [hsrange (fs y), hurange (fu y)]
    exact Submodule.isCompl_map (a.linearEquivAt ℝ y.val (hO y.property)) (hc y.val)


theorem projection_map_apply {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (p q : Submodule ℝ V) (hc : IsCompl p q)
    (e : V ≃ₗ[ℝ] W) (v : V) :
    (p.map e.toLinearMap).projection (q.map e.toLinearMap)
      (Submodule.isCompl_map e hc) (e v) = e (p.projection q hc v) := by
  have hs : e (p.projection q hc v) ∈ p.map e.toLinearMap :=
    ⟨_, Submodule.projection_apply_mem hc v, rfl⟩
  have hu : e (q.projection p hc.symm v) ∈ q.map e.toLinearMap :=
    ⟨_, Submodule.projection_apply_mem hc.symm v, rfl⟩
  have hsum : e (p.projection q hc v) + e (q.projection p hc.symm v) = e v := by
    rw [← map_add, Submodule.projection_add_projection_eq_self]
  rw [← hsum, map_add, Submodule.projection_apply_of_mem_left _ hs,
    Submodule.projection_apply_of_mem_right _ hu, add_zero]

omit [FiniteDimensional ℝ E] in



theorem exists_continuous_native_projection
    (RS RU : ContinuousRealTangentSubbundle I X)
    (hc : ∀ x, IsCompl (RS.toDistribution x) (RU.toDistribution x)) (x : X) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧
      Continuous (fun z : {z : TangentBundle I X // z.proj ∈ O} ↦
        (⟨z.val.proj, (RS.toDistribution z.val.proj).projection
          (RU.toDistribution z.val.proj) (hc z.val.proj) z.val.snd⟩ : TangentBundle I X)) := by
  obtain ⟨r, t, O, hOopen, hx, a, haeq, ha, hO, js, ju,
    hscont, hucont, hsinj, huinj, hsrange, hurange, hcompl⟩ :=
    exists_native_paired_coordinate_frames I RS RU hc x
  let := ha
  let Z := {z : TangentBundle I X // z.proj ∈ O}
  have hbase : Continuous (fun z : Z ↦ z.val.proj) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have hcoord : Continuous (fun z : Z ↦ (a z.val).2) :=
    (a.continuousOn.comp_continuous continuous_subtype_val
      (fun z ↦ a.mem_source.mpr (hO z.property))).snd
  have hinput : Continuous (fun z : Z ↦ ((⟨z.val.proj, z.property⟩ : O), (a z.val).2)) :=
    (hbase.subtype_mk _).prodMk hcoord
  let P : O × E → E := fun z ↦
    (js z.1).toLinearMap.range.projection (ju z.1).toLinearMap.range (hcompl z.1) z.2
  have hP : Continuous P := continuous_projection_from_frames js ju hsinj huinj hcompl
    hscont hucont
  have hout : Continuous (fun z : Z ↦
      (⟨z.val.proj, a.symm z.val.proj (P (⟨z.val.proj, z.property⟩, (a z.val).2))⟩ :
        TangentBundle I X)) :=
    a.continuousOn_symm.comp_continuous (hbase.prodMk (hP.comp hinput))
      (fun z ↦ ⟨hO z.property, mem_univ _⟩)
  refine ⟨O, hOopen, hx, hout.congr ?_⟩
  intro z
  apply congrArg (fun v : TangentSpace I z.val.proj ↦
    (⟨z.val.proj, v⟩ : TangentBundle I X))
  let y : O := ⟨z.val.proj, z.property⟩
  let e := a.linearEquivAt ℝ z.val.proj (hO z.property)
  have hp : P (y, (a z.val).2) =
      e ((RS.toDistribution z.val.proj).projection (RU.toDistribution z.val.proj)
        (hc z.val.proj) z.val.snd) := by
    dsimp only [P]
    simp only [hsrange y, hurange y]
    exact projection_map_apply (RS.toDistribution z.val.proj) (RU.toDistribution z.val.proj)
      (hc z.val.proj) e z.val.snd
  rw [hp]
  change e.symm (e _) = _
  exact e.symm_apply_apply _

omit [FiniteDimensional ℝ E] in



theorem continuous_native_projection
    (RS RU : ContinuousRealTangentSubbundle I X)
    (hc : ∀ x, IsCompl (RS.toDistribution x) (RU.toDistribution x)) :
    Continuous (fun z : TangentBundle I X ↦
      (⟨z.proj, (RS.toDistribution z.proj).projection
        (RU.toDistribution z.proj) (hc z.proj) z.snd⟩ : TangentBundle I X)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨O, hO, hx, hcont⟩ := exists_continuous_native_projection I RS RU hc z.proj
  have hOn : ContinuousOn (fun w : TangentBundle I X ↦
      (⟨w.proj, (RS.toDistribution w.proj).projection
        (RU.toDistribution w.proj) (hc w.proj) w.snd⟩ : TangentBundle I X))
      {w | w.proj ∈ O} := continuousOn_iff_continuous_domRestrict.mpr hcont
  exact hOn.continuousAt ((hO.preimage
    (FiberBundle.continuous_proj E (TangentSpace I))).mem_nhds hx)

end NativeFrames


section OriginalComplexTotalSpace
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
attribute [local instance] complex_isManifold_real
variable (S U : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
  (hsplit : ∀ x, IsCompl (S x) (U x))
  (RS RU : ContinuousRealTangentSubbundle (realModel d) X)
  (hS : ∀ x, ((S x).restrictScalars ℝ).map
    (complexTangentToReal d x).toLinearEquiv.toLinearMap = RS.toDistribution x)
  (hU : ∀ x, ((U x).restrictScalars ℝ).map
    (complexTangentToReal d x).toLinearEquiv.toLinearMap = RU.toDistribution x)

include RS RU hS hU in




theorem continuous_original_stable_projection :
    Continuous (fun z : TangentBundle (complexModel d) X ↦
      (⟨z.proj, stableProjection S U hsplit z.proj z.snd⟩ :
        TangentBundle (complexModel d) X)) := by
  have hr := continuous_native_projection (realModel d) RS RU
    (original_real_subbundles_isCompl S U hsplit RS RU hS hU)
  have h := continuous_complexTangentToReal_symm.comp (hr.comp continuous_complexTangentToReal)
  apply h.congr
  intro z
  apply congrArg (fun v : TangentSpace (complexModel d) z.proj ↦
    (⟨z.proj, v⟩ : TangentBundle (complexModel d) X))
  change (complexTangentToReal d z.proj).symm
    ((RS.toDistribution z.proj).projection (RU.toDistribution z.proj)
      (original_real_subbundles_isCompl S U hsplit RS RU hS hU z.proj)
      ((complexTangentToReal d z.proj) z.snd)) = _
  rw [← original_projection_realification S U hsplit RS RU hS hU z.proj z.snd]
  exact (complexTangentToReal d z.proj).symm_apply_apply _

include RS RU hS hU in


theorem continuous_original_unstable_projection :
    Continuous (fun z : TangentBundle (complexModel d) X ↦
      (⟨z.proj, unstableProjection S U hsplit z.proj z.snd⟩ :
        TangentBundle (complexModel d) X)) :=
  continuous_original_stable_projection U S (fun x ↦ (hsplit x).symm) RU RS hU hS

end OriginalComplexTotalSpace


end HolomorphicAnosov.NativeSplittingPreparation














open Set Bundle
open scoped ContDiff Topology _root_.Topology














open Set Bundle
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Preparation

set_option autoImplicit false





theorem exists_continuous_subbundle_frame
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] (I : ModelWithCorners ℝ E H)
    [ChartedSpace H X] [IsManifold I ∞ X]
    (R : ContinuousRealTangentSubbundle I X) (x : X) :
    ∃ r : ℕ,
      letI : TopologicalSpace (TotalSpace (Fin r → ℝ)
          (fun y : X ↦ ↥(R.toDistribution y))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
      ∃ e : Trivialization (Fin r → ℝ)
          (TotalSpace.proj (F := Fin r → ℝ) (E := fun y : X ↦ ↥(R.toDistribution y))),
        x ∈ e.baseSet ∧ e.IsLinear ℝ ∧
        Continuous (fun z : e.baseSet × (Fin r → ℝ) ↦
          (⟨z.1.val, (e.symm z.1.val z.2).val⟩ : TangentBundle I X)) := by
  obtain ⟨r, hr⟩ := R.locally_trivial x
  refine ⟨r, ?_⟩
  let : TopologicalSpace (TotalSpace (Fin r → ℝ)
      (fun y : X ↦ ↥(R.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
  obtain ⟨e, hx, he⟩ := hr
  refine ⟨e, hx, he, ?_⟩
  have hc : Continuous (fun z : e.baseSet × (Fin r → ℝ) ↦
      (⟨z.1.val, e.symm z.1.val z.2⟩ :
        TotalSpace (Fin r → ℝ) (fun y : X ↦ ↥(R.toDistribution y)))) :=
    e.continuousOn_symm.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z ↦ ⟨z.1.property, mem_univ _⟩)
  exact continuous_induced_dom.comp hc




theorem continuous_compact_ratio_maximum
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K] [CompactSpace K]
    (p q : X → K → ℝ)
    (hp : Continuous (fun z : X × K ↦ p z.1 z.2))
    (hq : Continuous (fun z : X × K ↦ q z.1 z.2))
    (hqpos : ∀ x z, 0 < q x z) :
    Continuous (fun x ↦ sSup ((fun z ↦ p x z / q x z) '' (univ : Set K))) := by
  exact isCompact_univ.continuous_sSup (hp.div hq (fun z ↦ ne_of_gt (hqpos z.1 z.2)))






theorem uniform_seminorm_upper_bound
    {X V : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (p q : X → Seminorm ℝ V)
    (hp : Continuous (fun z : X × V ↦ p z.1 z.2))
    (hq : Continuous (fun z : X × V ↦ q z.1 z.2))
    (hqpos : ∀ x v, v ≠ 0 → 0 < q x v) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x v, p x v ≤ C * q x v := by
  let K := Metric.sphere (0 : V) 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hratio : Continuous (fun z : X × K ↦ p z.1 z.2.val / q z.1 z.2.val) := by
    have hc : Continuous (fun z : X × K ↦ (z.1, z.2.val)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    refine (hp.comp hc).div (hq.comp hc) ?_
    intro z
    apply ne_of_gt (hqpos z.1 z.2.val ?_)
    intro hz
    have hn : ‖z.2.val‖ = 1 := by simp [K]
    simp [hz] at hn
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hratio.continuousOn
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro x v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : V := ‖v‖⁻¹ • v
  have hw : w ∈ K := by
    simp [K, w, norm_smul, ne_of_gt hn]
  have hbound : p x w / q x w ≤ max 1 M :=
    (hM (mem_image_of_mem (fun z : X × K ↦ p z.1 z.2.val / q z.1 z.2.val)
      (mem_univ (x, (⟨w, hw⟩ : K))))).trans (le_max_right _ _)
  have hwne : w ≠ 0 := by
    intro hzero
    have : ‖w‖ = 1 := by simpa [K, Metric.mem_sphere, dist_zero_right] using hw
    simp [hzero] at this
  have hle := (div_le_iff₀ (hqpos x w hwne)).mp hbound
  have hscaled : ‖v‖⁻¹ * p x v ≤ ‖v‖⁻¹ * (max 1 M * q x v) := by
    simpa only [w, map_smul_eq_mul, norm_inv, Real.norm_of_nonneg (norm_nonneg v),
      mul_left_comm, mul_assoc] using hle
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr hn)).mp hscaled





theorem uniform_seminorm_comparison
    {X V : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (p q : X → Seminorm ℝ V)
    (hp : Continuous (fun z : X × V ↦ p z.1 z.2))
    (hq : Continuous (fun z : X × V ↦ q z.1 z.2))
    (hppos : ∀ x v, v ≠ 0 → 0 < p x v)
    (hqpos : ∀ x v, v ≠ 0 → 0 < q x v) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ 1 ≤ C ∧
      ∀ x v, c * q x v ≤ p x v ∧ p x v ≤ C * q x v := by
  obtain ⟨C, hC, hupper⟩ := uniform_seminorm_upper_bound p q hp hq hqpos
  obtain ⟨K, hK, hreverse⟩ := uniform_seminorm_upper_bound q p hq hp hppos
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨K⁻¹, C, inv_pos.mpr hKpos,
    (inv_le_one_of_one_le₀ hK).trans hC, hC, ?_⟩
  intro x v
  refine ⟨?_, hupper x v⟩
  calc
    K⁻¹ * q x v ≤ K⁻¹ * (K * p x v) :=
      mul_le_mul_of_nonneg_left (hreverse x v) (le_of_lt (inv_pos.mpr hKpos))
    _ = p x v := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hKpos), one_mul]








theorem exists_continuous_subbundle_ratio_maximum
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] (I : ModelWithCorners ℝ E H)
    [ChartedSpace H X] [IsManifold I ∞ X]
    (R : ContinuousRealTangentSubbundle I X)
    (p q : ∀ y : X, TangentSpace I y → ℝ)
    (hp : Continuous (fun z : TangentBundle I X ↦ p z.proj z.snd))
    (hq : Continuous (fun z : TangentBundle I X ↦ q z.proj z.snd))
    (hppos : ∀ y v, v ≠ 0 → 0 < p y v) (x : X) :
    ∃ r : ℕ,
      letI : TopologicalSpace (TotalSpace (Fin r → ℝ)
          (fun y : X ↦ ↥(R.toDistribution y))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
      ∃ e : Trivialization (Fin r → ℝ)
          (TotalSpace.proj (F := Fin r → ℝ) (E := fun y : X ↦ ↥(R.toDistribution y))),
        x ∈ e.baseSet ∧ e.IsLinear ℝ ∧
        Continuous (fun y : e.baseSet ↦
          sSup ((fun v : Metric.sphere (0 : Fin r → ℝ) 1 ↦
            q y.val (e.symm y.val v.val).val /
              p y.val (e.symm y.val v.val).val) '' univ)) := by
  obtain ⟨r, hr⟩ := exists_continuous_subbundle_frame I R x
  refine ⟨r, ?_⟩
  let : TopologicalSpace (TotalSpace (Fin r → ℝ)
      (fun y : X ↦ ↥(R.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
  obtain ⟨e, hx, he, hframe⟩ := hr
  refine ⟨e, hx, he, ?_⟩
  have : e.IsLinear ℝ := he
  have : CompactSpace (Metric.sphere (0 : Fin r → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have hcoords : Continuous (fun z : e.baseSet × Metric.sphere (0 : Fin r → ℝ) 1 ↦
      (z.1, z.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  apply continuous_compact_ratio_maximum
    (fun (y : e.baseSet) (v : Metric.sphere (0 : Fin r → ℝ) 1) ↦
      q y.val (e.symm y.val v.val).val)
    (fun (y : e.baseSet) (v : Metric.sphere (0 : Fin r → ℝ) 1) ↦
      p y.val (e.symm y.val v.val).val)
    (hq.comp (hframe.comp hcoords)) (hp.comp (hframe.comp hcoords))
  intro y v
  apply hppos
  intro hz
  have hezero : e.symm y.val v.val = 0 := Subtype.ext hz
  have hzero : v.val = 0 :=
    (e.linearEquivAt ℝ y.val y.property).symm.map_eq_zero_iff.mp hezero
  have hn : ‖v.val‖ = 1 := by simp
  simp [hzero] at hn


section ComplexFrames

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]

attribute [local instance] complex_isManifold_real





theorem exists_continuous_complex_subbundle_frame
    (R : ContinuousRealTangentSubbundle (realModel d) M) (x : M) :
    ∃ r : ℕ,
      letI : TopologicalSpace (TotalSpace (Fin r → ℝ)
          (fun y : M ↦ ↥(R.toDistribution y))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) M)) inferInstance
      ∃ e : Trivialization (Fin r → ℝ)
          (TotalSpace.proj (F := Fin r → ℝ) (E := fun y : M ↦ ↥(R.toDistribution y))),
        x ∈ e.baseSet ∧ e.IsLinear ℝ ∧
        Continuous (fun z : e.baseSet × (Fin r → ℝ) ↦
          (⟨z.1.val, (complexTangentToReal d z.1.val).symm
            (e.symm z.1.val z.2).val⟩ : TangentBundle (complexModel d) M)) := by
  obtain ⟨r, hr⟩ := exists_continuous_subbundle_frame (realModel d) R x
  refine ⟨r, ?_⟩
  let : TopologicalSpace (TotalSpace (Fin r → ℝ)
      (fun y : M ↦ ↥(R.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) M)) inferInstance
  obtain ⟨e, hx, he, hc⟩ := hr
  exact ⟨e, hx, he, continuous_complexTangentToReal_symm.comp hc⟩

end ComplexFrames





theorem core_inner_sum_smul
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] (h : InnerProductSpace.Core ℂ V)
    (b : ι → V) (w : ι → ℂ) :
    h.inner (∑ i, w i • b i) (∑ i, w i • b i) =
      ∑ i, ∑ j, star (w i) * w j * h.inner (b i) (b j) := by
  have hleft (s : Finset ι) (f : ι → V) (v : V) :
      h.inner (∑ i ∈ s, f i) v = ∑ i ∈ s, h.inner (f i) v := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [InnerProductSpace.Core.inner_zero_left]
    | @insert i s hi ih => simp [Finset.sum_insert hi, h.add_left, ih]
  have hright (s : Finset ι) (f : ι → V) (v : V) :
      h.inner v (∑ i ∈ s, f i) = ∑ i ∈ s, h.inner v (f i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [InnerProductSpace.Core.inner_zero_right]
    | @insert i s hi ih =>
      simp [Finset.sum_insert hi, InnerProductSpace.Core.inner_add_right, ih]
  rw [hleft Finset.univ]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hright Finset.univ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h.smul_left, InnerProductSpace.Core.inner_smul_right]
  simp [mul_assoc]





theorem continuous_hermitian_chart_frame_norm
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (e : OpenPartialHomeomorph M (ComplexModel d))
    (he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ M) :
    Continuous (fun z : e.target × (Fin d → ℂ) ↦
      Real.sqrt (((h (e.symm z.1.val)).inner
        (∑ i, z.2 i • hermitianTangentChartFrame e z.1.val i)
        (∑ i, z.2 i • hermitianTangentChartFrame e z.1.val i)).re)) := by
  have hc (i j : Fin d) :
      Continuous (fun z : e.target ↦ hermitianTangentChartCoefficient h e i j z.val) :=
    continuousOn_iff_continuous_domRestrict.mp (hh e he i j).continuousOn
  simp_rw [core_inner_sum_smul]
  apply Real.continuous_sqrt.comp
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  have hcoef : Continuous (fun z : e.target × (Fin d → ℂ) ↦
      (h (e.symm z.1.val)).inner
        (hermitianTangentChartFrame e z.1.val i)
        (hermitianTangentChartFrame e z.1.val j)) :=
    (hc j i).comp continuous_fst
  exact ((continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul
    ((continuous_apply j).comp continuous_snd)).mul hcoef


set_option backward.isDefEq.respectTransparency false in



theorem chart_frame_sum_eq_tangent_inverse
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (x : M) (z : ComplexModel d) (hz : z ∈ (chartAt (ComplexModel d) x).target)
    (w : Fin d → ℂ) :
    (∑ i, w i • hermitianTangentChartFrame (chartAt (ComplexModel d) x) z i) =
      (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x).symm
        ((chartAt (ComplexModel d) x).symm z) w := by
  let e := chartAt (ComplexModel d) x
  have hy : e.symm z ∈ e.source := e.map_target hz
  rw [← Trivialization.symmL_apply (R := ℂ) _ hy,
    TangentBundle.symmL_trivializationAt hy]
  simp only [complexModel, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]
  change (∑ i, w i • hermitianTangentChartFrame e z i) =
    mfderiv (complexModel d) (complexModel d) e.symm (e (e.symm z)) w
  rw [e.right_inv hz]
  change (∑ i, w i • mfderiv (complexModel d) (complexModel d) e.symm z
      ((NormedSpace.fromTangentSpace z).symm (Pi.single i 1))) =
    mfderiv (complexModel d) (complexModel d) e.symm z w
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  change (∑ i, w i • Pi.single i 1) = w
  exact (pi_eq_sum_univ' w).symm






theorem continuous_hermitian_tangent_norm
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    Continuous (fun z : TangentBundle (complexModel d) M ↦
      Real.sqrt (((h z.proj).inner z.snd z.snd).re)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let e := chartAt (ComplexModel d) z.proj
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) z.proj
  let A : Set (TangentBundle (complexModel d) M) := {w | w.proj ∈ e.source}
  have hA : IsOpen A := e.open_source.preimage
    (FiberBundle.continuous_proj (ComplexModel d) (TangentSpace (complexModel d)))
  have hzA : z ∈ A := mem_chart_source _ _
  have ht : Continuous (fun w : A ↦ t w.val) :=
    t.continuousOn.comp_continuous continuous_subtype_val (fun w ↦ w.property)
  have hbase : Continuous (fun w : A ↦ e w.val.proj) :=
    e.continuousOn.comp_continuous
      ((FiberBundle.continuous_proj (ComplexModel d) (TangentSpace (complexModel d))).comp
        continuous_subtype_val) (fun w ↦ w.property)
  let coords : A → e.target × (Fin d → ℂ) := fun w ↦
    (⟨e w.val.proj, e.map_source w.property⟩, (t w.val).2)
  have hcoords : Continuous coords :=
    (hbase.subtype_mk _).prodMk (continuous_snd.comp ht)
  have hc := (continuous_hermitian_chart_frame_norm h hh e
    (IsManifold.chart_mem_maximalAtlas _)).comp hcoords
  have hn : Continuous (fun w : A ↦
      Real.sqrt (((h w.val.proj).inner w.val.snd w.val.snd).re)) := by
    apply hc.congr
    intro w
    dsimp [coords]
    rw [chart_frame_sum_eq_tangent_inverse _ _ (e.map_source w.property)]
    rw [e.left_inv w.property]
    rw [Trivialization.symm_apply_apply_mk _ w.property]
  exact (continuousOn_iff_continuous_domRestrict.mpr hn).continuousAt (hA.mem_nhds hzA)






theorem locally_uniform_tangent_seminorm_bound
    {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (p q : ∀ y : M, Seminorm ℝ (TangentSpace (complexModel d) y))
    (hp : Continuous (fun z : TangentBundle (complexModel d) M ↦ p z.proj z.snd))
    (hq : Continuous (fun z : TangentBundle (complexModel d) M ↦ q z.proj z.snd))
    (hqpos : ∀ y v, v ≠ 0 → 0 < q y v) (x : M) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ y ∈ O, ∀ v, p y v ≤ C * q y v := by
  let e := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  obtain ⟨K, hKnhds, hKe, hKcompact⟩ := local_compact_nhds
    (e.open_baseSet.mem_nhds (by exact mem_chart_source (ComplexModel d) x))
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let frame (y : K) : ComplexModel d →ₗ[ℝ] TangentSpace (complexModel d) y.val :=
    ((e.linearEquivAt ℂ y.val (hKe y.property)).symm.toLinearMap).restrictScalars ℝ
  have hf : Continuous (fun z : K × ComplexModel d ↦
      (⟨z.1.val, frame z.1 z.2⟩ : TangentBundle (complexModel d) M)) := by
    exact e.continuousOn_symm.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z ↦ ⟨hKe z.1.property, mem_univ _⟩)
  let pk : K → Seminorm ℝ (ComplexModel d) := fun y ↦ (p y.val).comp (frame y)
  let qk : K → Seminorm ℝ (ComplexModel d) := fun y ↦ (q y.val).comp (frame y)
  have hpk : Continuous (fun z : K × ComplexModel d ↦ pk z.1 z.2) := hp.comp hf
  have hqk : Continuous (fun z : K × ComplexModel d ↦ qk z.1 z.2) := hq.comp hf
  have hqkpos : ∀ y v, v ≠ 0 → 0 < qk y v := by
    intro y v hv
    apply hqpos
    intro hz
    exact hv ((e.linearEquivAt ℂ y.val (hKe y.property)).symm.map_eq_zero_iff.mp hz)
  obtain ⟨C, hC, hbound⟩ := uniform_seminorm_upper_bound pk qk hpk hqk hqkpos
  refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hKnhds, C, hC, ?_⟩
  intro y hy v
  let yk : K := ⟨y, interior_subset hy⟩
  have he : frame yk ((e.linearEquivAt ℂ y (hKe yk.property)) v) = v :=
    (e.linearEquivAt ℂ y (hKe yk.property)).symm_apply_apply v
  simpa only [pk, qk, Seminorm.comp_apply, he] using
    hbound yk ((e.linearEquivAt ℂ y (hKe yk.property)) v)





theorem uniform_tangent_seminorm_upper_bound
    {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (p q : ∀ y : M, Seminorm ℝ (TangentSpace (complexModel d) y))
    (hp : Continuous (fun z : TangentBundle (complexModel d) M ↦ p z.proj z.snd))
    (hq : Continuous (fun z : TangentBundle (complexModel d) M ↦ q z.proj z.snd))
    (hqpos : ∀ y v, v ≠ 0 → 0 < q y v) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y v, p y v ≤ C * q y v := by
  classical
  choose O hO hx C hC hbound using locally_uniform_tangent_seminorm_bound p q hp hq hqpos
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun y _ ↦ mem_iUnion.mpr ⟨y, hx y⟩)
  refine ⟨max 1 (∑ x ∈ t, C x), le_max_left _ _, ?_⟩
  intro y v
  obtain ⟨x, hxt, hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  have hle : C x ≤ max 1 (∑ x ∈ t, C x) :=
    (Finset.single_le_sum (fun z _ ↦ (zero_le_one.trans (hC z))) hxt).trans
      (le_max_right _ _)
  exact (hbound x y hy v).trans (mul_le_mul_of_nonneg_right hle (apply_nonneg (q y) v))





theorem uniform_tangent_seminorm_comparison
    {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (p q : ∀ y : M, Seminorm ℝ (TangentSpace (complexModel d) y))
    (hp : Continuous (fun z : TangentBundle (complexModel d) M ↦ p z.proj z.snd))
    (hq : Continuous (fun z : TangentBundle (complexModel d) M ↦ q z.proj z.snd))
    (hppos : ∀ y v, v ≠ 0 → 0 < p y v)
    (hqpos : ∀ y v, v ≠ 0 → 0 < q y v) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ 1 ≤ C ∧
      ∀ y v, c * q y v ≤ p y v ∧ p y v ≤ C * q y v := by
  obtain ⟨C, hC, hupper⟩ := uniform_tangent_seminorm_upper_bound p q hp hq hqpos
  obtain ⟨K, hK, hreverse⟩ := uniform_tangent_seminorm_upper_bound q p hq hp hppos
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨K⁻¹, C, inv_pos.mpr hKpos,
    (inv_le_one_of_one_le₀ hK).trans hC, hC, ?_⟩
  intro y v
  refine ⟨?_, hupper y v⟩
  calc
    K⁻¹ * q y v ≤ K⁻¹ * (K * p y v) :=
      mul_le_mul_of_nonneg_left (hreverse y v) (le_of_lt (inv_pos.mpr hKpos))
    _ = p y v := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hKpos), one_mul]







theorem uniform_hermitian_tangent_norm_comparison
    {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (g : ∀ y : M, Seminorm ℝ (TangentSpace (complexModel d) y))
    (gcont : Continuous (fun z : TangentBundle (complexModel d) M ↦ g z.proj z.snd))
    (gpos : ∀ y v, v ≠ 0 → 0 < g y v)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ 1 ≤ C ∧ ∀ y v,
      c * Real.sqrt (((h y).inner v v).re) ≤ g y v ∧
      g y v ≤ C * Real.sqrt (((h y).inner v v).re) := by
  let hnorm (y : M) : Seminorm ℂ (TangentSpace (complexModel d) y) :=
    let : InnerProductSpace.Core ℂ (TangentSpace (complexModel d) y) := h y
    let : Norm (TangentSpace (complexModel d) y) := InnerProductSpace.Core.toNorm (𝕜 := ℂ)
    Seminorm.of (fun v ↦ Real.sqrt (((h y).inner v v).re))
      ((h y).toNormedSpaceCore.norm_triangle) ((h y).toNormedSpaceCore.norm_smul)
  let hr (y : M) : Seminorm ℝ (TangentSpace (complexModel d) y) :=
    (hnorm y).restrictScalars ℝ
  have hrcont : Continuous (fun z : TangentBundle (complexModel d) M ↦ hr z.proj z.snd) :=
    continuous_hermitian_tangent_norm h hh
  have hrpos : ∀ y v, v ≠ 0 → 0 < hr y v := by
    intro y v hv
    have hzero : hr y v = 0 ↔ v = 0 := by
      let : InnerProductSpace.Core ℂ (TangentSpace (complexModel d) y) := h y
      let : Norm (TangentSpace (complexModel d) y) := InnerProductSpace.Core.toNorm (𝕜 := ℂ)
      exact (h y).toNormedSpaceCore.norm_eq_zero_iff v
    exact lt_of_le_of_ne (apply_nonneg (hr y) v)
      (Ne.symm (hzero.not.mpr hv))
  exact uniform_tangent_seminorm_comparison g hr gcont hrcont gpos hrpos


section ComplexRatioMaximum

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]

attribute [local instance] complex_isManifold_real






theorem exists_continuous_complex_subbundle_ratio_maximum
    (R : ContinuousRealTangentSubbundle (realModel d) M)
    (p q : ∀ y : M, TangentSpace (complexModel d) y → ℝ)
    (hp : Continuous (fun z : TangentBundle (complexModel d) M ↦ p z.proj z.snd))
    (hq : Continuous (fun z : TangentBundle (complexModel d) M ↦ q z.proj z.snd))
    (hppos : ∀ y v, v ≠ 0 → 0 < p y v) (x : M) :
    ∃ r : ℕ,
      letI : TopologicalSpace (TotalSpace (Fin r → ℝ)
          (fun y : M ↦ ↥(R.toDistribution y))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) M)) inferInstance
      ∃ e : Trivialization (Fin r → ℝ)
          (TotalSpace.proj (F := Fin r → ℝ) (E := fun y : M ↦ ↥(R.toDistribution y))),
        x ∈ e.baseSet ∧ e.IsLinear ℝ ∧
        Continuous (fun y : e.baseSet ↦
          sSup ((fun v : Metric.sphere (0 : Fin r → ℝ) 1 ↦
            q y.val ((complexTangentToReal d y.val).symm (e.symm y.val v.val).val) /
              p y.val ((complexTangentToReal d y.val).symm (e.symm y.val v.val).val)) '' univ)) := by
  let rp (y : M) (v : TangentSpace (realModel d) y) :=
    p y ((complexTangentToReal d y).symm v)
  let rq (y : M) (v : TangentSpace (realModel d) y) :=
    q y ((complexTangentToReal d y).symm v)
  have hrp : Continuous (fun z : TangentBundle (realModel d) M ↦ rp z.proj z.snd) :=
    hp.comp continuous_complexTangentToReal_symm
  have hrq : Continuous (fun z : TangentBundle (realModel d) M ↦ rq z.proj z.snd) :=
    hq.comp continuous_complexTangentToReal_symm
  have hrpos : ∀ y v, v ≠ 0 → 0 < rp y v := by
    intro y v hv
    apply hppos
    intro hzero
    exact hv ((complexTangentToReal d y).symm.map_eq_zero_iff.mp hzero)
  exact exists_continuous_subbundle_ratio_maximum (realModel d) R rp rq hrp hrq hrpos x

end ComplexRatioMaximum


end HolomorphicAnosov.Preparation
namespace HolomorphicAnosov.NativeProjectionBounds
open HermitianFibreAlgebra NativeSplittingPreparation Preparation
open scoped ContDiff
attribute [local instance] complex_isManifold_real

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]





theorem uniform_hermitian_linear_family_bound
    (L : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ]
      TangentSpace (complexModel d) x)
    (hL : Continuous (fun z : TangentBundle (complexModel d) X ↦
      (⟨z.proj, L z.proj z.snd⟩ : TangentBundle (complexModel d) X)))
    (h : HermitianTangentMetricCore d X) (hh : IsSmoothHermitianTangentMetric h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x v,
      hermitianBoundsNorm h x (L x v) ≤ C * hermitianBoundsNorm h x v := by
  let q : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x) :=
    hermitianBoundsRealSeminorm h
  let p : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x) :=
    fun x ↦ (q x).comp ((L x).toLinearMap.restrictScalars ℝ)
  have hq : Continuous (fun z : TangentBundle (complexModel d) X ↦ q z.proj z.snd) :=
    continuous_hermitian_tangent_norm h hh
  have hp : Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd) :=
    hq.comp hL
  have hqpos : ∀ x v, v ≠ 0 → 0 < q x v := by
    intro x v hv
    exact coreLength_pos (h x) hv
  exact uniform_tangent_seminorm_upper_bound p q hp hq hqpos














theorem uniform_original_hermitian_projection_bounds
    (S U : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
    (hsplit : ∀ x, IsCompl (S x) (U x))
    (RS RU : ContinuousRealTangentSubbundle (realModel d) X)
    (hS : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = RS.toDistribution x)
    (hU : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = RU.toDistribution x)
    (h : HermitianTangentMetricCore d X) (hh : IsSmoothHermitianTangentMetric h) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x v,
      hermitianBoundsNorm h x (stableProjection S U hsplit x v) ≤
          K * hermitianBoundsNorm h x v ∧
        hermitianBoundsNorm h x (unstableProjection S U hsplit x v) ≤
          K * hermitianBoundsNorm h x v := by
  obtain ⟨Cs, hCs, hs⟩ := uniform_hermitian_linear_family_bound
    (stableProjection S U hsplit)
    (continuous_original_stable_projection S U hsplit RS RU hS hU) h hh
  obtain ⟨Cu, hCu, hu⟩ := uniform_hermitian_linear_family_bound
    (unstableProjection S U hsplit)
    (continuous_original_unstable_projection S U hsplit RS RU hS hU) h hh
  refine ⟨max Cs Cu, hCs.trans (le_max_left _ _), ?_⟩
  intro x v
  have hv : 0 ≤ hermitianBoundsNorm h x v := Real.sqrt_nonneg _
  exact ⟨(hs x v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv),
    (hu x v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hv)⟩


end HolomorphicAnosov.NativeProjectionBounds










namespace HolomorphicAnosov.NativeOperatorPreparation

open Set Bundle
open scoped ContDiff Topology _root_.Topology

noncomputable section
set_option autoImplicit false

variable {d : ℕ} {X : Type*} [TopologicalSpace X]
variable [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

attribute [local instance] complex_isManifold_real




theorem continuous_iterate_derivative_total (f : Biholomorph d d X X) (n : ℕ) :
    Continuous (fun z : TangentBundle (complexModel d) X ↦
      (⟨hermitianBoundsIterate f n z.proj,
        hermitianBoundsDerivative f n z.proj z.snd⟩ : TangentBundle (complexModel d) X)) := by
  change Continuous (tangentMap (complexModel d) (complexModel d) (hermitianBoundsIterate f n))
  exact (hermitianBoundsIterate f n).contMDiff_toFun.continuous_tangentMap
    (by simp : (1 : ℕ∞ω) ≤ ∞)






theorem exists_continuous_subbundle_frame
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace X] (I : ModelWithCorners ℝ E H)
    [ChartedSpace H X] [IsManifold I ∞ X]
    (R : ContinuousRealTangentSubbundle I X) (x : X) :
    ∃ r : ℕ,
      letI : TopologicalSpace (TotalSpace (Fin r → ℝ)
          (fun y : X ↦ ↥(R.toDistribution y))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
      ∃ e : Trivialization (Fin r → ℝ)
          (TotalSpace.proj (F := Fin r → ℝ) (E := fun y : X ↦ ↥(R.toDistribution y))),
        x ∈ e.baseSet ∧ e.IsLinear ℝ ∧
        Continuous (fun z : e.baseSet × (Fin r → ℝ) ↦
          (⟨z.1.val, (e.symm z.1.val z.2).val⟩ : TangentBundle I X)) := by
  obtain ⟨r, hr⟩ := R.locally_trivial x
  refine ⟨r, ?_⟩
  let : TopologicalSpace (TotalSpace (Fin r → ℝ)
      (fun y : X ↦ ↥(R.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I X)) inferInstance
  obtain ⟨e, hx, he⟩ := hr
  refine ⟨e, hx, he, ?_⟩
  have hc : Continuous (fun z : e.baseSet × (Fin r → ℝ) ↦
      (⟨z.1.val, e.symm z.1.val z.2⟩ :
        TotalSpace (Fin r → ℝ) (fun y : X ↦ ↥(R.toDistribution y)))) :=
    e.continuousOn_symm.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z ↦ ⟨z.1.property, mem_univ _⟩)
  exact continuous_induced_dom.comp hc






theorem exists_continuous_complex_subbundle_frame
    (R : ContinuousRealTangentSubbundle (realModel d) X) (x : X) :
    ∃ r : ℕ,
      letI : TopologicalSpace (TotalSpace (Fin r → ℝ)
          (fun y : X ↦ ↥(R.toDistribution y))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) X)) inferInstance
      ∃ e : Trivialization (Fin r → ℝ)
          (TotalSpace.proj (F := Fin r → ℝ) (E := fun y : X ↦ ↥(R.toDistribution y))),
        x ∈ e.baseSet ∧ e.IsLinear ℝ ∧
        Continuous (fun z : e.baseSet × (Fin r → ℝ) ↦
          (⟨z.1.val, (complexTangentToReal d z.1.val).symm
            (e.symm z.1.val z.2).val⟩ : TangentBundle (complexModel d) X)) := by
  obtain ⟨r, hr⟩ := exists_continuous_subbundle_frame (realModel d) R x
  refine ⟨r, ?_⟩
  let : TopologicalSpace (TotalSpace (Fin r → ℝ)
      (fun y : X ↦ ↥(R.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) X)) inferInstance
  obtain ⟨e, hx, he, hc⟩ := hr
  exact ⟨e, hx, he, continuous_complexTangentToReal_symm.comp hc⟩





def complexSubspaceToRealDistribution
    (P : ∀ y : X, Submodule ℂ (TangentSpace (complexModel d) y))
    (R : ContinuousRealTangentSubbundle (realModel d) X)
    (hP : ∀ y, ((P y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = R.toDistribution y)
    (y : X) : P y ≃ₗ[ℝ] R.toDistribution y :=
  ((Submodule.restrictScalarsEquiv ℝ ℂ _ (P y)).symm.restrictScalars ℝ).trans
    (((complexTangentToReal d y).toLinearEquiv.submoduleMap ((P y).restrictScalars ℝ)).trans
      (LinearEquiv.ofEq _ _ (hP y)))



theorem complexSubspaceToRealDistribution_symm_val
    (P : ∀ y : X, Submodule ℂ (TangentSpace (complexModel d) y))
    (R : ContinuousRealTangentSubbundle (realModel d) X)
    (hP : ∀ y, ((P y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = R.toDistribution y)
    (y : X) (v : R.toDistribution y) :
    ((complexSubspaceToRealDistribution P R hP y).symm v).val =
      (complexTangentToReal d y).symm v.val := rfl


set_option maxHeartbeats 800000 in




theorem exists_continuous_iterate_operator_ratio
    (f : Biholomorph d d X X) (n : ℕ)
    (P : ∀ y : X, Submodule ℂ (TangentSpace (complexModel d) y))
    (R : ContinuousRealTangentSubbundle (realModel d) X)
    (hP : ∀ y, ((P y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = R.toDistribution y)
    (g : ∀ y : X, Seminorm ℝ (TangentSpace (complexModel d) y))
    (gcont : Continuous (fun z : TangentBundle (complexModel d) X ↦ g z.proj z.snd))
    (gpos : ∀ y v, v ≠ 0 → 0 < g y v) (x : X) :
    ∃ r : ℕ,
      letI : TopologicalSpace (TotalSpace (Fin r → ℝ)
          (fun y : X ↦ ↥(R.toDistribution y))) :=
        TopologicalSpace.induced
          (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) X)) inferInstance
      ∃ e : Trivialization (Fin r → ℝ)
          (TotalSpace.proj (F := Fin r → ℝ) (E := fun y : X ↦ ↥(R.toDistribution y))),
        x ∈ e.baseSet ∧ ∃ he : e.IsLinear ℝ,
        letI := he
        let frame (y : e.baseSet) : (Fin r → ℝ) ≃ₗ[ℝ] P y.val :=
          (e.linearEquivAt ℝ y.val y.property).symm.trans
            (complexSubspaceToRealDistribution P R hP y.val).symm
        Continuous (fun z : e.baseSet × Metric.sphere (0 : Fin r → ℝ) 1 ↦
          g (hermitianBoundsIterate f n z.1.val)
              (hermitianBoundsDerivative f n z.1.val (frame z.1 z.2.val).val) /
            g z.1.val (frame z.1 z.2.val).val) ∧
        Continuous (fun y : e.baseSet ↦ sSup
          ((fun v : Metric.sphere (0 : Fin r → ℝ) 1 ↦
            g (hermitianBoundsIterate f n y.val)
                (hermitianBoundsDerivative f n y.val (frame y v.val).val) /
              g y.val (frame y v.val).val) '' univ)) := by
  obtain ⟨r, hr⟩ := exists_continuous_complex_subbundle_frame R x
  refine ⟨r, ?_⟩
  let : TopologicalSpace (TotalSpace (Fin r → ℝ)
      (fun y : X ↦ ↥(R.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) X)) inferInstance
  obtain ⟨e, hx, he, hframe⟩ := hr
  refine ⟨e, hx, he, ?_⟩
  have : e.IsLinear ℝ := he
  let frame (y : e.baseSet) : (Fin r → ℝ) ≃ₗ[ℝ] P y.val :=
    (e.linearEquivAt ℝ y.val y.property).symm.trans
      (complexSubspaceToRealDistribution P R hP y.val).symm
  have : CompactSpace (Metric.sphere (0 : Fin r → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have hcoords : Continuous (fun z : e.baseSet × Metric.sphere (0 : Fin r → ℝ) 1 ↦
      (z.1, z.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hf : Continuous (fun z : e.baseSet × Metric.sphere (0 : Fin r → ℝ) 1 ↦
      (⟨z.1.val, (frame z.1 z.2.val).val⟩ : TangentBundle (complexModel d) X)) :=
    hframe.comp hcoords
  have hden := gcont.comp hf
  have hnum := gcont.comp ((continuous_iterate_derivative_total f n).comp hf)
  have hratio : Continuous (fun z : e.baseSet × Metric.sphere (0 : Fin r → ℝ) 1 ↦
      g (hermitianBoundsIterate f n z.1.val)
          (hermitianBoundsDerivative f n z.1.val (frame z.1 z.2.val).val) /
        g z.1.val (frame z.1 z.2.val).val) := by
    refine hnum.div hden ?_
    intro z
    apply ne_of_gt (gpos z.1.val _ ?_)
    intro hz
    have hfzero : frame z.1 z.2.val = 0 := Subtype.ext hz
    have hzero : z.2.val = 0 := (frame z.1).map_eq_zero_iff.mp hfzero
    have hn : ‖z.2.val‖ = 1 := by simp
    simp [hzero] at hn
  exact ⟨hratio, isCompact_univ.continuous_sSup hratio⟩


namespace SphereIdentification
variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]


theorem ratio_is_unit_ball_value (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (frame : E ≃ₗ[ℝ] P) (L : V →ₗ[ℝ] W)
    (hp : ∀ v : V, v ≠ 0 → 0 < p v) {w : E} (hw : ‖w‖ = 1) :
    ∃ v : V, v ∈ P ∧ p v ≤ 1 ∧ q (L v) = q (L (frame w)) / p (frame w) := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hv0 : (frame w : V) ≠ 0 := by
    intro h
    apply hw0
    exact frame.injective (by exact Subtype.ext (by simpa using h))
  have hpos := hp (frame w) hv0
  refine ⟨(p (frame w))⁻¹ • (frame w : V),
    (P.restrictScalars ℝ).smul_mem _ (frame w).property, ?_, ?_⟩
  · rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
    simp [hpos.ne']
  · rw [L.map_smul, map_smul_eq_mul,
      Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
    exact (div_eq_inv_mul _ _).symm



theorem pointwise_bound_of_sphere_ratio (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (frame : E ≃ₗ[ℝ] P) (L : V →ₗ[ℝ] W)
    (hp : ∀ v : V, v ≠ 0 → 0 < p v) {C : ℝ}
    (hC : ∀ w : E, ‖w‖ = 1 → q (L (frame w)) / p (frame w) ≤ C)
    {v : V} (hv : v ∈ P) : q (L v) ≤ C * p v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  let w : E := frame.symm ⟨v, hv⟩
  have hw0 : w ≠ 0 := by
    intro h
    apply hv0
    have := congrArg (fun z : P ↦ (z : V)) (frame.apply_symm_apply ⟨v, hv⟩)
    simpa [w, h] using this.symm
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hunit : ‖(‖w‖)⁻¹ • w‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    exact inv_mul_cancel₀ hn.ne'
  have hframe : (frame ((‖w‖)⁻¹ • w) : V) = (‖w‖)⁻¹ • v := by
    rw [frame.map_smul]
    change (‖w‖)⁻¹ • ((frame w : P) : V) = _
    rw [show frame w = ⟨v, hv⟩ from frame.apply_symm_apply _]
  have ht := hC ((‖w‖)⁻¹ • w) hunit
  rw [hframe, L.map_smul, map_smul_eq_mul, map_smul_eq_mul,
    Real.norm_of_nonneg (inv_nonneg.mpr hn.le)] at ht
  have hpos := hp v hv0
  have hden : 0 < (‖w‖)⁻¹ * p v := mul_pos (inv_pos.mpr hn) hpos
  have ht' := (div_le_iff₀ hden).mp ht
  have hmul : (‖w‖)⁻¹ * q (L v) ≤ (‖w‖)⁻¹ * (C * p v) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using ht'
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr hn)).mp hmul



theorem operator_eq_sphere_ratio_sup (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (frame : E ≃ₗ[ℝ] P) (L : V →ₗ[ℝ] W)
    (hp : ∀ v : V, v ≠ 0 → 0 < p v) (hsphere : ∃ w : E, ‖w‖ = 1)
    (hb : BddAbove {a : ℝ | ∃ w : E, ‖w‖ = 1 ∧ a = q (L (frame w)) / p (frame w)}) :
    fibreNormOperator p q P L =
      sSup {a : ℝ | ∃ w : E, ‖w‖ = 1 ∧ a = q (L (frame w)) / p (frame w)} := by
  let T : Set ℝ := {a : ℝ | ∃ w : E, ‖w‖ = 1 ∧ a = q (L (frame w)) / p (frame w)}
  have hT : T.Nonempty := by
    obtain ⟨w, hw⟩ := hsphere
    exact ⟨_, w, hw, rfl⟩
  have hnonneg : 0 ≤ sSup T := by
    obtain ⟨w, hw⟩ := hsphere
    exact (div_nonneg (apply_nonneg q _) (apply_nonneg p _)).trans
      (le_csSup hb ⟨w, hw, rfl⟩)
  have hpoint : ∀ v ∈ P, q (L v) ≤ sSup T * p v := by
    intro v hv
    exact pointwise_bound_of_sphere_ratio p q P frame L hp
      (fun w hw ↦ le_csSup hb ⟨w, hw, rfl⟩) hv
  have hball : BddAbove {a : ℝ | ∃ v : V, v ∈ P ∧ p v ≤ 1 ∧ a = q (L v)} := by
    refine ⟨sSup T, ?_⟩
    rintro a ⟨v, hv, hpv, rfl⟩
    exact (hpoint v hv).trans (mul_le_of_le_one_right hnonneg hpv)
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, 0, P.zero_mem, by simp, by simp⟩
    · rintro a ⟨v, hv, hpv, rfl⟩
      exact (hpoint v hv).trans (mul_le_of_le_one_right hnonneg hpv)
  · apply csSup_le hT
    rintro a ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hpv, heq⟩ := ratio_is_unit_ball_value p q P frame L hp hw
    exact le_csSup hball ⟨v, hv, hpv, heq.symm⟩



theorem operator_zero_of_subsingleton_model [Subsingleton E]
    (p : Seminorm ℝ V) (q : Seminorm ℝ W) (P : Submodule ℂ V)
    (frame : E ≃ₗ[ℝ] P) (L : V →ₗ[ℝ] W) : fibreNormOperator p q P L = 0 := by
  have hP : P = ⊥ := by
    apply bot_unique
    intro v hv
    have hw : frame.symm ⟨v, hv⟩ = 0 := Subsingleton.elim _ _
    have ht := congrArg (fun z : P ↦ (z : V)) (frame.apply_symm_apply ⟨v, hv⟩)
    simpa [hw] using ht.symm
  simp [hP, fibreNormOperator]



theorem operator_eq_compact_sphere_image_sup (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (frame : E ≃ₗ[ℝ] P) (L : V →ₗ[ℝ] W)
    (hp : ∀ v : V, v ≠ 0 → 0 < p v)
    (hcompact : IsCompact (Metric.sphere (0 : E) 1))
    (hne : (Metric.sphere (0 : E) 1).Nonempty)
    (hcont : ContinuousOn (fun w : E ↦ q (L (frame w)) / p (frame w))
      (Metric.sphere (0 : E) 1)) :
    fibreNormOperator p q P L =
      sSup ((fun w : E ↦ q (L (frame w)) / p (frame w)) '' Metric.sphere (0 : E) 1) := by
  have hset : {a : ℝ | ∃ w : E, ‖w‖ = 1 ∧ a = q (L (frame w)) / p (frame w)} =
      (fun w : E ↦ q (L (frame w)) / p (frame w)) '' Metric.sphere (0 : E) 1 := by
    ext a
    simp only [mem_ofPred_eq, mem_image, Metric.mem_sphere, dist_zero_right]
    constructor
    · rintro ⟨w, hw, ha⟩
      exact ⟨w, hw, ha.symm⟩
    · rintro ⟨w, hw, ha⟩
      exact ⟨w, hw, ha.symm⟩
  rw [← hset]
  apply operator_eq_sphere_ratio_sup p q P frame L hp
  · obtain ⟨w, hw⟩ := hne
    exact ⟨w, by simpa [Metric.mem_sphere, dist_zero_right] using hw⟩
  · rw [hset]
    exact (hcompact.image_of_continuousOn hcont).bddAbove



theorem operator_eq_sphere_subtype_sup (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (frame : E ≃ₗ[ℝ] P) (L : V →ₗ[ℝ] W)
    (hp : ∀ v : V, v ≠ 0 → 0 < p v)
    (hcompact : IsCompact (Metric.sphere (0 : E) 1))
    (hne : (Metric.sphere (0 : E) 1).Nonempty)
    (hcont : ContinuousOn (fun w : E ↦ q (L (frame w)) / p (frame w))
      (Metric.sphere (0 : E) 1)) :
    fibreNormOperator p q P L =
      sSup ((fun w : ↥(Metric.sphere (0 : E) 1) ↦
        q (L (frame w.val)) / p (frame w.val)) '' univ) := by
  rw [operator_eq_compact_sphere_image_sup p q P frame L hp hcompact hne hcont]
  congr 1
  ext a
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, mem_univ _, rfl⟩
  · rintro ⟨w, _, rfl⟩
    exact ⟨w.val, w.property, rfl⟩


end SphereIdentification

set_option maxHeartbeats 1000000 in





theorem continuous_restricted_iterate_operator
    (f : Biholomorph d d X X) (n : ℕ)
    (P : ∀ y : X, Submodule ℂ (TangentSpace (complexModel d) y))
    (R : ContinuousRealTangentSubbundle (realModel d) X)
    (hP : ∀ y, ((P y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = R.toDistribution y)
    (g : ∀ y : X, Seminorm ℝ (TangentSpace (complexModel d) y))
    (gcont : Continuous (fun z : TangentBundle (complexModel d) X ↦ g z.proj z.snd))
    (gpos : ∀ y v, v ≠ 0 → 0 < g y v) :
    Continuous (fun y ↦ fibreNormOperator (g y) (g (hermitianBoundsIterate f n y))
      (P y) (hermitianBoundsDerivative f n y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨r, hr⟩ := exists_continuous_iterate_operator_ratio f n P R hP g gcont gpos x
  let : TopologicalSpace (TotalSpace (Fin r → ℝ)
      (fun y : X ↦ ↥(R.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) X)) inferInstance
  obtain ⟨e, hx, he, hratio, hmax⟩ := hr
  have : e.IsLinear ℝ := he
  let frame (y : e.baseSet) : (Fin r → ℝ) ≃ₗ[ℝ] P y.val :=
    (e.linearEquivAt ℝ y.val y.property).symm.trans
      (complexSubspaceToRealDistribution P R hP y.val).symm
  have hc : Continuous (fun y : e.baseSet ↦
      fibreNormOperator (g y.val) (g (hermitianBoundsIterate f n y.val))
        (P y.val) (hermitianBoundsDerivative f n y.val)) := by
    by_cases hrzero : r = 0
    · subst r
      apply continuous_const.congr
      intro y
      exact (SphereIdentification.operator_zero_of_subsingleton_model (g y.val)
        (g (hermitianBoundsIterate f n y.val)) (P y.val) (frame y)
        ((hermitianBoundsDerivative f n y.val).toContinuousLinearMap.toLinearMap.restrictScalars ℝ)).symm
    · have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hrzero⟩⟩
      have hne : (Metric.sphere (0 : Fin r → ℝ) 1).Nonempty := by
        obtain ⟨v, hv⟩ := exists_norm_eq (Fin r → ℝ) (by norm_num : (0 : ℝ) ≤ 1)
        exact ⟨v, by simpa [Metric.mem_sphere, dist_zero_right] using hv⟩
      apply hmax.congr
      intro y
      exact (SphereIdentification.operator_eq_sphere_subtype_sup (g y.val)
        (g (hermitianBoundsIterate f n y.val)) (P y.val) (frame y)
        ((hermitianBoundsDerivative f n y.val).toContinuousLinearMap.toLinearMap.restrictScalars ℝ)
        (gpos y.val) (isCompact_sphere 0 1) hne
        (continuousOn_iff_continuous_domRestrict.mpr
          (hratio.comp ((continuous_const : Continuous (fun _ : ↥(Metric.sphere (0 : Fin r → ℝ) 1) ↦ y)).prodMk continuous_id)))).symm
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt (e.open_baseSet.mem_nhds hx)


omit [IsManifold (complexModel d) ∞ X] in



theorem inverse_derivative_total_eq (f : Biholomorph d d X X) (n : ℕ) (x : X)
    (w : TangentSpace (complexModel d) (hermitianBoundsIterate f n x)) :
    tangentMap (complexModel d) (complexModel d) (hermitianBoundsIterate f n).symm
      ⟨hermitianBoundsIterate f n x, w⟩ =
      (⟨x, (hermitianBoundsDerivative f n x).symm w⟩ : TangentBundle (complexModel d) X) := by
  let F := hermitianBoundsIterate f n
  have hcomp : (F.symm : X → X) ∘ F = id := by
    funext y
    exact F.symm_apply_apply y
  have h := tangentMap_comp_at
    (⟨x, (hermitianBoundsDerivative f n x).symm w⟩ : TangentBundle (complexModel d) X)
    (F.symm.contMDiff_toFun.mdifferentiable (by simp) (F x))
    (F.contMDiff_toFun.mdifferentiable (by simp) x)
  change tangentMap (complexModel d) (complexModel d) ((F.symm : X → X) ∘ F) _ =
    tangentMap (complexModel d) (complexModel d) F.symm
      (tangentMap (complexModel d) (complexModel d) F _) at h
  rw [hcomp] at h
  change tangentMap (complexModel d) (complexModel d) id _ =
    tangentMap (complexModel d) (complexModel d) F.symm
      ⟨F x, hermitianBoundsDerivative f n x ((hermitianBoundsDerivative f n x).symm w)⟩ at h
  simpa [tangentMap, mfderiv_id, F] using h.symm


omit [IsManifold (complexModel d) ∞ X] in



theorem inverse_operator_eq_reverse_iterate (f : Biholomorph d d X X) (n : ℕ)
    (P : ∀ y : X, Submodule ℂ (TangentSpace (complexModel d) y))
    (g : ∀ y : X, Seminorm ℝ (TangentSpace (complexModel d) y)) (x : X) :
    fibreNormOperator (g (hermitianBoundsIterate f n x)) (g x)
        (P (hermitianBoundsIterate f n x)) (hermitianBoundsDerivative f n x).symm =
      fibreNormOperator (g (hermitianBoundsIterate f n x))
        (g (hermitianBoundsIterate f.symm n (hermitianBoundsIterate f n x)))
        (P (hermitianBoundsIterate f n x))
        (hermitianBoundsDerivative f.symm n (hermitianBoundsIterate f n x)) := by
  have hn (v : TangentSpace (complexModel d) (hermitianBoundsIterate f n x)) :
      g (hermitianBoundsIterate f.symm n (hermitianBoundsIterate f n x))
          (hermitianBoundsDerivative f.symm n (hermitianBoundsIterate f n x) v) =
        g x ((hermitianBoundsDerivative f n x).symm v) := by
    exact congrArg (fun z : TangentBundle (complexModel d) X ↦ g z.proj z.snd)
      (inverse_derivative_total_eq f n x v)
  unfold fibreNormOperator
  congr 1
  ext a
  simp only [mem_ofPred_eq]
  constructor <;> rintro ⟨v, hv, hgv, ha⟩
  · exact ⟨v, hv, hgv, ha.trans (hn v).symm⟩
  · exact ⟨v, hv, hgv, ha.trans (hn v)⟩




theorem continuous_restricted_inverse_iterate_operator
    (f : Biholomorph d d X X) (n : ℕ)
    (P : ∀ y : X, Submodule ℂ (TangentSpace (complexModel d) y))
    (R : ContinuousRealTangentSubbundle (realModel d) X)
    (hP : ∀ y, ((P y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = R.toDistribution y)
    (g : ∀ y : X, Seminorm ℝ (TangentSpace (complexModel d) y))
    (gcont : Continuous (fun z : TangentBundle (complexModel d) X ↦ g z.proj z.snd))
    (gpos : ∀ y v, v ≠ 0 → 0 < g y v) :
    Continuous (fun y ↦ fibreNormOperator (g (hermitianBoundsIterate f n y)) (g y)
      (P (hermitianBoundsIterate f n y)) (hermitianBoundsDerivative f n y).symm) := by
  apply ((continuous_restricted_iterate_operator f.symm n P R hP g gcont gpos).comp
    (hermitianBoundsIterate f n).continuous).congr
  intro x
  exact (inverse_operator_eq_reverse_iterate f n P g x).symm





theorem compact_common_strict_bound {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (u v : Y → ℝ) (hu : Continuous u) (hv : Continuous v)
    (h : ∀ y, u y < 1 ∧ v y < 1) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∀ y, u y ≤ a ∧ v y ≤ a := by
  have hc : Continuous (fun y ↦ max (u y) (v y)) := hu.max hv
  obtain ⟨b, hb, hbound⟩ :=
    isCompact_univ.exists_forall_le' (α := ℝᵒᵈ) hc.continuousOn
      (fun y _ ↦ (show max (u y) (v y) < (1 : ℝ) from max_lt_iff.mpr (h y)))
  refine ⟨max (1 / 2 : ℝ) b, lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    max_lt (by norm_num) hb, ?_⟩
  intro y
  have hy : max (u y) (v y) ≤ b := hbound y (mem_univ _)
  exact ⟨(le_max_left _ _).trans (hy.trans (le_max_right _ _)),
    (le_max_right _ _).trans (hy.trans (le_max_right _ _))⟩




theorem compact_finite_common_bound {I Y : Type*} [Finite I]
    [TopologicalSpace Y] [CompactSpace Y] (u v : I → Y → ℝ)
    (hu : ∀ i, Continuous (u i)) (hv : ∀ i, Continuous (v i)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ i y, u i y ≤ R ∧ v i y ≤ R := by
  obtain ⟨b, hb⟩ :=
    (isCompact_iUnion (fun i ↦ isCompact_range ((hu i).max (hv i)))).bddAbove
  refine ⟨max 1 b, le_max_left _ _, ?_⟩
  intro i y
  have hy : max (u i y) (v i y) ≤ b :=
    hb (mem_iUnion.mpr ⟨i, mem_range_self y⟩)
  exact ⟨(le_max_left _ _).trans (hy.trans (le_max_right _ _)),
    (le_max_right _ _).trans (hy.trans (le_max_right _ _))⟩

set_option maxHeartbeats 1000000 in







theorem native_compact_block_residue_bounds [CompactSpace X]
    (f : Biholomorph d d X X)
    (S U : ∀ y : X, Submodule ℂ (TangentSpace (complexModel d) y))
    (RS RU : ContinuousRealTangentSubbundle (realModel d) X)
    (hS : ∀ y, ((S y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = RS.toDistribution y)
    (hU : ∀ y, ((U y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = RU.toDistribution y)
    (g : ∀ y : X, Seminorm ℝ (TangentSpace (complexModel d) y))
    (gcont : Continuous (fun z : TangentBundle (complexModel d) X ↦ g z.proj z.snd))
    (gpos : ∀ y v, v ≠ 0 → 0 < g y v) (k : ℕ)
    (hcontract : ∀ x,
      fibreNormOperator (g x) (g (hermitianBoundsIterate f k x)) (S x)
          (hermitianBoundsDerivative f k x) < 1 ∧
        fibreNormOperator (g (hermitianBoundsIterate f k x)) (g x)
          (U (hermitianBoundsIterate f k x)) (hermitianBoundsDerivative f k x).symm < 1) :
    ∃ a R : ℝ, 0 < a ∧ a < 1 ∧ 1 ≤ R ∧
      (∀ x, fibreNormOperator (g x) (g (hermitianBoundsIterate f k x)) (S x)
          (hermitianBoundsDerivative f k x) ≤ a ∧
        fibreNormOperator (g (hermitianBoundsIterate f k x)) (g x)
          (U (hermitianBoundsIterate f k x)) (hermitianBoundsDerivative f k x).symm ≤ a) ∧
      (∀ r < k, ∀ x, fibreNormOperator (g x) (g (hermitianBoundsIterate f r x)) (S x)
          (hermitianBoundsDerivative f r x) ≤ R ∧
        fibreNormOperator (g (hermitianBoundsIterate f r x)) (g x)
          (U (hermitianBoundsIterate f r x)) (hermitianBoundsDerivative f r x).symm ≤ R) := by
  obtain ⟨a, ha, ha1, hab⟩ := compact_common_strict_bound _ _
    (continuous_restricted_iterate_operator f k S RS hS g gcont gpos)
    (continuous_restricted_inverse_iterate_operator f k U RU hU g gcont gpos) hcontract
  obtain ⟨R, hR, hRb⟩ := compact_finite_common_bound
    (fun r : Fin k ↦ fun x ↦ fibreNormOperator (g x)
      (g (hermitianBoundsIterate f r.val x)) (S x) (hermitianBoundsDerivative f r.val x))
    (fun r : Fin k ↦ fun x ↦ fibreNormOperator (g (hermitianBoundsIterate f r.val x))
      (g x) (U (hermitianBoundsIterate f r.val x)) (hermitianBoundsDerivative f r.val x).symm)
    (fun r ↦ continuous_restricted_iterate_operator f r.val S RS hS g gcont gpos)
    (fun r ↦ continuous_restricted_inverse_iterate_operator f r.val U RU hU g gcont gpos)
  exact ⟨a, R, ha, ha1, hR, hab, fun r hr x ↦ hRb ⟨r, hr⟩ x⟩


end
end HolomorphicAnosov.NativeOperatorPreparation










namespace HolomorphicAnosov.CompactHermitianBoundsScratch

open Set

section SeminormOperators

variable {V W Z : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]



theorem operator_le_of_pointwise (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (L : V →ₗ[ℝ] W) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v ∈ P, q (L v) ≤ C * p v) :
    fibreNormOperator p q P L ≤ C := by
  apply csSup_le
  · exact ⟨0, 0, P.zero_mem, by simp, by simp⟩
  · rintro a ⟨v, hv, hp, rfl⟩
    exact (h v hv).trans (mul_le_of_le_one_right hC hp)


theorem unit_value_le_operator (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (L : V →ₗ[ℝ] W)
    (hb : BddAbove {a : ℝ | ∃ v : V, v ∈ P ∧ p v ≤ 1 ∧ a = q (L v)})
    {v : V} (hv : v ∈ P) (hp : p v ≤ 1) :
    q (L v) ≤ fibreNormOperator p q P L :=
  le_csSup hb ⟨v, hv, hp, rfl⟩



theorem pointwise_le_operator (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (L : V →ₗ[ℝ] W)
    (hp : ∀ v : V, v ≠ 0 → 0 < p v)
    (hb : BddAbove {a : ℝ | ∃ v : V, v ∈ P ∧ p v ≤ 1 ∧ a = q (L v)})
    {v : V} (hv : v ∈ P) :
    q (L v) ≤ fibreNormOperator p q P L * p v := by
  by_cases hzero : v = 0
  · simp [hzero]
  have hpos := hp v hzero
  have hu : (p v)⁻¹ • v ∈ P := (P.restrictScalars ℝ).smul_mem _ hv
  have hunit : p ((p v)⁻¹ • v) ≤ 1 := by
    rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
    simp [hpos.ne']
  have hbound := unit_value_le_operator p q P L hb hu hunit
  rw [L.map_smul, map_smul_eq_mul,
    Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)] at hbound
  exact (inv_mul_le_iff₀ hpos).mp hbound |>.trans_eq (mul_comm _ _)



theorem operator_comp_le (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (r : Seminorm ℝ Z) (P : Submodule ℂ V) (Q : Submodule ℂ W)
    (L : V →ₗ[ℝ] W) (M : W →ₗ[ℝ] Z) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hL : ∀ v ∈ P, q (L v) ≤ C * p v)
    (hM : ∀ w ∈ Q, r (M w) ≤ D * q w)
    (hPQ : ∀ v ∈ P, L v ∈ Q) :
    fibreNormOperator p r P (M.comp L) ≤ D * C := by
  apply operator_le_of_pointwise p r P (M.comp L) (mul_nonneg hD hC)
  intro v hv
  exact (hM (L v) (hPQ v hv)).trans
    ((mul_le_mul_of_nonneg_left (hL v hv) hD).trans_eq (mul_assoc _ _ _).symm)



theorem exists_unit_vector (p : Seminorm ℝ V) (P : Submodule ℂ V)
    (hp : ∀ v : V, v ≠ 0 → 0 < p v) (hne : ∃ v : V, v ∈ P ∧ v ≠ 0) :
    ∃ v : V, v ∈ P ∧ p v = 1 := by
  obtain ⟨v, hv, hv0⟩ := hne
  have hpos := hp v hv0
  refine ⟨(p v)⁻¹ • v, (P.restrictScalars ℝ).smul_mem _ hv, ?_⟩
  rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  exact inv_mul_cancel₀ hpos.ne'



theorem exists_unit_vector_of_positive_finrank (p : Seminorm ℝ V) (P : Submodule ℂ V)
    (hp : ∀ v : V, v ≠ 0 → 0 < p v) (hrank : 0 < Module.finrank ℂ P) :
    ∃ v : V, v ∈ P ∧ p v = 1 := by
  have : Nontrivial P := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨v, hv⟩ := exists_ne (0 : P)
  apply exists_unit_vector p P hp
  refine ⟨v, v.property, ?_⟩
  intro h
  apply hv
  exact Subtype.ext h



theorem conorm_le_operator (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (L : V →ₗ[ℝ] W)
    (hb : BddAbove {a : ℝ | ∃ v : V, v ∈ P ∧ p v ≤ 1 ∧ a = q (L v)})
    (hunit : ∃ v : V, v ∈ P ∧ p v = 1) :
    fibreNormConorm p q P L ≤ fibreNormOperator p q P L := by
  obtain ⟨v, hv, hp⟩ := hunit
  apply le_trans (b := q (L v))
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro a ⟨w, _, _, rfl⟩
      exact apply_nonneg q _
    · exact ⟨v, hv, hp, rfl⟩
  · exact unit_value_le_operator p q P L hb hv hp.le


theorem operator_bot_zero (p : Seminorm ℝ V) (q : Seminorm ℝ W) (L : V →ₗ[ℝ] W) :
    fibreNormOperator p q ⊥ L = 0 := by
  simp [fibreNormOperator]



theorem endpoint_norm_comparison (p p' : Seminorm ℝ V) (q q' : Seminorm ℝ W)
    (P : Submodule ℂ V) (L : V →ₗ[ℝ] W) {c C K : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsource : ∀ v, p v ≤ C * p' v) (htarget : ∀ w, c * q' w ≤ q w)
    (hbound : ∀ v ∈ P, q (L v) ≤ K * p v) :
    fibreNormOperator p' q' P L ≤ (C / c) * K := by
  apply operator_le_of_pointwise p' q' P L (by positivity)
  intro v hv
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c * q' (L v) ≤ q (L v) := htarget (L v)
    _ ≤ K * p v := hbound v hv
    _ ≤ K * (C * p' v) := mul_le_mul_of_nonneg_left (hsource v) hK
    _ = c * ((C / c) * K * p' v) := by field_simp



theorem full_operator_le_of_decomposition (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (S U : Submodule ℂ V) (L : V →ₗ[ℝ] W) (s u : V → V) {P Cs Cu : ℝ}
    (hP : 0 ≤ P) (hCs : 0 ≤ Cs) (hCu : 0 ≤ Cu)
    (hdecomp : ∀ v, s v + u v = v)
    (hs : ∀ v, s v ∈ S) (hu : ∀ v, u v ∈ U)
    (hsp : ∀ v, p (s v) ≤ P * p v) (hup : ∀ v, p (u v) ≤ P * p v)
    (hS : ∀ v ∈ S, q (L v) ≤ Cs * p v)
    (hU : ∀ v ∈ U, q (L v) ≤ Cu * p v) :
    fibreNormOperator p q ⊤ L ≤ P * (Cs + Cu) := by
  apply operator_le_of_pointwise p q ⊤ L (by positivity)
  intro v _
  calc
    q (L v) = q (L (s v) + L (u v)) := by rw [← L.map_add, hdecomp]
    _ ≤ q (L (s v)) + q (L (u v)) := map_add_le_add q _ _
    _ ≤ Cs * p (s v) + Cu * p (u v) := add_le_add (hS _ (hs v)) (hU _ (hu v))
    _ ≤ Cs * (P * p v) + Cu * (P * p v) :=
      add_le_add (mul_le_mul_of_nonneg_left (hsp v) hCs)
        (mul_le_mul_of_nonneg_left (hup v) hCu)
    _ = P * (Cs + Cu) * p v := by ring

end SeminormOperators



theorem block_residue_decay (b : ℕ → ℝ) {k : ℕ} (hk : 0 < k) {a R : ℝ}
    (ha : 0 ≤ a) (hstep : ∀ n, b (n + k) ≤ a * b n)
    (hres : ∀ r, r < k → b r ≤ R) (n : ℕ) :
    b n ≤ R * a ^ (n / k) := by
  have hblocks : ∀ l r, r < k → b (l * k + r) ≤ R * a ^ l := by
    intro l
    induction l with
    | zero => intro r hr; simpa using hres r hr
    | succ l ih =>
      intro r hr
      have heq : (l + 1) * k + r = (l * k + r) + k := by ring
      rw [heq]
      calc
        b (l * k + r + k) ≤ a * b (l * k + r) := hstep _
        _ ≤ a * (R * a ^ l) := mul_le_mul_of_nonneg_left (ih r hr) ha
        _ = R * a ^ (l + 1) := by rw [pow_succ]; ring
  have h := hblocks (n / k) (n % k) (Nat.mod_lt n hk)
  simpa [Nat.mul_comm, Nat.div_add_mod] using h



theorem geometric_from_blocks {a q R : ℝ} {k n : ℕ} (hk : 0 < k)
    (hq : 0 < q) (hq1 : q ≤ 1) (hR : 0 ≤ R) (hqa : q ^ k = a) :
    R * a ^ (n / k) ≤ (R / q ^ (k - 1)) * q ^ n := by
  have hp := pow_pos hq (k - 1)
  have hr : n % k ≤ k - 1 := by have := Nat.mod_lt n hk; omega
  have hpow : q ^ (k - 1) ≤ q ^ (n % k) := pow_le_pow_of_le_one hq.le hq1 hr
  have hn : q ^ n = a ^ (n / k) * q ^ (n % k) := by
    conv_lhs => rw [← Nat.div_add_mod n k]
    rw [pow_add, pow_mul, hqa]
  rw [hn]
  calc
    R * a ^ (n / k) = (R / q ^ (k - 1)) *
        (a ^ (n / k) * q ^ (k - 1)) := by field_simp
    _ ≤ (R / q ^ (k - 1)) * (a ^ (n / k) * q ^ (n % k)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (pow_nonneg (by rw [← hqa]; positivity) _))
        (div_nonneg hR hp.le)



theorem exists_geometric_constants {a R : ℝ} {k : ℕ} (hk : 0 < k)
    (ha : 0 < a) (ha1 : a < 1) (hR : 1 ≤ R) :
    ∃ q D : ℝ, 0 < q ∧ q < 1 ∧ 1 ≤ D ∧ q ^ k = a ∧
      ∀ n : ℕ, R * a ^ (n / k) ≤ D * q ^ n := by
  let q : ℝ := a ^ ((k : ℝ)⁻¹)
  have hq : 0 < q := Real.rpow_pos_of_pos ha _
  have hq1 : q < 1 := Real.rpow_lt_one ha.le ha1 (by positivity)
  have hqa : q ^ k = a := Real.rpow_inv_natCast_pow ha.le hk.ne'
  have hp : 0 < q ^ (k - 1) := pow_pos hq _
  have hp1 : q ^ (k - 1) ≤ 1 := pow_le_one₀ hq.le hq1.le
  refine ⟨q, R / q ^ (k - 1), hq, hq1, ?_, hqa, ?_⟩
  · exact (le_div_iff₀ hp).mpr (by simpa using hp1.trans hR)
  · intro n
    exact geometric_from_blocks hk hq hq1.le (le_trans (by norm_num) hR) hqa

section Conorm

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]



theorem conorm_lower_of_inverse_bound (p : V → ℝ) (q : W → ℝ)
    (P : Submodule ℂ V) (L : V → W) {C : ℝ} (hC : 0 < C)
    (hunit : ∃ v : V, v ∈ P ∧ p v = 1)
    (hinv : ∀ v ∈ P, p v ≤ C * q (L v)) :
    C⁻¹ ≤ fibreNormConorm p q P L := by
  apply le_csInf
  · obtain ⟨v, hv, hp⟩ := hunit
    exact ⟨q (L v), v, hv, hp, rfl⟩
  · rintro a ⟨v, hv, hp, rfl⟩
    have ht := hinv v hv
    rw [hp] at ht
    exact (inv_le_iff_one_le_mul₀ hC).mpr (by simpa [mul_comm] using ht)

end Conorm



theorem stable_plus_unstable_le {S U A P q : ℝ} {n : ℕ}
    (hA : 0 < A) (hP : 0 ≤ P) (hq : 0 < q) (hq1 : q ≤ 1)
    (hS : S ≤ A * q ^ n) (hU : A⁻¹ * (q ^ n)⁻¹ ≤ U) :
    P * (S + U) ≤ (P * (1 + A ^ 2)) * U := by
  have hqn : 0 < q ^ n := pow_pos hq n
  have hqn1 : q ^ n ≤ 1 := pow_le_one₀ hq.le hq1
  have hU0 : 0 ≤ U := (by positivity : 0 < A⁻¹ * (q ^ n)⁻¹).le.trans hU
  have hqinv : q ^ n ≤ (q ^ n)⁻¹ := hqn1.trans ((one_le_inv₀ hqn).mpr hqn1)
  have hAU : A * (q ^ n)⁻¹ ≤ A ^ 2 * U := by
    have ht := mul_le_mul_of_nonneg_left hU (sq_nonneg A)
    calc
      A * (q ^ n)⁻¹ = A ^ 2 * (A⁻¹ * (q ^ n)⁻¹) := by field_simp
      _ ≤ A ^ 2 * U := ht
  have hSU : S ≤ A ^ 2 * U :=
    hS.trans ((mul_le_mul_of_nonneg_left hqinv hA.le).trans hAU)
  calc
    P * (S + U) ≤ P * (A ^ 2 * U + U) :=
      mul_le_mul_of_nonneg_left (add_le_add hSU (le_refl U)) hP
    _ = (P * (1 + A ^ 2)) * U := by ring



theorem final_constant_laws {c C D P q : ℝ} (hc : 0 < c) (hcC : c ≤ C)
    (hD : 1 ≤ D) (hP : 1 ≤ P) (hq : 0 < q) (hq1 : q < 1) :
    1 ≤ (C / c) * D ∧ 0 < P * (1 + ((C / c) * D) ^ 2) ∧ 1 < q⁻¹ ∧
      ∀ n : ℕ, q ^ n = (q⁻¹ ^ n)⁻¹ := by
  have hCc : 1 ≤ C / c := (le_div_iff₀ hc).mpr (by simpa using hcC)
  refine ⟨?_, ?_, (one_lt_inv₀ hq).mpr hq1, ?_⟩
  · calc
      1 ≤ D := hD
      _ ≤ (C / c) * D := le_mul_of_one_le_left (by linarith) hCc
  · have : 0 < P := lt_of_lt_of_le (by norm_num) hP
    positivity
  · intro n
    simp



theorem unit_values_bddAbove {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (p : Seminorm ℝ V) (q : Seminorm ℝ W)
    (P : Submodule ℂ V) (L : V →ₗ[ℝ] W) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v ∈ P, q (L v) ≤ C * p v) :
    BddAbove {a : ℝ | ∃ v : V, v ∈ P ∧ p v ≤ 1 ∧ a = q (L v)} := by
  refine ⟨C, ?_⟩
  rintro a ⟨v, hv, hp, rfl⟩
  exact (h v hv).trans (mul_le_of_le_one_right hC hp)

section ActualDerivatives

open scoped ContDiff
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [IsManifold (complexModel d) ∞ X]

omit [IsManifold (complexModel d) ∞ X] in
theorem actual_iterate_add (f : Biholomorph d d X X) (m n : ℕ) (x : X) :
    hermitianBoundsIterate f (m + n) x =
      hermitianBoundsIterate f n (hermitianBoundsIterate f m x) := by
  change (f : X → X)^[m + n] x = (f : X → X)^[n] ((f : X → X)^[m] x)
  rw [Nat.add_comm m n, Function.iterate_add_apply]

omit [IsManifold (complexModel d) ∞ X] in
theorem actual_iterate_zero (f : Biholomorph d d X X) (x : X) :
    hermitianBoundsIterate f 0 x = x := rfl

omit [IsManifold (complexModel d) ∞ X] in
theorem actual_derivative_zero (f : Biholomorph d d X X) (x : X)
    (v : TangentSpace (complexModel d) x) : hermitianBoundsDerivative f 0 x v = v := by
  change mfderiv (complexModel d) (complexModel d) id x v = v
  simp

omit [IsManifold (complexModel d) ∞ X] in
theorem actual_inverse_derivative_zero (f : Biholomorph d d X X) (x : X)
    (v : TangentSpace (complexModel d) x) : (hermitianBoundsDerivative f 0 x).symm v = v := by
  apply (hermitianBoundsDerivative f 0 x).injective
  exact ((hermitianBoundsDerivative f 0 x).apply_symm_apply v).trans
    (actual_derivative_zero f x v).symm



omit [IsManifold (complexModel d) ∞ X] in
theorem actual_derivative_add (f : Biholomorph d d X X) (m n : ℕ) (x : X)
    (v : TangentSpace (complexModel d) x) :
    hermitianBoundsDerivative f (m + n) x v =
      hermitianBoundsDerivative f n (hermitianBoundsIterate f m x)
        (hermitianBoundsDerivative f m x v) := by
  change mfderiv (complexModel d) (complexModel d) ((f : X → X)^[m + n]) x v =
    mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n])
      ((f : X → X)^[m] x)
      (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[m]) x v)
  rw [Nat.add_comm m n, Function.iterate_add]
  exact mfderiv_comp_apply x
    ((hermitianBoundsIterate f n).contMDiff_toFun.mdifferentiable (by simp) _)
    ((hermitianBoundsIterate f m).contMDiff_toFun.mdifferentiable (by simp) _) v



omit [IsManifold (complexModel d) ∞ X] in
theorem actual_iterate_subspace_invariant (f : Biholomorph d d X X)
    (P : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
    (hP : ∀ x, (P x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = P (f x))
    (n : ℕ) (x : X) :
    (P x).map (hermitianBoundsDerivative f n x).toLinearMap =
      P (hermitianBoundsIterate f n x) := by
  change (P x).map
    (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x).toLinearMap =
      P ((f : X → X)^[n] x)
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, mfderiv_id]
    change (P x).map LinearMap.id = P x
    exact Submodule.map_id _
  | succ n ih =>
    rw [show n + 1 = n.succ from rfl, Function.iterate_succ']
    simp only [Function.comp_apply]
    have hd : MDifferentiable (complexModel d) (complexModel d) ((f : X → X)^[n]) :=
      (hermitianBoundsIterate f n).mdifferentiable (by simp)
    rw [mfderiv_comp x (f.mdifferentiable (by simp) _) (hd x)]
    change (P x).map
      ((mfderiv (complexModel d) (complexModel d) f ((f : X → X)^[n] x)).toLinearMap.comp
        (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x).toLinearMap) = _
    rw [Submodule.map_comp, ih, hP]


omit [IsManifold (complexModel d) ∞ X] in
theorem actual_inverse_derivative_add (f : Biholomorph d d X X) (m n : ℕ) (x : X)
    (w : TangentSpace (complexModel d) (hermitianBoundsIterate f (m + n) x)) :
    (hermitianBoundsDerivative f (m + n) x).symm w =
      (hermitianBoundsDerivative f m x).symm
        ((hermitianBoundsDerivative f n (hermitianBoundsIterate f m x)).symm w) := by
  apply (hermitianBoundsDerivative f (m + n) x).injective
  rw [(hermitianBoundsDerivative f (m + n) x).apply_symm_apply,
    actual_derivative_add]
  rw [(hermitianBoundsDerivative f m x).apply_symm_apply]
  exact ((hermitianBoundsDerivative f n (hermitianBoundsIterate f m x)).apply_symm_apply w).symm



omit [IsManifold (complexModel d) ∞ X] in
theorem actual_inverse_mem_subspace (f : Biholomorph d d X X)
    (P : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
    (hP : ∀ x, (P x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = P (f x))
    (n : ℕ) (x : X)
    {w : TangentSpace (complexModel d) (hermitianBoundsIterate f n x)}
    (hw : w ∈ P (hermitianBoundsIterate f n x)) :
    (hermitianBoundsDerivative f n x).symm w ∈ P x := by
  rw [← actual_iterate_subspace_invariant f P hP n x] at hw
  obtain ⟨v, hv, heq⟩ := hw
  simpa [← heq] using hv



omit [IsManifold (complexModel d) ∞ X] in
theorem actual_stable_block_bound (f : Biholomorph d d X X)
    (P : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
    (hP : ∀ x, (P x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = P (f x))
    (g : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x))
    {k : ℕ} (hk : 0 < k) {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hblock : ∀ x v, v ∈ P x →
      g (hermitianBoundsIterate f k x) (hermitianBoundsDerivative f k x v) ≤ a * g x v)
    (hres : ∀ r, r < k → ∀ x v, v ∈ P x →
      g (hermitianBoundsIterate f r x) (hermitianBoundsDerivative f r x v) ≤ R * g x v)
    (n : ℕ) (x : X) {v : TangentSpace (complexModel d) x} (hv : v ∈ P x) :
    g (hermitianBoundsIterate f n x) (hermitianBoundsDerivative f n x v) ≤
      (R * a ^ (n / k)) * g x v := by
  have hblocks : ∀ l x (v : TangentSpace (complexModel d) x), v ∈ P x →
      g (hermitianBoundsIterate f (l * k) x) (hermitianBoundsDerivative f (l * k) x v) ≤
        a ^ l * g x v := by
    intro l
    induction l with
    | zero =>
      intro x v hv
      rw [zero_mul]
      change g x (mfderiv (complexModel d) (complexModel d) id x v) ≤ a ^ 0 * g x v
      simp
    | succ l ih =>
      intro x v hv
      have heq : (l + 1) * k = l * k + k := by ring
      rw [heq, actual_derivative_add, actual_iterate_add]
      have hmem : hermitianBoundsDerivative f (l * k) x v ∈
          P (hermitianBoundsIterate f (l * k) x) := by
        rw [← actual_iterate_subspace_invariant f P hP (l * k) x]
        exact Submodule.mem_map_of_mem hv
      have ht := hblock (hermitianBoundsIterate f (l * k) x) _ hmem
      calc
        _ ≤ a * g (hermitianBoundsIterate f (l * k) x)
            (hermitianBoundsDerivative f (l * k) x v) := ht
        _ ≤ a * (a ^ l * g x v) := mul_le_mul_of_nonneg_left (ih x v hv) ha
        _ = a ^ (l + 1) * g x v := by rw [pow_succ]; ring
  have hmem : hermitianBoundsDerivative f ((n / k) * k) x v ∈
      P (hermitianBoundsIterate f ((n / k) * k) x) := by
    rw [← actual_iterate_subspace_invariant f P hP ((n / k) * k) x]
    exact Submodule.mem_map_of_mem hv
  have ht := hres (n % k) (Nat.mod_lt n hk)
    (hermitianBoundsIterate f ((n / k) * k) x) _ hmem
  have hn : (n / k) * k + n % k = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n k
  conv_lhs => rw [← hn]
  rw [actual_derivative_add, actual_iterate_add]
  calc
    _ ≤ R * g (hermitianBoundsIterate f ((n / k) * k) x)
        (hermitianBoundsDerivative f ((n / k) * k) x v) := ht
    _ ≤ R * (a ^ (n / k) * g x v) :=
      mul_le_mul_of_nonneg_left (hblocks (n / k) x v hv) hR
    _ = _ := by ring



omit [IsManifold (complexModel d) ∞ X] in
theorem actual_inverse_block_bound (f : Biholomorph d d X X)
    (P : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
    (hP : ∀ x, (P x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = P (f x))
    (g : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x))
    {k : ℕ} (hk : 0 < k) {a R : ℝ} (ha : 0 ≤ a) (_hR : 0 ≤ R)
    (hblock : ∀ x w, w ∈ P (hermitianBoundsIterate f k x) →
      g x ((hermitianBoundsDerivative f k x).symm w) ≤
        a * g (hermitianBoundsIterate f k x) w)
    (hres : ∀ r, r < k → ∀ x w, w ∈ P (hermitianBoundsIterate f r x) →
      g x ((hermitianBoundsDerivative f r x).symm w) ≤
        R * g (hermitianBoundsIterate f r x) w)
    (n : ℕ) (x : X)
    {w : TangentSpace (complexModel d) (hermitianBoundsIterate f n x)}
    (hw : w ∈ P (hermitianBoundsIterate f n x)) :
    g x ((hermitianBoundsDerivative f n x).symm w) ≤
      (R * a ^ (n / k)) * g (hermitianBoundsIterate f n x) w := by
  have hblocks : ∀ l x (w : TangentSpace (complexModel d)
      (hermitianBoundsIterate f (l * k) x)), w ∈ P (hermitianBoundsIterate f (l * k) x) →
      g x ((hermitianBoundsDerivative f (l * k) x).symm w) ≤
        a ^ l * g (hermitianBoundsIterate f (l * k) x) w := by
    intro l
    induction l with
    | zero =>
      intro x w hw
      erw [zero_mul]
      erw [actual_inverse_derivative_zero f x w, actual_iterate_zero f x]
      simp
    | succ l ih =>
      intro x w hw
      have heq : (l + 1) * k = l * k + k := by ring
      rw [heq, actual_iterate_add] at hw
      have hmem := actual_inverse_mem_subspace f P hP k
        (hermitianBoundsIterate f (l * k) x) hw
      have ht := hblock (hermitianBoundsIterate f (l * k) x) w hw
      erw [heq, actual_inverse_derivative_add, actual_iterate_add]
      calc
        _ ≤ a ^ l * g (hermitianBoundsIterate f (l * k) x)
            ((hermitianBoundsDerivative f k (hermitianBoundsIterate f (l * k) x)).symm w) :=
          ih x _ hmem
        _ ≤ a ^ l * (a * g
            (hermitianBoundsIterate f k (hermitianBoundsIterate f (l * k) x)) w) :=
          mul_le_mul_of_nonneg_left ht (pow_nonneg ha _)
        _ = _ := by rw [pow_succ]; ring
  have hn : (n / k) * k + n % k = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n k
  have hw' : w ∈ P (hermitianBoundsIterate f (n % k)
      (hermitianBoundsIterate f ((n / k) * k) x)) := by
    rw [← actual_iterate_add, hn]
    exact hw
  have hmem := actual_inverse_mem_subspace f P hP (n % k)
    (hermitianBoundsIterate f ((n / k) * k) x) hw'
  have ht := hres (n % k) (Nat.mod_lt n hk)
    (hermitianBoundsIterate f ((n / k) * k) x) w hw'
  conv_lhs => rw [← hn]
  erw [actual_inverse_derivative_add]
  calc
    _ ≤ a ^ (n / k) * g (hermitianBoundsIterate f ((n / k) * k) x)
        ((hermitianBoundsDerivative f (n % k)
          (hermitianBoundsIterate f ((n / k) * k) x)).symm w) := hblocks _ x _ hmem
    _ ≤ a ^ (n / k) * (R * g
        (hermitianBoundsIterate f (n % k) (hermitianBoundsIterate f ((n / k) * k) x)) w) :=
      mul_le_mul_of_nonneg_left ht (pow_nonneg ha _)
    _ = _ := by rw [← actual_iterate_add, hn]; ring




omit [IsManifold (complexModel d) ∞ X] in
theorem actual_operator_decay_from_blocks (f : Biholomorph d d X X)
    (S U : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
    (hS : ∀ x, (S x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = S (f x))
    (hU : ∀ x, (U x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = U (f x))
    (g : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x))
    {k : ℕ} (hk : 0 < k) {a R : ℝ} (ha : 0 < a) (ha1 : a < 1) (hR : 1 ≤ R)
    (hblockS : ∀ x v, v ∈ S x →
      g (hermitianBoundsIterate f k x) (hermitianBoundsDerivative f k x v) ≤ a * g x v)
    (hblockU : ∀ x w, w ∈ U (hermitianBoundsIterate f k x) →
      g x ((hermitianBoundsDerivative f k x).symm w) ≤
        a * g (hermitianBoundsIterate f k x) w)
    (hresS : ∀ r, r < k → ∀ x v, v ∈ S x →
      g (hermitianBoundsIterate f r x) (hermitianBoundsDerivative f r x v) ≤ R * g x v)
    (hresU : ∀ r, r < k → ∀ x w, w ∈ U (hermitianBoundsIterate f r x) →
      g x ((hermitianBoundsDerivative f r x).symm w) ≤
        R * g (hermitianBoundsIterate f r x) w) :
    ∃ q D : ℝ, 0 < q ∧ q < 1 ∧ 1 ≤ D ∧ ∀ n x,
      fibreNormOperator (g x) (g (hermitianBoundsIterate f n x)) (S x)
        (hermitianBoundsDerivative f n x) ≤ D * q ^ n ∧
      fibreNormOperator (g (hermitianBoundsIterate f n x)) (g x)
        (U (hermitianBoundsIterate f n x)) (hermitianBoundsDerivative f n x).symm ≤
          D * q ^ n := by
  obtain ⟨q, D, hq, hq1, hD, _, hgeometric⟩ := exists_geometric_constants hk ha ha1 hR
  have hR0 : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR
  have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD
  refine ⟨q, D, hq, hq1, hD, ?_⟩
  intro n x
  constructor
  · apply operator_le_of_pointwise (g x) (g (hermitianBoundsIterate f n x)) (S x)
      ((hermitianBoundsDerivative f n x).toContinuousLinearMap.restrictScalars ℝ).toLinearMap
      (mul_nonneg hD0 (pow_nonneg hq.le _))
    intro v hv
    exact (actual_stable_block_bound f S hS g hk ha.le hR0 hblockS hresS n x hv).trans
      (mul_le_mul_of_nonneg_right (hgeometric n) (apply_nonneg (g x) v))
  · apply operator_le_of_pointwise (g (hermitianBoundsIterate f n x)) (g x)
      (U (hermitianBoundsIterate f n x))
      ((hermitianBoundsDerivative f n x).symm.toContinuousLinearMap.restrictScalars ℝ).toLinearMap
      (mul_nonneg hD0 (pow_nonneg hq.le _))
    intro w hw
    exact (actual_inverse_block_bound f U hU g hk ha.le hR0 hblockU hresU n x hw).trans
      (mul_le_mul_of_nonneg_right (hgeometric n)
        (apply_nonneg (g (hermitianBoundsIterate f n x)) w))



omit [IsManifold (complexModel d) ∞ X] in
theorem actual_conorm_lower_from_inverse (f : Biholomorph d d X X)
    (U : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
    (hU : ∀ x, (U x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = U (f x))
    (p : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x))
    (n : ℕ) (x : X) (hrank : 0 < Module.finrank ℂ (U x))
    (hp : ∀ v, v ≠ 0 → 0 < p x v) {C : ℝ} (hC : 0 < C)
    (hinv : ∀ w, w ∈ U (hermitianBoundsIterate f n x) →
      p x ((hermitianBoundsDerivative f n x).symm w) ≤
        C * p (hermitianBoundsIterate f n x) w) :
    C⁻¹ ≤ fibreNormConorm (p x) (p (hermitianBoundsIterate f n x)) (U x)
      (hermitianBoundsDerivative f n x) := by
  apply conorm_lower_of_inverse_bound (p x) (p (hermitianBoundsIterate f n x)) (U x)
    (hermitianBoundsDerivative f n x) hC
    (exists_unit_vector_of_positive_finrank (p x) (U x) hp hrank)
  intro v hv
  have hmem : hermitianBoundsDerivative f n x v ∈ U (hermitianBoundsIterate f n x) := by
    rw [← actual_iterate_subspace_invariant f U hU n x]
    exact Submodule.mem_map_of_mem hv
  have ht := hinv _ hmem
  rw [(hermitianBoundsDerivative f n x).symm_apply_apply] at ht
  exact ht

end ActualDerivatives


end HolomorphicAnosov.CompactHermitianBoundsScratch

namespace HolomorphicAnosov.CompactHermitianAssembly
open Set
open scoped ContDiff
open CompactHermitianBoundsScratch NativeOperatorPreparation
  HermitianFibreAlgebra NativeSplittingPreparation
noncomputable section
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
attribute [local instance] complex_isManifold_real




theorem native_derivative_pointwise_bound (F : Biholomorph d d X X)
    (g : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x))
    (gcont : Continuous (fun z : TangentBundle (complexModel d) X ↦ g z.proj z.snd))
    (gpos : ∀ x v, v ≠ 0 → 0 < g x v) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x v,
      g (F x) (mfderiv (complexModel d) (complexModel d) F x v) ≤ R * g x v := by
  let p (x : X) : Seminorm ℝ (TangentSpace (complexModel d) x) :=
    (g (F x)).comp
      ((mfderiv (complexModel d) (complexModel d) F x).toLinearMap.restrictScalars ℝ)
  have hp : Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd) :=
    gcont.comp (F.contMDiff_toFun.continuous_tangentMap (by simp))
  exact Preparation.uniform_tangent_seminorm_upper_bound p g hp gcont gpos



theorem native_unit_values_bddAbove (f : Biholomorph d d X X)
    (g : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x))
    (gcont : Continuous (fun z : TangentBundle (complexModel d) X ↦ g z.proj z.snd))
    (gpos : ∀ x v, v ≠ 0 → 0 < g x v) (n : ℕ) (x : X)
    (P : Submodule ℂ (TangentSpace (complexModel d) x))
    (Q : Submodule ℂ (TangentSpace (complexModel d) (hermitianBoundsIterate f n x))) :
    BddAbove {a : ℝ | ∃ v, v ∈ P ∧ g x v ≤ 1 ∧
      a = g (hermitianBoundsIterate f n x) (hermitianBoundsDerivative f n x v)} ∧
    BddAbove {a : ℝ | ∃ w, w ∈ Q ∧ g (hermitianBoundsIterate f n x) w ≤ 1 ∧
      a = g x ((hermitianBoundsDerivative f n x).symm w)} := by
  obtain ⟨R, hR, hbound⟩ := native_derivative_pointwise_bound
    (hermitianBoundsIterate f n) g gcont gpos
  obtain ⟨T, hT, ht⟩ := native_derivative_pointwise_bound
    (hermitianBoundsIterate f n).symm g gcont gpos
  constructor
  · refine ⟨R, ?_⟩
    rintro a ⟨v, _, hv, rfl⟩
    exact (hbound x v).trans (mul_le_of_le_one_right (by linarith) hv)
  · refine ⟨T, ?_⟩
    rintro a ⟨w, _, hw, rfl⟩
    have htw := ht (hermitianBoundsIterate f n x) w
    change g (tangentMap (complexModel d) (complexModel d)
      (hermitianBoundsIterate f n).symm ⟨hermitianBoundsIterate f n x, w⟩).proj
      (tangentMap (complexModel d) (complexModel d)
        (hermitianBoundsIterate f n).symm ⟨hermitianBoundsIterate f n x, w⟩).snd ≤
      T * g (hermitianBoundsIterate f n x) w at htw
    rw [inverse_derivative_total_eq] at htw
    exact htw.trans (mul_le_of_le_one_right (by linarith) hw)


end
end HolomorphicAnosov.CompactHermitianAssembly


namespace HolomorphicAnosov
universe u
noncomputable section
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
variable [IsManifold (complexModel d) ∞ X]
attribute [local instance] complex_isManifold_real
open Set
open CompactHermitianBoundsScratch NativeOperatorPreparation
  HermitianFibreAlgebra NativeSplittingPreparation CompactHermitianAssembly





































theorem compact_anosov_hermitian_operator_bounds
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    (f : Biholomorph d d X X)
    (S U : ∀ x : X, Submodule ℂ (TangentSpace (complexModel d) x))
    (RS RU : ContinuousRealTangentSubbundle (realModel d) X)
    (hS : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = RS.toDistribution x)
    (hU : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap = RU.toDistribution x)
    (hsplit : ∀ x, IsCompl (S x) (U x))
    (hSinv : ∀ x, (S x).map (mfderiv (complexModel d) (complexModel d) f x).toLinearMap =
      S (f x))
    (hUinv : ∀ x, (U x).map (mfderiv (complexModel d) (complexModel d) f x).toLinearMap =
      U (f x))
    (hrank : ∀ x, 0 < Module.finrank ℂ (U x))
    (g : ∀ x : X, Seminorm ℝ (TangentSpace (complexModel d) x))
    (gpos : ∀ x v, v ≠ 0 → 0 < g x v)
    (gcont : Continuous (fun z : TangentBundle (complexModel d) X ↦ g z.proj z.snd))
    (k : ℕ) (hk : 1 ≤ k)
    (hcontract : ∀ x,
      fibreNormOperator (g x) (g (hermitianBoundsIterate f k x)) (S x)
          (hermitianBoundsDerivative f k x) < 1 ∧
        fibreNormOperator (g (hermitianBoundsIterate f k x)) (g x)
          (U (hermitianBoundsIterate f k x)) (hermitianBoundsDerivative f k x).symm < 1)
    (h : HermitianTangentMetricCore d X) (hsmooth : IsSmoothHermitianTangentMetric h) :
    ∃ A B lam : ℝ, 1 ≤ A ∧ 0 < B ∧ 1 < lam ∧ ∀ (n : ℕ) (x : X),
      fibreNormOperator (hermitianBoundsNorm h x)
          (hermitianBoundsNorm h (hermitianBoundsIterate f n x)) (S x)
          (hermitianBoundsDerivative f n x) ≤ A * (lam ^ n)⁻¹ ∧
        fibreNormOperator (hermitianBoundsNorm h (hermitianBoundsIterate f n x))
          (hermitianBoundsNorm h x) (U (hermitianBoundsIterate f n x))
          (hermitianBoundsDerivative f n x).symm ≤ A * (lam ^ n)⁻¹ ∧
        A⁻¹ * lam ^ n ≤ fibreNormConorm (hermitianBoundsNorm h x)
          (hermitianBoundsNorm h (hermitianBoundsIterate f n x)) (U x)
          (hermitianBoundsDerivative f n x) ∧
        fibreNormOperator (hermitianBoundsNorm h x)
          (hermitianBoundsNorm h (hermitianBoundsIterate f n x)) ⊤
          (hermitianBoundsDerivative f n x) ≤
            B * fibreNormOperator (hermitianBoundsNorm h x)
              (hermitianBoundsNorm h (hermitianBoundsIterate f n x)) (U x)
              (hermitianBoundsDerivative f n x) := by
  classical
  let p := hermitianBoundsRealSeminorm h
  have pp : ∀ x v, v ≠ 0 → 0 < p x v := fun x _ hv ↦ coreLength_pos (h x) hv
  have pc : Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd) :=
    Preparation.continuous_hermitian_tangent_norm h hsmooth
  have gb n x := native_unit_values_bddAbove f g gcont gpos n x
    (S x) (U (hermitianBoundsIterate f n x))
  have gpS : ∀ n x v, v ∈ S x →
      g (hermitianBoundsIterate f n x) (hermitianBoundsDerivative f n x v) ≤
        fibreNormOperator (g x) (g (hermitianBoundsIterate f n x)) (S x)
          (hermitianBoundsDerivative f n x) * g x v := by
    intro n x v hv
    exact pointwise_le_operator (g x) (g (hermitianBoundsIterate f n x)) (S x)
      ((hermitianBoundsDerivative f n x).toLinearMap.restrictScalars ℝ)
      (gpos x) (gb n x).1 hv
  have gpU : ∀ n x w, w ∈ U (hermitianBoundsIterate f n x) →
      g x ((hermitianBoundsDerivative f n x).symm w) ≤
        fibreNormOperator (g (hermitianBoundsIterate f n x)) (g x)
          (U (hermitianBoundsIterate f n x)) (hermitianBoundsDerivative f n x).symm *
            g (hermitianBoundsIterate f n x) w := by
    intro n x w hw
    exact pointwise_le_operator (g (hermitianBoundsIterate f n x)) (g x)
      (U (hermitianBoundsIterate f n x))
      ((hermitianBoundsDerivative f n x).symm.toLinearMap.restrictScalars ℝ)
      (gpos _) (gb n x).2 hw
  obtain ⟨a, R, ha, ha1, hR, hblock, hres⟩ :=
    native_compact_block_residue_bounds f S U RS RU hS hU g gcont gpos k hcontract
  obtain ⟨q, D, hq, hq1, hD, hdecay⟩ := actual_operator_decay_from_blocks
    f S U hSinv hUinv g (by omega : 0 < k) ha ha1 hR
    (fun x v hv ↦ (gpS k x v hv).trans
      (mul_le_mul_of_nonneg_right (hblock x).1 (apply_nonneg (g x) v)))
    (fun x w hw ↦ (gpU k x w hw).trans
      (mul_le_mul_of_nonneg_right (hblock x).2 (apply_nonneg (g _) w)))
    (fun r hr x v hv ↦ (gpS r x v hv).trans
      (mul_le_mul_of_nonneg_right (hres r hr x).1 (apply_nonneg (g x) v)))
    (fun r hr x w hw ↦ (gpU r x w hw).trans
      (mul_le_mul_of_nonneg_right (hres r hr x).2 (apply_nonneg (g _) w)))
  obtain ⟨c, C, hc, hcC, hC, hcomp⟩ :=
    Preparation.uniform_hermitian_tangent_norm_comparison g gcont gpos h hsmooth
  obtain ⟨K, hK, hproj⟩ := NativeProjectionBounds.uniform_original_hermitian_projection_bounds
    S U hsplit RS RU hS hU h hsmooth
  let A := (C / c) * D
  obtain ⟨hA, hB, hlam, hpow⟩ := final_constant_laws hc hcC hD hK hq hq1
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hD0 : 0 ≤ D := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hsbound : ∀ n x, fibreNormOperator (p x) (p (hermitianBoundsIterate f n x))
      (S x) (hermitianBoundsDerivative f n x) ≤ A * q ^ n := by
    intro n x
    calc
      _ ≤ (C / c) * (D * q ^ n) := endpoint_norm_comparison
        (g x) (p x) (g (hermitianBoundsIterate f n x)) (p (hermitianBoundsIterate f n x))
        (S x) ((hermitianBoundsDerivative f n x).toLinearMap.restrictScalars ℝ)
        hc hC0 (by positivity) (fun v ↦ (hcomp x v).2)
        (fun w ↦ (hcomp _ w).1)
        (fun v hv ↦ (gpS n x v hv).trans
          (mul_le_mul_of_nonneg_right (hdecay n x).1 (apply_nonneg (g x) v)))
      _ = A * q ^ n := by dsimp [A]; ring
  have hubound : ∀ n x, fibreNormOperator (p (hermitianBoundsIterate f n x)) (p x)
      (U (hermitianBoundsIterate f n x)) (hermitianBoundsDerivative f n x).symm ≤
        A * q ^ n := by
    intro n x
    calc
      _ ≤ (C / c) * (D * q ^ n) := endpoint_norm_comparison
        (g (hermitianBoundsIterate f n x)) (p (hermitianBoundsIterate f n x)) (g x) (p x)
        (U (hermitianBoundsIterate f n x))
        ((hermitianBoundsDerivative f n x).symm.toLinearMap.restrictScalars ℝ)
        hc hC0 (by positivity) (fun w ↦ (hcomp _ w).2)
        (fun v ↦ (hcomp x v).1)
        (fun w hw ↦ (gpU n x w hw).trans
          (mul_le_mul_of_nonneg_right (hdecay n x).2 (apply_nonneg (g _) w)))
      _ = A * q ^ n := by dsimp [A]; ring
  refine ⟨A, K * (1 + A ^ 2), q⁻¹, hA, hB, hlam, ?_⟩
  intro n x
  have hb := native_unit_values_bddAbove f p pc pp n x (U x)
    (U (hermitianBoundsIterate f n x))
  have hbS := (native_unit_values_bddAbove f p pc pp n x (S x)
    (U (hermitianBoundsIterate f n x))).1
  have hinv : ∀ w, w ∈ U (hermitianBoundsIterate f n x) →
      p x ((hermitianBoundsDerivative f n x).symm w) ≤
        (A * q ^ n) * p (hermitianBoundsIterate f n x) w := by
    intro w hw
    exact (pointwise_le_operator (p _) (p x) (U (hermitianBoundsIterate f n x))
      ((hermitianBoundsDerivative f n x).symm.toLinearMap.restrictScalars ℝ)
      (pp _) hb.2 hw).trans
      (mul_le_mul_of_nonneg_right (hubound n x) (apply_nonneg (p _) w))
  have hcon := actual_conorm_lower_from_inverse f U hUinv p n x (hrank x) (pp x)
    (mul_pos hApos (pow_pos hq n)) hinv
  have hunit := exists_unit_vector_of_positive_finrank (p x) (U x) (pp x) (hrank x)
  have hcop := conorm_le_operator (p x) (p _) (U x)
    ((hermitianBoundsDerivative f n x).toLinearMap.restrictScalars ℝ) hb.1 hunit
  have hUnonneg : 0 ≤ fibreNormOperator (p x) (p _) (U x)
      (hermitianBoundsDerivative f n x) :=
    (by simpa using (unit_value_le_operator (p x) (p _) (U x)
      ((hermitianBoundsDerivative f n x).toLinearMap.restrictScalars ℝ)
      hb.1 (U x).zero_mem (by simp : p x (0 : TangentSpace (complexModel d) x) ≤ 1)))
  have hSnonneg : 0 ≤ fibreNormOperator (p x) (p _) (S x)
      (hermitianBoundsDerivative f n x) :=
    (by simpa using (unit_value_le_operator (p x) (p _) (S x)
      ((hermitianBoundsDerivative f n x).toLinearMap.restrictScalars ℝ)
      hbS (S x).zero_mem (by simp : p x (0 : TangentSpace (complexModel d) x) ≤ 1)))
  have hfull := full_operator_le_of_decomposition (p x) (p _) (S x) (U x)
    ((hermitianBoundsDerivative f n x).toLinearMap.restrictScalars ℝ)
    (stableProjection S U hsplit x) (unstableProjection S U hsplit x)
    hK0 hSnonneg hUnonneg (projections_add S U hsplit x)
    (fun v ↦ (projections_mem S U hsplit x v).1)
    (fun v ↦ (projections_mem S U hsplit x v).2)
    (fun v ↦ (hproj x v).1) (fun v ↦ (hproj x v).2)
    (fun v hv ↦ pointwise_le_operator (p x) (p _) (S x)
      ((hermitianBoundsDerivative f n x).toLinearMap.restrictScalars ℝ) (pp x) hbS hv)
    (fun v hv ↦ pointwise_le_operator (p x) (p _) (U x)
      ((hermitianBoundsDerivative f n x).toLinearMap.restrictScalars ℝ) (pp x) hb.1 hv)
  have hlower : A⁻¹ * (q ^ n)⁻¹ ≤ fibreNormOperator (p x) (p _) (U x)
      (hermitianBoundsDerivative f n x) := by
    simpa [mul_inv_rev, mul_comm] using hcon.trans hcop
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [p, hermitianBoundsRealSeminorm_coe, ← hpow n] using hsbound n x
  · simpa only [p, hermitianBoundsRealSeminorm_coe, ← hpow n] using hubound n x
  · simpa only [p, hermitianBoundsRealSeminorm_coe, mul_inv_rev, mul_comm, inv_pow] using hcon
  · exact hfull.trans (stable_plus_unstable_le hApos hK0 hq hq1.le (hsbound n x) hlower)


end
end HolomorphicAnosov

