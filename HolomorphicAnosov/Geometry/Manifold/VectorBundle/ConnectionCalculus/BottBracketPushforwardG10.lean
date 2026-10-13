import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! # Pushforward of smooth tangent fields and the Bott bracket Source: Zhang §2.1 equation (5), p.5, and naturality of the real Lie bracket. The pushforward is the actual complex differential, identified with pullback along the inverse biholomorphism. The real bracket naturality theorem is applied to the fields and to their imaginary multiples. -/

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace HolomorphicAnosov.ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The actual differential pushforward (Zhang, equation (5), p.5). -/
def pushTangentField (f : Biholomorph d d X X)
    (Y : (x : X) → TangentSpace (complexModel d) x)
    (y : X) : TangentSpace (complexModel d) y :=
  mfderiv (complexModel d) (complexModel d) f (f.symm y) (Y (f.symm y))

omit [IsManifold (complexModel d) ∞ X] in
/-- Differentiating both inverse identities identifies the inverse differential. -/
lemma inverse_mfderiv_symm (f : Biholomorph d d X X) (y : X) :
    (mfderiv (realModel d) (realModel d) f.symm y).inverse =
      mfderiv (realModel d) (realModel d) f (f.symm y) := by
  have hf : MDifferentiable (realModel d) (realModel d) f :=
    f.toReal.contMDiff.mdifferentiable (by simp)
  have hg : MDifferentiable (realModel d) (realModel d) f.symm :=
    f.toReal.symm.contMDiff.mdifferentiable (by simp)
  have hfg : (f ∘ f.symm : X → X) = id := funext f.apply_symm_apply
  have hgf : (f.symm ∘ f : X → X) = id := funext f.symm_apply_apply
  have h₁ := mfderiv_comp (I := realModel d) (I' := realModel d)
    (I'' := realModel d) y (hf (f.symm y)) (hg y)
  have h₂ := mfderiv_comp (I := realModel d) (I' := realModel d)
    (I'' := realModel d) (f.symm y) (hg (f (f.symm y))) (hf (f.symm y))
  rw [hfg, mfderiv_id] at h₁
  rw [hgf, mfderiv_id, f.apply_symm_apply] at h₂
  exact ContinuousLinearMap.inverse_eq h₂.symm h₁.symm

/-- Differential pushforward is real vector-field pullback by the inverse. -/
lemma pushTangentField_eq_mpullback (f : Biholomorph d d X X)
    (Y : (x : X) → TangentSpace (complexModel d) x) :
    (fun y ↦ complexTangentToReal d y (pushTangentField f Y y)) =
      VectorField.mpullback (realModel d) (realModel d) f.symm
        (fun x ↦ complexTangentToReal d x (Y x)) := by
  funext y
  rw [VectorField.mpullback_apply, inverse_mfderiv_symm, f.real_mfderiv_eq_complex]
  rfl

/-- Smoothness is preserved on the inverse image of the original domain. -/
theorem smooth_pushTangentField (f : Biholomorph d d X X)
    {V : Set X} {Y : (x : X) → TangentSpace (complexModel d) x}
    (hY : QuotientLineConnection.IsSmoothTangentField V Y) :
    QuotientLineConnection.IsSmoothTangentField (f.symm ⁻¹' V) (pushTangentField f Y) := by
  unfold QuotientLineConnection.IsSmoothTangentField at hY ⊢
  have h := hY.mpullback_vectorField_preimage f.toReal.symm.contMDiff
    (fun y hy ↦ f.toReal.symm.isInvertible_mfderiv (by simp)) (by simp)
  convert h using 1
  · funext y
    exact congrArg (fun v ↦ (⟨y, v⟩ : TangentBundle (realModel d) X))
      (congrFun (pushTangentField_eq_mpullback f Y) y)
  · rfl


/-- Multiplication by a constant complex scalar preserves real smoothness of tangent fields on an open domain. -/
theorem smoothTangentField_const_smul {V : Set X} (hV : IsOpen V)
    {Y : (x : X) → TangentSpace (complexModel d) x}
    (hY : QuotientLineConnection.IsSmoothTangentField V Y) (a : ℂ) :
    QuotientLineConnection.IsSmoothTangentField V (fun x ↦ a • Y x) := by
  intro x hx
  let er := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) x
  have hc := (er.contMDiffAt_section_iff
    (FiberBundle.mem_baseSet_trivializationAt' x)).mp
    (hY.contMDiffAt (hV.mem_nhds hx))
  apply ContMDiffAt.contMDiffWithinAt
  apply (er.contMDiffAt_section_iff
    (FiberBundle.mem_baseSet_trivializationAt' x)).mpr
  let L : ComplexModel d →L[ℝ] ComplexModel d :=
    (a • ContinuousLinearMap.id ℂ (ComplexModel d)).restrictScalars ℝ
  have hca := L.contMDiff.contMDiffAt.comp x hc
  apply hca.congr_of_eventuallyEq
  filter_upwards [(chartAt (ComplexModel d) x).open_source.mem_nhds
    (mem_chart_source (ComplexModel d) x)] with y hy
  change tangentCoordChange (realModel d) y x y (a • Y y) =
    a • tangentCoordChange (realModel d) y x y (Y y)
  rw [complexTangentCoordChange_restrictScalars y x y
    ⟨mem_extChartAt_source (I := complexModel d) y, by simpa only [extChartAt_source] using hy⟩]
  exact (tangentCoordChange (complexModel d) y x y).map_smul a (Y y)

/-- Naturality of the real bracket for the actual complex differential pushforward. -/
lemma realBracket_pushTangentField (f : Biholomorph d d X X)
    {V : Set X} (hV : IsOpen V)
    {Y Z : (x : X) → TangentSpace (complexModel d) x}
    (hY : QuotientLineConnection.IsSmoothTangentField V Y)
    (hZ : QuotientLineConnection.IsSmoothTangentField V Z)
    {x : X} (hx : x ∈ V) :
    VectorField.mlieBracket (realModel d)
      (fun y ↦ complexTangentToReal d y (pushTangentField f Y y))
      (fun y ↦ complexTangentToReal d y (pushTangentField f Z y)) (f x) =
    mfderiv (complexModel d) (complexModel d) f x
      (VectorField.mlieBracket (realModel d)
        (fun y ↦ complexTangentToReal d y (Y y))
        (fun y ↦ complexTangentToReal d y (Z y)) x) := by
  have : IsManifold (realModel d) (minSmoothness ℝ 2) X :=
    IsManifold.of_le (n := ∞) (by simp)
  have hy := (hY.contMDiffAt (hV.mem_nhds hx)).mdifferentiableAt (by simp)
  have hz := (hZ.contMDiffAt (hV.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := VectorField.mpullback_mlieBracket
    (f := (f.symm : X → X)) (x₀ := f x)
    (by simpa only [f.symm_apply_apply] using hy)
    (by simpa only [f.symm_apply_apply] using hz)
    (f.toReal.symm.contMDiff.contMDiffAt) (by simp)
  rw [pushTangentField_eq_mpullback, pushTangentField_eq_mpullback]
  rw [← h, VectorField.mpullback_apply, inverse_mfderiv_symm,
    f.symm_apply_apply, f.real_mfderiv_eq_complex]
  rfl

/-- The native Bott bracket commutes with the biholomorphism's differential (Zhang, §2.1 (5), p.5). -/
theorem bottBracket_pushTangentField (f : Biholomorph d d X X)
    {V : Set X} (hV : IsOpen V)
    {Y Z : (x : X) → TangentSpace (complexModel d) x}
    (hY : QuotientLineConnection.IsSmoothTangentField V Y)
    (hZ : QuotientLineConnection.IsSmoothTangentField V Z)
    {x : X} (hx : x ∈ V) :
    QuotientLineConnection.bottBracket (pushTangentField f Y) (pushTangentField f Z) (f x) =
      mfderiv (complexModel d) (complexModel d) f x
        (QuotientLineConnection.bottBracket Y Z x) := by
  have h := realBracket_pushTangentField f hV hY hZ hx
  have hi := realBracket_pushTangentField f hV
    (smoothTangentField_const_smul hV hY Complex.I)
    (smoothTangentField_const_smul hV hZ Complex.I) hx
  have hI (T : (x : X) → TangentSpace (complexModel d) x) :
      pushTangentField f (fun x ↦ Complex.I • T x) =
        fun y ↦ Complex.I • pushTangentField f T y := by
    funext y
    exact map_smul _ _ _
  rw [hI Y, hI Z] at hi
  unfold QuotientLineConnection.bottBracket
  change (1 / 2 : ℂ) • (_ - _) =
    mfderiv (complexModel d) (complexModel d) f x ((1 / 2 : ℂ) • (_ - _))
  rw [h, hi, map_smul]
  congr 1
  exact (map_sub (mfderiv (complexModel d) (complexModel d) f x) _ _).symm

end HolomorphicAnosov.ConnectionCalculus
