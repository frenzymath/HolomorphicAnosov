import HolomorphicAnosov.Paper.Zhang.HolomorphicTangentFieldSmooth
import HolomorphicAnosov.Paper.Zhang.CompatibleDifferenceOnSmoothField
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open Set TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection












theorem compatible_difference_on_subbundle
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)} {r : ℕ}
    (hU : IsHolomorphicTangentSubbundle r U)
    (D D' : Connection U) (hD : IsCompatible D) (hD' : IsCompatible D')
    (V : Opens X) (e : HolomorphicFrame U V) (x : X) (hx : x ∈ V)
    (v : TangentSpace (complexModel d) x) (hv : v ∈ U x) :
    D'.form V e x (complexTangentToReal d x v) =
      D.form V e x (complexTangentToReal d x v) := by
  classical
  obtain ⟨O, s, hxO, hs, hspan⟩ := hU x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (show v ∈ Submodule.span ℂ (Set.range (fun i ↦ s i x)) by rw [hspan x hxO]; exact hv)
  let Y : (y : X) → TangentSpace (complexModel d) y := fun y ↦ ∑ i, c i • s i y
  have hY : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨y, Y y⟩ : TangentBundle (complexModel d) X)) O :=
    ContMDiffOn.sum_section (fun i _ ↦ (hs.2.1 i).const_smul_section)
  obtain ⟨W, Z, hWo, hxW, hWV, hZ, hproj⟩ := e.holomorphic x hx
  let A : Opens X := ⟨W ∩ O, hWo.inter hs.1⟩
  have hxA : x ∈ A := ⟨hxW, hxO⟩
  have hAV : ∀ y ∈ A, y ∈ V := fun y hy ↦ hWV hy.1
  let eA : HolomorphicFrame U A :=
    { sectionValue := e.sectionValue
      holomorphic := fun y hy ↦ ⟨A, Z, A.isOpen, hy, Subset.rfl,
        hZ.mono inter_subset_left, fun z hz ↦ hproj z hz.1⟩
      coordinate := fun y hy ↦ e.coordinate y (hAV y hy)
      normalized := fun y hy ↦ e.normalized y (hAV y hy) }
  have hYA : IsSmoothTangentField A Y :=
    holomorphic_tangent_field_smooth (hY.mono inter_subset_right)
  have hZA : IsSmoothTangentField A Z :=
    holomorphic_tangent_field_smooth (hZ.mono inter_subset_left)
  have hYU : ∀ y ∈ A, Y y ∈ U y := by
    intro y hy
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    rw [← hspan y hy.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcoef : eA.coefficient (fun y ↦ projection U y (Z y)) x = 1 := by
    simp only [HolomorphicFrame.coefficient, dite_eq_left hxA]
    change e.coordinate x (hAV x hxA) (projection U x (Z x)) = 1
    rw [hproj x hxW]
    exact e.normalized x _
  have he := compatible_difference_on_smooth_field D D' hD hD' A eA Y Z
    hYA hZA hYU x hxA (by rw [hcoef]; exact one_ne_zero)
  have hdif : D'.form V e x - D.form V e x = D'.form A eA x - D.form A eA x := by
    rw [D'.gauge V A e eA x hx hxA, D.gauge V A e eA x hx hxA]
    abel
  have hvY : Y x = v := hc
  apply sub_eq_zero.mp
  have hev := congrArg (fun L ↦ L (complexTangentToReal d x v)) hdif
  simpa only [sub_apply, ← hvY, he, sub_self] using hev

end HolomorphicAnosov
