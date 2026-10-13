import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Local holomorphic tangent fields extending prescribed fibre vectors. -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace Bundle
open scoped ContDiff Manifold
universe u

/-- A subbundle vector and an arbitrary tangent vector extend to holomorphic fields on a common
neighborhood inside a prescribed open set, with the first field valued in the subbundle.
(Demailly, V §11, p. 267; Zhang, Lemma 2.4, eq. (13), p. 7) -/
theorem holomorphic_tangent_field_extension
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hU : IsHolomorphicTangentSubbundle r U)
    (V : Opens X) (x : X) (hx : x ∈ V)
    (v w : TangentSpace (complexModel d) x) (hv : v ∈ U x) :
    ∃ (W : Opens X) (Y Z : (y : X) → TangentSpace (complexModel d) y),
      x ∈ W ∧ W ≤ V ∧ Y x = v ∧ Z x = w ∧
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun y ↦ (⟨y, Y y⟩ : TangentBundle (complexModel d) X)) W ∧
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun y ↦ (⟨y, Z y⟩ : TangentBundle (complexModel d) X)) W ∧
      ∀ y ∈ W, Y y ∈ U y := by
  classical
  obtain ⟨O, s, hxO, hs, hspan⟩ := hU x
  have hv' : v ∈ Submodule.span ℂ (range (fun i ↦ s i x)) := by
    rw [hspan x hxO]
    exact hv
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv'
  let Y (y : X) := ∑ i, a i • s i y
  let e := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let b := e.continuousLinearMapAt ℂ x w
  let Z (y : X) := e.symmL ℂ y b
  let W : Opens X := ⟨O ∩ e.baseSet ∩ V, (hs.1.inter e.open_baseSet).inter V.isOpen⟩
  have hxE : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  refine ⟨W, Y, Z, ⟨⟨hxO, hxE⟩, hx⟩, (fun _ hy ↦ hy.2), ha, ?_, ?_, ?_, ?_⟩
  · exact e.symmL_continuousLinearMapAt hxE w
  · exact ContMDiffOn.sum_section (fun i _ ↦
      ((hs.2.1 i).mono (fun _ hy ↦ hy.1.1)).const_smul_section (a := a i))
  · apply (e.contMDiffOn_section_iff W.isOpen (fun _ hy ↦ hy.1.2)).mpr
    apply (contMDiffOn_const (c := b)).congr
    intro y hy
    rw [← e.continuousLinearMapAt_apply_of_mem ℂ hy.1.2]
    exact e.continuousLinearMapAt_symmL hy.1.2 b
  · intro y hy
    apply Submodule.sum_mem
    intro i _
    apply (U y).smul_mem
    rw [← hspan y hy.1.1]
    exact Submodule.subset_span (mem_range_self i)

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
