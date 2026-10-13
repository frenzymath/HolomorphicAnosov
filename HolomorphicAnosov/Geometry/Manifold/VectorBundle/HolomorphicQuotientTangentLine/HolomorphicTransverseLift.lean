import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-! Local holomorphic transverse sections for holomorphic tangent subbundles of codimension one
(Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- A holomorphic tangent subbundle of rank `d - 1` admits a local holomorphic transverse tangent
section around every point (Zhang, p.4, Lemma 2.4). -/
theorem exists_holomorphic_transverse_lift
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] (hd : 1 ≤ d)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU : IsHolomorphicTangentSubbundle (d - 1) U) (x : X) :
    ∃ (W : TopologicalSpace.Opens X) (T : (y : X) → TangentSpace (complexModel d) y),
      x ∈ W ∧
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun y ↦ (⟨y, T y⟩ : TangentBundle (complexModel d) X)) W ∧
      ∀ y ∈ W, T y ∉ U y := by
  classical
  obtain ⟨V, s, hxV, hs, hspan⟩ := hU x
  let e := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let B := V ∩ e.baseSet
  have hB : IsOpen B := hs.1.inter e.open_baseSet
  have hxbase : x ∈ e.baseSet := by
    simp [e, TangentBundle.trivializationAt_baseSet]
  have hxB : x ∈ B := ⟨hxV, hxbase⟩
  let C (y : X) := e.continuousLinearMapAt ℂ y
  let Y (i : Fin (d - 1)) (y : X) := C y (s i y)
  have hY : ∀ i, ContinuousOn (Y i) B := by
    intro i
    have hcoeff := (e.contMDiffOn_section_iff hB Set.inter_subset_right).mp
      ((hs.2.1 i).mono Set.inter_subset_left)
    have heq : Set.EqOn (Y i) (fun y ↦ (e ⟨y, s i y⟩).2) B := by
      intro y hy
      exact e.continuousLinearMapAt_apply_of_mem ℂ hy.2 _
    exact hcoeff.continuousOn.congr (fun y hy ↦ heq hy)
  have hLI : ∀ y ∈ B, LinearIndependent ℂ (fun i ↦ Y i y) := by
    intro y hy
    exact (hs.2.2 y hy.1).map' (C y).toLinearMap
      (LinearMap.ker_eq_bot.mpr (Function.LeftInverse.injective
        (fun v ↦ e.symmL_continuousLinearMapAt hy.2 v)))
  have hdim : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i ↦ Y i x))) = d - 1 := by
    rw [finrank_span_eq_card (hLI x hxB)]
    simp
  have hproper : Submodule.span ℂ (Set.range (fun i ↦ Y i x)) ≠ ⊤ := by
    intro h
    rw [h] at hdim
    simp [ComplexModel] at hdim
    omega
  obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top _ hproper
  let T (y : X) := e.symmL ℂ y v
  have hCT : ∀ y ∈ B, C y (T y) = v :=
    fun y hy ↦ e.continuousLinearMapAt_symmL hy.2 v
  have hT : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨y, T y⟩ : TangentBundle (complexModel d) X)) B := by
    apply (e.contMDiffOn_section_iff hB Set.inter_subset_right).mpr
    apply (contMDiffOn_const (c := v)).congr
    intro y hy
    rw [← e.continuousLinearMapAt_apply_of_mem ℂ hy.2]
    exact hCT y hy
  let A (y : X) : Option (Fin (d - 1)) → ComplexModel d :=
    fun i ↦ Option.casesOn' i v (fun j ↦ Y j y)
  have hA : ContinuousOn A B := by
    apply continuousOn_pi.mpr
    intro i
    cases i with
    | none => exact continuousOn_const
    | some i => exact hY i
  let W := B ∩ A ⁻¹' {a | LinearIndependent ℂ a}
  have hW : IsOpen W := hA.isOpen_inter_preimage hB isOpen_setOfPred_linearIndependent
  have hxW : x ∈ W := ⟨hxB, (hLI x hxB).option hv⟩
  refine ⟨⟨W, hW⟩, T, hxW, hT.mono Set.inter_subset_left, ?_⟩
  intro y hy hTU
  have hn : v ∉ Submodule.span ℂ (Set.range (fun i ↦ Y i y)) :=
    (linearIndependent_option'.mp hy.2).2
  apply hn
  rw [← hCT y hy.1]
  have hmap : (U y).map (C y).toLinearMap =
      Submodule.span ℂ (Set.range (fun i ↦ Y i y)) := by
    rw [← hspan y hy.1.1, Submodule.map_span]
    congr 1
    exact (Set.range_comp (C y).toLinearMap (fun i ↦ s i y)).symm
  rw [← hmap]
  exact Submodule.mem_map_of_mem hTU


end HolomorphicAnosov
