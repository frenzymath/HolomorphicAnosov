import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.ComplexLinearFrameFromRealSubbundle
import HolomorphicAnosov.Geometry.RealificationSubbundleChart
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Complex charts from a continuous real tangent subbundle

This file constructs local complex-linear charts from a continuous complex tangent subbundle. (Hatcher, Lemma 1.1 and Prop. 1.3; Ghys, Lemma 2.1)
-/

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
open Bundle
/-- A complex-linear family that is bijective at one fibre gives a complex-linear chart on a neighborhood. (Hatcher, Lemma 1.1 and Prop. 1.3; Ghys, Lemma 2.1) -/
theorem complex_chart_of_real_chart
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (S : ∀ y : M, Submodule ℂ (TangentSpace (complexModel d) y))
    (r s : ℕ) :
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y ↦ S y)) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    letI : TopologicalSpace (TotalSpace (Fin s → ℂ) (fun y ↦ S y)) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∀ (t : Trivialization (Fin r → ℝ)
        (TotalSpace.proj (F := Fin r → ℝ) (E := fun y ↦ S y))),
    t.IsLinear ℝ →
    ∀ (L : ∀ y, (Fin s → ℂ) →ₗ[ℂ] S y) (U : Set M), IsOpen U →
    (∀ w, ContinuousOn (fun y ↦ (⟨y, (L y w).val⟩ :
      TangentBundle (complexModel d) M)) U) →
    ∀ (x : M), x ∈ U ∩ t.baseSet → Function.Bijective (L x) →
    ∃ e : Trivialization (Fin s → ℂ)
        (TotalSpace.proj (F := Fin s → ℂ) (E := fun y ↦ S y)),
      x ∈ e.baseSet ∧ e.baseSet ⊆ U ∩ t.baseSet ∧ e.IsLinear ℂ ∧
      ∀ y ∈ e.baseSet, ∀ w, e.symm y w = L y w := by
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y ↦ S y)) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let : TopologicalSpace (TotalSpace (Fin s → ℂ) (fun y ↦ S y)) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  intro t ht L U hU hL x hx hxL
  let := ht
  let A (y : M) : (Fin s → ℂ) →L[ℝ] (Fin r → ℝ) :=
    ((t.linearMapAt ℝ y).comp ((L y).restrictScalars ℝ)).toContinuousLinearMap
  have hA : ContinuousOn A (U ∩ t.baseSet) := by
    apply continuousOn_clm_apply.mpr
    intro w
    have hi : ContinuousOn (fun y ↦ (⟨y, L y w⟩ :
        TotalSpace (Fin r → ℝ) (fun y ↦ S y))) U := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact continuous_induced_rng.mpr
        (continuousOn_iff_continuous_domRestrict.mp (hL w))
    have hc := (t.continuousOn.comp (hi.mono inter_subset_left)
      (fun y hy ↦ t.mem_source.mpr hy.2)).snd
    apply hc.congr
    intro y hy
    exact congrFun (t.coe_linearMapAt_of_mem (R := ℝ) hy.2) (L y w)
  have hAx : Function.Bijective (A x) := by
    have heq : (A x : (Fin s → ℂ) → (Fin r → ℝ)) =
        (t.linearEquivAt ℝ x hx.2) ∘ L x := by
      funext w
      change t.linearMapAt ℝ x (L x w) = _
      rw [t.linearMapAt_def_of_mem hx.2]
      rfl
    rw [heq]
    exact (t.linearEquivAt ℝ x hx.2).bijective.comp hxL
  let c := (LinearEquiv.ofBijective (A x).toLinearMap hAx).toContinuousLinearEquiv
  let N (y : M) := c.symm.toContinuousLinearMap.comp (A y)
  have hN : ContinuousOn N (U ∩ t.baseSet) := continuousOn_const.clm_comp hA
  have hNx : N x = ContinuousLinearMap.id ℝ (Fin s → ℂ) := by
    apply ContinuousLinearMap.ext
    intro w
    exact c.symm_apply_apply w
  let V := (U ∩ t.baseSet) ∩ {y | (N y).IsInvertible}
  have hV : IsOpen V := hN.isOpen_inter_preimage (hU.inter t.open_baseSet)
    ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hxV : x ∈ V := ⟨hx, by
    change (N x).IsInvertible
    rw [hNx]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩⟩
  let Q (y : M) := (N y).inverse.comp c.symm.toContinuousLinearMap
  have hQ : ContinuousOn Q V := by
    intro y hy
    obtain ⟨n, hn⟩ := hy.2
    have hi : ContinuousAt ContinuousLinearMap.inverse (N y) := by
      rw [← ContinuousLinearMap.ringInverse_eq_inverse, ← hn]
      exact NormedRing.inverse_continuousAt n.toUnit
    exact (hi.comp_continuousWithinAt (hN.mono inter_subset_left y hy)).clm_comp
      continuousWithinAt_const
  have hQL (y : M) (hy : y ∈ V) (w : Fin s → ℂ) :
      Q y (t.linearMapAt ℝ y (L y w)) = w := hy.2.inverse_apply_self w
  have hLQ (y : M) (hy : y ∈ V) (v : S y) :
      L y (Q y (t.linearMapAt ℝ y v)) = v := by
    apply (t.linearEquivAt ℝ y hy.1.2).injective
    apply c.symm.injective
    have hh := hy.2.self_apply_inverse (c.symm (t.linearMapAt ℝ y v))
    change c.symm (t.linearMapAt ℝ y (L y (Q y (t.linearMapAt ℝ y v)))) =
      c.symm (t.linearMapAt ℝ y v) at hh
    simpa only [t.linearMapAt_def_of_mem hy.1.2,
      LinearEquiv.coe_coe] using hh
  let repack (z : TotalSpace (Fin s → ℂ) (fun y ↦ S y)) :
      TotalSpace (Fin r → ℝ) (fun y ↦ S y) := ⟨z.proj, z.snd⟩
  have hrep : Continuous repack := continuous_induced_rng.mpr continuous_induced_dom
  have hproj : Continuous (TotalSpace.proj (F := Fin s → ℂ) (E := fun y ↦ S y)) := by
    have hi : Continuous (fun z : TotalSpace (Fin s → ℂ) (fun y ↦ S y) ↦
        (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) := continuous_induced_dom
    exact (FiberBundle.continuous_proj (ComplexModel d) (TangentSpace (complexModel d))).comp hi
  have htcoord : ContinuousOn (fun z : TotalSpace (Fin s → ℂ) (fun y ↦ S y) ↦
      (t (repack z)).2) (TotalSpace.proj ⁻¹' V) :=
    (t.continuousOn.comp hrep.continuousOn (fun z hz ↦ t.mem_source.mpr hz.1.2)).snd
  let e : Trivialization (Fin s → ℂ)
      (TotalSpace.proj (F := Fin s → ℂ) (E := fun y ↦ S y)) := {
    toFun := fun z ↦ (z.proj, Q z.proj (t (repack z)).2)
    invFun := fun z ↦ ⟨z.1, L z.1 z.2⟩
    source := TotalSpace.proj ⁻¹' V
    target := V ×ˢ univ
    map_source' := by intro z hz; exact ⟨hz, mem_univ _⟩
    map_target' := by intro z hz; exact hz.1
    left_inv' := by
      intro z hz
      apply TotalSpace.ext
      · rfl
      apply heq_of_eq
      change L z.proj (Q z.proj (t (repack z)).2) = z.snd
      rw [← congrFun (t.coe_linearMapAt_of_mem (R := ℝ) hz.1.2) z.snd]
      exact hLQ z.proj hz z.snd
    right_inv' := by
      intro z hz
      apply Prod.ext
      · rfl
      change Q z.1 (t ⟨z.1, L z.1 z.2⟩).2 = z.2
      rw [← congrFun (t.coe_linearMapAt_of_mem (R := ℝ) hz.1.1.2) (L z.1 z.2)]
      exact hQL z.1 hz.1 z.2
    open_source := hV.preimage hproj
    open_target := hV.prod isOpen_univ
    continuousOn_toFun := hproj.continuousOn.prodMk
      ((hQ.comp hproj.continuousOn (fun z hz ↦ hz)).clm_apply htcoord)
    continuousOn_invFun := by
      rw [continuousOn_iff_continuous_domRestrict]
      apply continuous_induced_rng.mpr
      have hcA : Continuous (fun z : V ×ˢ (univ : Set (Fin s → ℂ)) ↦
          (z.val.1, A z.val.1 z.val.2)) :=
        continuous_subtype_val.fst.prodMk
          ((hA.comp_continuous continuous_subtype_val.fst
            (fun z ↦ z.property.1.1)).clm_apply continuous_subtype_val.snd)
      have hc := t.continuousOn_symm.comp_continuous hcA
        (fun z ↦ ⟨z.property.1.1.2, mem_univ _⟩)
      have hi : Continuous (fun z : TotalSpace (Fin r → ℝ) (fun y ↦ S y) ↦
          (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) :=
        continuous_induced_dom
      apply (hi.comp hc).congr
      intro z
      change (⟨z.val.1, (t.symm z.val.1 (A z.val.1 z.val.2)).val⟩ :
          TangentBundle (complexModel d) M) = ⟨z.val.1, (L z.val.1 z.val.2).val⟩
      apply congrArg (fun v : S z.val.1 ↦
        (⟨z.val.1, v.val⟩ : TangentBundle (complexModel d) M))
      have hh := t.symm_apply_apply_mk z.property.1.1.2 (L z.val.1 z.val.2)
      change t.symm z.val.1 (t.linearMapAt ℝ z.val.1 (L z.val.1 z.val.2)) =
        L z.val.1 z.val.2
      rw [t.coe_linearMapAt_of_mem z.property.1.1.2]
      exact hh
    baseSet := V
    open_baseSet := hV
    source_eq := rfl
    target_eq := rfl
    proj_toFun := by intros; rfl }
  have heinv (y : M) (hy : y ∈ e.baseSet) (w : Fin s → ℂ) : e.symm y w = L y w := by
    apply TotalSpace.mk_injective y
    exact e.mk_symm hy w
  refine ⟨e, hxV, inter_subset_left, ?_, heinv⟩
  constructor
  intro y hy
  exact ((L y).inverse (fun v ↦ (e ⟨y, v⟩).2)
    (fun w ↦ by
      rw [← heinv y hy w]
      exact congrArg Prod.snd (e.apply_mk_symm hy w))
    (fun v ↦ by
      rw [← heinv y hy]
      exact e.symm_apply_apply_mk hy v)).isLinear


/-- Continuous complex tangent subspaces admit complex-linear local charts for their induced tangent topology. (Ghys, Lemma 2.1) -/
theorem complex_subbundle_of_realification
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (P : ContinuousRealTangentSubbundle (realModel d) M)
    (S : ∀ y : M, Submodule ℂ (TangentSpace (complexModel d) y))
    (hS : ∀ y, ((S y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = P.toDistribution y) :
    ∃ T : ContinuousComplexTangentSubbundle (complexModel d) M,
      T.toDistribution = S := by
  refine ⟨⟨S, ?_⟩, rfl⟩
  intro x
  let s := Module.finrank ℂ (S x)
  let b := Module.finBasis ℂ (S x)
  obtain ⟨U, L, hU, hx, hLx, hmem, hL⟩ :=
    complex_linear_frame_from_real_subbundle P S hS x b
  let K (y : M) : (Fin s → ℂ) →ₗ[ℂ] S y := (L y).codRestrict (S y) (hmem y)
  have hKx : Function.Bijective (K x) := by
    have heq : (K x : (Fin s → ℂ) → S x) = b.equivFun.symm := by
      funext w
      apply Subtype.ext
      change L x w = _
      rw [hLx]
      simp [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
    rw [heq]
    exact b.equivFun.symm.bijective
  obtain ⟨r, t, hxt, ht⟩ := P.locally_trivial x
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y ↦ P.toDistribution y)) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) M)) inferInstance
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y ↦ S y)) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  obtain ⟨t', ht'base, ht'⟩ := realification_subbundle_chart P.toDistribution S hS r t ht
  have hLfixed (w : Fin s → ℂ) : ContinuousOn (fun y ↦
      (⟨y, (K y w).val⟩ : TangentBundle (complexModel d) M)) U :=
    hL.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun y hy ↦ ⟨hy, mem_univ _⟩)
  obtain ⟨e, hxe, _, he, _⟩ := complex_chart_of_real_chart S r s t' ht' K U hU
    hLfixed x ⟨hx, ht'base.symm ▸ hxt⟩ hKx
  exact ⟨s, e, hxe, he⟩


end HolomorphicAnosov
