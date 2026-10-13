import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Basic

/-! Holomorphicity of normalized coefficient evaluation on the tangent total space (Demailly, V §1,
pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- A complex-linear functional with kernel a holomorphic subbundle of rank `d - 1`, normalized on a
holomorphic transverse section, has holomorphic total-space evaluation. -/
theorem normalized_total_coefficient_at
    (hd : 1 ≤ d)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU : IsHolomorphicTangentSubbundle (d - 1) U)
    {V : TopologicalSpace.Opens X}
    (T : (y : X) → TangentSpace (complexModel d) y)
    (hT : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨y, T y⟩ : TangentBundle (complexModel d) X)) V)
    (θ : (y : X) → TangentSpace (complexModel d) y →L[ℂ] ℂ)
    (hker : ∀ y ∈ V, (θ y).ker = U y) (hθT : ∀ y ∈ V, θ y (T y) = 1)
    (p : TangentBundle (complexModel d) X) (hpV : p.proj ∈ V) :
    ContMDiffAt (complexModel d).tangent 𝓘(ℂ, ℂ) ∞
      (fun q : TangentBundle (complexModel d) X ↦ θ q.proj q.snd) p := by
  classical
  let x := p.proj
  have hxV : x ∈ V := hpV
  obtain ⟨S, s, hxS, hs, hspan⟩ := hU x
  let W := (V : Set X)
  have hW : IsOpen W := V.isOpen
  have hxW : x ∈ W := hxV
  have hWV : W ⊆ (V : Set X) := Set.Subset.rfl
  let τ := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  let B := S ∩ W ∩ τ.baseSet
  have hB : IsOpen B := (hs.1.inter hW).inter τ.open_baseSet
  have hxτ : x ∈ τ.baseSet := by simp [τ, TangentBundle.trivializationAt_baseSet]
  have hxB : x ∈ B := ⟨⟨hxS, hxW⟩, hxτ⟩
  have hBV : B ⊆ (V : Set X) := fun y hy ↦ hWV hy.1.2
  let C (y : X) := τ.continuousLinearMapAt ℂ y
  let Y (i : Option (Fin (d - 1))) (y : X) :=
    Option.casesOn' i (C y (T y)) (fun j ↦ C y (s j y))
  have hsection : ∀ i : Option (Fin (d - 1)),
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun y ↦ (⟨y, Option.casesOn' i (T y) (fun j ↦ s j y)⟩ :
          TangentBundle (complexModel d) X)) B := by
    intro i
    cases i with
    | none => exact hT.mono (fun y hy ↦ hy.1.2)
    | some i => exact (hs.2.1 i).mono (fun y hy ↦ hy.1.1)
  have hY : ∀ i, ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel d) ∞ (Y i) B := by
    intro i
    have hc := (τ.contMDiffOn_section_iff hB Set.inter_subset_right).mp (hsection i)
    apply hc.congr
    intro y hy
    cases i <;> exact τ.continuousLinearMapAt_apply_of_mem ℂ hy.2 _
  have hLI : ∀ y ∈ B, LinearIndependent ℂ (fun i ↦ Y i y) := by
    intro y hy
    have hi : Function.Injective (C y) := Function.LeftInverse.injective
      (fun v ↦ τ.symmL_continuousLinearMapAt hy.2 v)
    have hsLI := (hs.2.2 y hy.1.1).map' (C y).toLinearMap (LinearMap.ker_eq_bot.mpr hi)
    apply hsLI.option
    intro hmem
    have hmap : (U y).map (C y).toLinearMap =
        Submodule.span ℂ (Set.range (fun i ↦ C y (s i y))) := by
      rw [← hspan y hy.1.1, Submodule.map_span]
      exact congrArg (Submodule.span ℂ) (Set.range_comp (C y).toLinearMap
        (fun i ↦ s i y)).symm
    change C y (T y) ∈ Submodule.span ℂ (Set.range (fun i ↦ C y (s i y))) at hmem
    rw [← hmap] at hmem
    obtain ⟨v, hv, heq⟩ := hmem
    have hTU : T y ∈ U y := (hi heq) ▸ hv
    have hzero : θ y (T y) = 0 := by
      have hm : T y ∈ (θ y).ker := by rw [hker y (hBV hy)]; exact hTU
      exact hm
    have hn := hθT y (hBV hy)
    rw [hzero] at hn
    exact zero_ne_one hn
  let F (y : X) : (Option (Fin (d - 1)) → ℂ) →L[ℂ] ComplexModel d :=
    ∑ i, (ContinuousLinearMap.proj i : (Option (Fin (d - 1)) → ℂ) →L[ℂ] ℂ).smulRight (Y i y)
  have hFapply : ∀ y a, F y a = ∑ i, a i • Y i y := by
    intro y a
    simp [F]
  have hF : ContMDiffOn (complexModel d)
      𝓘(ℂ, (Option (Fin (d - 1)) → ℂ) →L[ℂ] ComplexModel d) ∞ F B := by
    have hterms : ∀ i, ContMDiffOn (complexModel d)
        𝓘(ℂ, (Option (Fin (d - 1)) → ℂ) →L[ℂ] ComplexModel d) ∞
        (fun y ↦ (ContinuousLinearMap.proj i : (Option (Fin (d - 1)) → ℂ) →L[ℂ] ℂ).smulRight (Y i y)) B := by
      intro i
      exact ((ContinuousLinearMap.smulRightL ℂ (Option (Fin (d - 1)) → ℂ)
        (ComplexModel d) (ContinuousLinearMap.proj i : (Option (Fin (d - 1)) → ℂ) →L[ℂ] ℂ)).contMDiff.comp_contMDiffOn (hY i))
    have hsum : ∀ K : Finset (Option (Fin (d - 1))), ContMDiffOn (complexModel d)
        𝓘(ℂ, (Option (Fin (d - 1)) → ℂ) →L[ℂ] ComplexModel d) ∞
        (fun y ↦ ∑ i ∈ K, (ContinuousLinearMap.proj i : (Option (Fin (d - 1)) → ℂ) →L[ℂ] ℂ).smulRight (Y i y)) B := by
      intro K
      induction K using Finset.induction_on with
      | empty => simpa using (contMDiffOn_const (c := (0 :
          (Option (Fin (d - 1)) → ℂ) →L[ℂ] ComplexModel d)))
      | @insert i K hi hK =>
          apply ((hterms i).add hK).congr
          intro y _
          simp only [Finset.sum_insert hi, Pi.add_apply]
    exact hsum Finset.univ
  have hinj : ∀ y ∈ B, Function.Injective (F y) := by
    intro y hy a b hab
    have hzero : F y (a - b) = 0 := by rw [map_sub, hab, sub_self]
    rw [hFapply] at hzero
    have hc := Fintype.linearIndependent_iff.mp (hLI y hy) (a - b) hzero
    ext i
    exact sub_eq_zero.mp (hc i)
  have hdim : Module.finrank ℂ (Option (Fin (d - 1)) → ℂ) =
      Module.finrank ℂ (ComplexModel d) := by
    simp [ComplexModel]
    omega
  have hinvert : ∀ y ∈ B, (F y).IsInvertible := by
    intro y hy
    exact ⟨(LinearEquiv.ofInjectiveOfFinrankEq (F y).toLinearMap
      (hinj y hy) hdim).toContinuousLinearEquiv, rfl⟩
  have hInv : ContMDiffAt (complexModel d)
      𝓘(ℂ, ComplexModel d →L[ℂ] (Option (Fin (d - 1)) → ℂ)) ∞
      (fun y ↦ (F y).inverse) x :=
    (hinvert x hxB).contDiffAt_map_inverse.contMDiffAt.comp x
      (hF.contMDiffAt (hB.mem_nhds hxB))
  have hpτ : p ∈ τ.source := τ.mem_source.mpr hxτ
  have hcoord : ContMDiffAt (complexModel d).tangent 𝓘(ℂ, ComplexModel d) ∞
      (fun q : TangentBundle (complexModel d) X ↦ (τ q).2) p :=
    ((τ.contMDiffOn (IB := complexModel d) (n := ∞)).contMDiffAt
      (τ.open_source.mem_nhds hpτ)).snd
  have hscalar : ContMDiffAt (complexModel d).tangent 𝓘(ℂ, ℂ) ∞
      (fun q : TangentBundle (complexModel d) X ↦
        ((F q.proj).inverse (τ q).2) none) p :=
    (ContinuousLinearMap.proj none).contMDiffAt.comp p
      ((hInv.comp p (contMDiffAt_proj (TangentSpace (complexModel d)))).clm_apply hcoord)
  apply hscalar.congr_of_eventuallyEq
  filter_upwards [(FiberBundle.continuous_proj (ComplexModel d)
    (TangentSpace (complexModel d))).continuousAt.preimage_mem_nhds
      (hB.mem_nhds hxB)] with q hq
  let y := q.proj
  have hy : y ∈ B := hq
  have hqcoord : (τ q).2 = C y q.snd :=
    (τ.continuousLinearMapAt_apply_of_mem ℂ hy.2 q.snd).symm
  rw [hqcoord]
  let a := (F y).inverse (C y q.snd)
  have heq : C y (q.snd) = ∑ i, a i • Y i y := by
    rw [← hFapply]
    exact ((hinvert y hy).self_apply_inverse (C y q.snd)).symm
  have hsum : q.snd = ∑ i : Option (Fin (d - 1)),
      a i • Option.casesOn' i (T y) (fun j ↦ s j y) := by
    apply (Function.LeftInverse.injective
      (fun v ↦ τ.symmL_continuousLinearMapAt (R := ℂ) hy.2 v))
    rw [map_sum]
    change C y (q.snd) = _
    rw [heq]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    cases i <;> rfl
  change θ y q.snd = a none
  rw [hsum, map_sum, Fintype.sum_option]
  simp only [Option.casesOn'_none, Option.casesOn'_some, map_smul]
  have hszero : ∀ i, θ y (s i y) = 0 := by
    intro i
    have hm : s i y ∈ (θ y).ker := by
      rw [hker y (hBV hy), ← hspan y hy.1.1]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact hm
  simp [hszero, hθT y (hBV hy)]


end HolomorphicAnosov
