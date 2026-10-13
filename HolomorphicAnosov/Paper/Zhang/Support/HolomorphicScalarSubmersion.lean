import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
universe u
set_option backward.isDefEq.respectTransparency false in
/-- A holomorphic scalar function with surjective manifold derivative admits local submersion
charts. (Zhang, Lemma 2.4, p. 7) -/
theorem holomorphic_scalar_submersion_of_surjective
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (f : X → ℂ) (V : Opens X)
    (hf : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ f V)
    (x : X) (hx : x ∈ V)
    (hsurj : Function.Surjective (mfderiv (complexModel d) 𝓘(ℂ, ℂ) f x)) :
    Manifold.IsSubmersionAt (complexModel d) 𝓘(ℂ, ℂ) ∞ f x := by
  have hcoord {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (f : E → ℂ) (S : Set E) (hSo : IsOpen S) (hf : ContDiffOn ℂ ∞ f S)
      (x : E) (hx : x ∈ S) (hsurj : Function.Surjective (fderiv ℂ f x)) :
      Manifold.IsSubmersionAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ f x := by
    obtain ⟨v₀, hv₀⟩ := hsurj 1
    let D := fderiv ℂ f x
    let R : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v₀
    have hR : Function.RightInverse R D := by intro a; simp [R, D, hv₀]
    let e : E ≃L[ℂ] ℂ × D.ker := ContinuousLinearEquiv.equivOfRightInverse D R hR
    let F : E → E := fun z ↦ z + R (f z - D z)
    have hF : ContDiffOn ℂ ∞ F S :=
      contDiffOn_id.add (R.contDiff.comp_contDiffOn (hf.sub D.contDiff.contDiffOn))
    have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hSo.mem_nhds hx)
    have hFd : HasFDerivAt F (ContinuousLinearEquiv.refl ℂ E : E →L[ℂ] E) x := by
      have h := (hasFDerivAt_id x).add
        (R.hasFDerivAt.comp x (((hf.contDiffAt (hSo.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.sub D.hasFDerivAt))
      simpa [D, F, Function.comp_def, Pi.add_def, Pi.sub_def] using h
    let p := hFx.toOpenPartialHomeomorph F hFd (by simp)
    have hxp : x ∈ p.source := hFx.mem_toOpenPartialHomeomorph_source hFd (by simp)
    have hinv : (fderiv ℂ F x).IsInvertible := by
      rw [hFd.fderiv]
      exact ContinuousLinearMap.isInvertible_equiv
    have hn := hFx.continuousAt_fderiv (by simp) hinv.eventually_nhds
    obtain ⟨T, hT, hTo, hxT⟩ := mem_nhds_iff.mp hn
    let q := p.restrOpen (S ∩ T) (hSo.inter hTo)
    have hxq : x ∈ q.source := ⟨hxp, hx, hxT⟩
    have hqf : (q : E → E) = F := rfl
    have hqs : ContDiffOn ℂ ∞ q q.source := hF.mono (fun _ hy ↦ hy.2.1)
    have hqinv : ContDiffOn ℂ ∞ q.symm q.target := by
      intro y hy
      have hys := q.map_target hy
      obtain ⟨L, hL⟩ := hT hys.2.2
      apply ContDiffAt.contDiffWithinAt
      apply q.contDiffAt_symm hy (f₀' := L)
      · have hd := ((hF _ hys.2.1).contDiffAt (hSo.mem_nhds hys.2.1)).differentiableAt (by simp)
        have hdf := hd.hasFDerivAt
        rw [← hL] at hdf
        exact hdf
      · exact hqs.contDiffAt (q.open_source.mem_nhds hys)
    have hqatlas := q.mem_maximalAtlas_of_contMDiffOn hqs.contMDiffOn hqinv.contMDiffOn
    apply Manifold.IsSubmersionAt.mk_of_charts e q (OpenPartialHomeomorph.refl ℂ)
      hxq (mem_univ _) hqatlas (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ (f x)))
      (fun _ _ ↦ mem_univ _)
    intro y hy
    have hyq : y ∈ q.target := by simpa using hy
    have hEq : f (q.symm y) = D y := by
      have hright := q.right_inv hyq
      change F (q.symm y) = y at hright
      calc
        f (q.symm y) = D (F (q.symm y)) := by
          simp only [F, map_add]
          rw [hR]
          abel
        _ = D y := congrArg D hright
    exact hEq
  let c := chartAt (ComplexModel d) x
  have hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
    IsManifold.chart_mem_maximalAtlas x
  have hcx : x ∈ c.source := mem_chart_source _ _
  let S := c.target ∩ c.symm ⁻¹' (V : Set X)
  have hSo : IsOpen S := c.isOpen_inter_preimage_symm V.isOpen
  have hxS : c x ∈ S := by
    refine ⟨c.map_source hcx, ?_⟩
    change c.symm (c x) ∈ V
    rwa [c.left_inv hcx]
  have hg : ContDiffOn ℂ ∞ (f ∘ c.symm) S :=
    (hf.comp ((contMDiffOn_symm_of_mem_maximalAtlas hc).mono inter_subset_left)
      (fun _ hy ↦ hy.2)).contDiffOn
  have hsurjg : Function.Surjective (fderiv ℂ (f ∘ c.symm) (c x)) := by
    have hfc : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) f x :=
      (hf.contMDiffAt (V.isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
    have hfc' : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) f (c.symm (c x)) := by
      rwa [c.left_inv hcx]
    have hci := (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hcx)).mdifferentiableAt
      (by simp)
    have hd := mfderiv_comp (c x) hfc' hci
    rw [mfderiv_eq_fderiv] at hd
    have hi : (mfderiv (complexModel d) (complexModel d) c.symm (c x)).IsInvertible := by
      have h := isInvertible_mfderivWithin_extend_symm (I := complexModel d)
        (IsManifold.chart_mem_maximalAtlas (n := 1) x) (y := c x)
        (by simpa using c.map_source hcx)
      simpa using h
    have hs : Function.Surjective (mfderiv (complexModel d) 𝓘(ℂ, ℂ) f (c.symm (c x))) := by
      rwa [c.left_inv hcx]
    intro a
    obtain ⟨v, hv⟩ := hs ((NormedSpace.fromTangentSpace (f (c.symm (c x)))).symm a)
    refine ⟨(mfderiv (complexModel d) (complexModel d) c.symm (c x)).inverse v, ?_⟩
    rw [hd]
    change mfderiv (complexModel d) 𝓘(ℂ, ℂ) f (c.symm (c x))
      (mfderiv (complexModel d) (complexModel d) c.symm (c x)
        ((mfderiv (complexModel d) (complexModel d) c.symm (c x)).inverse v)) = _
    rw [hi.self_apply_inverse, hv]
    rfl
  have hgsub := hcoord (f ∘ c.symm) S hSo hg (c x) hxS hsurjg
  let q := c.trans hgsub.domChart
  have hxq : x ∈ q.source := ⟨hcx, hgsub.mem_domChart_source⟩
  have hqatlas : q ∈ IsManifold.maximalAtlas (complexModel d) ∞ X := by
    apply q.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hgsub.domChart_mem_maximalAtlas).comp
        ((contMDiffOn_of_mem_maximalAtlas hc).mono inter_subset_left) (fun _ hy ↦ hy.2)
    · exact (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hgsub.domChart_mem_maximalAtlas).mono
          inter_subset_left) (fun _ hy ↦ hy.2)
  apply Manifold.IsSubmersionAt.mk_of_charts hgsub.equiv q hgsub.codChart hxq
    (by simpa only [Function.comp_apply, c.left_inv hcx] using hgsub.mem_codChart_source)
    hqatlas hgsub.codChart_mem_maximalAtlas
  · intro y hy
    have h := hgsub.source_subset_preimage_source hy.2
    change f (c.symm (c y)) ∈ hgsub.codChart.source at h
    rwa [c.left_inv hy.1] at h
  · intro y hy
    have hyq : y ∈ q.target := by simpa using hy
    have h := hgsub.writtenInCharts (by simpa using hyq.1)
    exact h


end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
