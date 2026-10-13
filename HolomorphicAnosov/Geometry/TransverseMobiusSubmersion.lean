import HolomorphicAnosov.Geometry.ComplexMobiusChartDifferential
import Mathlib.Analysis.Calculus.FDeriv.Prod

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
open Ghys

/-- A projective developing map has a surjective real differential in any real chart
whose transition to a lifted flowbox is `C¹` with invertible derivative.
(Ghys, §5, p. 597) -/
theorem transverse_mobius_submersion
    {M Y ι : Type*} [TopologicalSpace M] [TopologicalSpace Y]
    (q : ℕ)
    (b : ι → OpenPartialHomeomorph M ((Fin q → ℝ) × ℂ))
    (hlocal : ∀ i j x, x ∈ (b i).source ∩ (b j).source →
      ∃ g : ComplexMobiusTransformation,
        ∀ᶠ w in 𝓝 x,
          complexProjectiveLineFinite ((b j w).2) =
            g.apply (complexProjectiveLineFinite ((b i w).2)))
    (p : Y → M) (hp : Continuous p)
    (D : Y → ComplexProjectiveLine)
    (hDlocal : ∀ y, ∃ i, ∃ g : ComplexMobiusTransformation, ∃ U : Set Y,
      IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (b i).source ∧
        EqOn D (fun w ↦ g.apply (complexProjectiveLineFinite ((b i (p w)).2))) U) :
    ∀ (c : OpenPartialHomeomorph Y ((Fin q → ℝ) × ℂ)) y,
      y ∈ c.source → ∀ i, p y ∈ (b i).source →
      ContDiffAt ℝ 1 (fun z ↦ b i (p (c.symm z))) (c y) →
      Function.Bijective (fderiv ℝ (fun z ↦ b i (p (c.symm z))) (c y)) →
      ∃ k : Fin 2,
        D y ∈ complexProjectiveLineChartSource k ∧
        DifferentiableAt ℝ (fun z ↦ complexProjectiveLineChartFun k (D (c.symm z))) (c y) ∧
        Function.Surjective
          (fderiv ℝ (fun z ↦ complexProjectiveLineChartFun k (D (c.symm z))) (c y)) := by
  intro c y hyc i hyi hcont hbij
  obtain ⟨j, gj, U, hUo, hyU, hUsub, hD⟩ := hDlocal y
  have hyj : p y ∈ (b j).source := hUsub hyU
  obtain ⟨gt, hgt⟩ := hlocal i j (p y) ⟨hyi, hyj⟩
  let gc : ComplexMobiusTransformation :=
    ⟨gt.val.trans gj.val, by
      obtain ⟨A, hA⟩ := gj.property
      obtain ⟨B, hB⟩ := gt.property
      refine ⟨A * B, ?_⟩
      intro z
      change gj.val (gt.val z) = (A * B) • z
      rw [hA, hB]
      simp only [mul_smul]⟩
  have hgc : ∀ᶠ w in 𝓝 (p y),
      complexProjectiveLineFinite ((b j w).2) =
        gt.apply (complexProjectiveLineFinite ((b i w).2)) := hgt
  have hc : ContinuousAt c.symm (c y) := c.continuousAt_symm (c.map_source hyc)
  have hcpy : ContinuousAt (fun z ↦ p (c.symm z)) (c y) := hp.continuousAt.comp hc
  have hUevent : ∀ᶠ z in 𝓝 (c y), c.symm z ∈ U := by
    apply mem_of_superset (hc.preimage_mem_nhds ?_)
    intro z hz
    exact hz
    simpa only [c.left_inv hyc] using hUo.mem_nhds hyU
  have htrans : ∀ᶠ z in 𝓝 (c y),
      complexProjectiveLineFinite ((b j (p (c.symm z))).2) =
        gt.apply (complexProjectiveLineFinite ((b i (p (c.symm z))).2)) := by
    have hpc : (fun z ↦ p (c.symm z)) (c y) = p y := by simp [c.left_inv hyc]
    have hh := hcpy.tendsto.eventually (show ∀ᶠ w in 𝓝 (p (c.symm (c y))),
      complexProjectiveLineFinite ((b j w).2) = gt.apply (complexProjectiveLineFinite ((b i w).2)) by
      simpa only [hpc] using hgc)
    simpa only [Function.comp_apply] using hh
  have hEq : ∀ᶠ z in 𝓝 (c y),
      D (c.symm z) = gc.apply (complexProjectiveLineFinite ((b i (p (c.symm z))).2)) := by
    filter_upwards [hUevent, htrans] with z hz htrans
    simpa only [Function.comp_apply, gc] using
      (hD hz).trans ((congrArg gj.apply htrans).trans (by rfl))
  let T : ((Fin q → ℝ) × ℂ) →L[ℝ] ComplexModel 1 :=
    ContinuousLinearMap.pi (fun _ ↦ ContinuousLinearMap.snd ℝ (Fin q → ℝ) ℂ)
  let B : ((Fin q → ℝ) × ℂ) → ((Fin q → ℝ) × ℂ) := fun z ↦ b i (p (c.symm z))
  let F := T ∘ B
  have hFy : F (c y) = (fun _ : Fin 1 ↦ (b i (p y)).2) := by
    simp [F, B, T, c.left_inv hyc]
  obtain ⟨k, hk, hdiffg, hsurjg⟩ :=
    complex_mobius_chart_differential gc (F (c y))
  let G : ComplexModel 1 → ComplexModel 1 := fun w ↦
    complexProjectiveLineChartFun k (gc.apply (complexProjectiveLineChartInv 1 w))
  have hDy : D y ∈ complexProjectiveLineChartSource k := by
    have he := hEq.self_of_nhds
    rw [c.left_inv hyc] at he
    rw [he]
    simpa only [hFy, complexProjectiveLineFinite] using hk
  have hpair : DifferentiableAt ℝ B (c y) := hcont.differentiableAt (by simp)
  have hFderiv : HasFDerivAt F (T.comp (fderiv ℝ B (c y))) (c y) :=
    T.hasFDerivAt.comp (c y) hpair.hasFDerivAt
  have hTsurj : Function.Surjective T := by
    intro w
    refine ⟨(0, w 0), ?_⟩
    funext j
    exact congrArg w (Subsingleton.elim 0 j)
  have hFsurj : Function.Surjective (T.comp (fderiv ℝ B (c y))) :=
    hTsurj.comp hbij.2
  have hcoordinateEq : (fun z ↦ complexProjectiveLineChartFun k (D (c.symm z))) =ᶠ[𝓝 (c y)]
      (G ∘ F) := by
    filter_upwards [hEq] with z hz
    exact congrArg (complexProjectiveLineChartFun k) hz
  have hderiv : HasFDerivAt (fun z ↦ complexProjectiveLineChartFun k (D (c.symm z)))
      ((fderiv ℝ G (F (c y))).comp (T.comp (fderiv ℝ B (c y)))) (c y) :=
    (hdiffg.hasFDerivAt.comp (c y) hFderiv).congr_of_eventuallyEq hcoordinateEq
  refine ⟨k, hDy, hderiv.differentiableAt, ?_⟩
  rw [hderiv.fderiv]
  exact hsurjg.comp hFsurj

end HolomorphicAnosov
