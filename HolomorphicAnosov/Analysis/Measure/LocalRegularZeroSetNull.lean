import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open Filter Set MeasureTheory
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- Mityagin, Claim 1, pp. 1–2: a regular zero of a C¹ real function has a
neighborhood on which its zero set is null. The implicit function theorem
parametrizes the level set by the kernel of the nonzero derivative. Compose
this parametrization with the continuous linear projection onto that kernel;
this gives a C¹ map of the original Euclidean space into itself near zero.
The kernel is a proper subspace and hence null. Its image under that map is
null, and contains every sufficiently nearby zero of the original function. -/
theorem exists_nhds_volume_zero_set_eq_zero {N : ℕ}
    {f : EuclideanSpace ℝ (Fin N) → ℝ} {a : EuclideanSpace ℝ (Fin N)}
    (hf : ContDiffAt ℝ 1 f a) (ha : f a = 0) (hreg : fderiv ℝ f a ≠ 0) :
    ∃ V ∈ 𝓝 a, volume {x | x ∈ V ∧ f x = 0} = 0 := by
  let L := fderiv ℝ f a
  have hL : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero (by
    intro h
    apply hreg
    ext x
    exact LinearMap.congr_fun h x)
  let hc := L.ker_closedComplemented_of_finiteDimensional_range
  let P : EuclideanSpace ℝ (Fin N) →L[ℝ] L.ker := Classical.choose hc
  have hP (x : L.ker) : P x = x := Classical.choose_spec hc x
  let φ := (hf.hasStrictFDerivAt one_ne_zero).implicitFunctionDataOfComplemented f L hL hc
  have hright : ContDiffAt ℝ 1 φ.rightFun a := by
    exact P.contDiff.contDiffAt.comp a (contDiffAt_id.sub contDiffAt_const)
  have hg : ContDiffAt ℝ 1 φ.implicitFunction.uncurry (0, (0 : L.ker)) := by
    simpa [φ, ImplicitFunctionData.prodFun, ha] using
      φ.contDiffAt_implicitFunction hf hright one_ne_zero
  let F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
    fun v ↦ φ.implicitFunction 0 (P v)
  have hF : ContDiffAt ℝ 1 F 0 := by
    have hc : ContDiffAt ℝ 1 (fun v : EuclideanSpace ℝ (Fin N) ↦ ((0 : ℝ), P v)) 0 :=
      contDiffAt_const.prodMk P.contDiff.contDiffAt
    have hg' : ContDiffAt ℝ 1 φ.implicitFunction.uncurry ((0 : ℝ), P 0) := by
      simpa only [map_zero] using hg
    exact hg'.comp 0 (f := fun v : EuclideanSpace ℝ (Fin N) ↦ ((0 : ℝ), P v)) hc
  obtain ⟨V, hV, hdiff⟩ := eventually_iff_exists_mem.mp
    ((hF.eventually (by decide)).mono fun x hx ↦ hx.differentiableAt one_ne_zero)
  have hnull : volume (F '' ((L.ker : Set _) ∩ V)) = 0 := by
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    · intro x hx
      exact (hdiff x hx.2).differentiableWithinAt
    · apply measure_mono_null inter_subset_left
      apply Measure.addHaar_submodule
      intro htop
      apply hreg
      ext x
      have hx : x ∈ L.ker := by rw [htop]; trivial
      exact hx
  have htend : Tendsto (fun x ↦ (P (x - a) : EuclideanSpace ℝ (Fin N)))
      (𝓝 a) (𝓝 0) := by
    have ht : ContinuousAt (fun x ↦ (P (x - a) : EuclideanSpace ℝ (Fin N))) a :=
      L.ker.subtypeL.continuous.continuousAt.comp
        (P.continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const))
    simpa only [sub_self, map_zero, ZeroMemClass.coe_zero] using ht.tendsto
  have heq := φ.implicitFunction_apply_image
  have hnear : ∀ᶠ x in 𝓝 a,
      f x = 0 → x ∈ F '' ((L.ker : Set _) ∩ V) := by
    filter_upwards [htend hV, heq] with x hx heq hxzero
    refine ⟨P (x - a), ⟨(P (x - a)).property, hx⟩, ?_⟩
    change φ.implicitFunction 0 (P (P (x - a))) = x
    rw [hP]
    change φ.implicitFunction (f x) (P (x - a)) = x at heq
    rwa [hxzero] at heq
  obtain ⟨W, hW, hsub⟩ := eventually_iff_exists_mem.mp hnear
  refine ⟨W, hW, measure_mono_null ?_ hnull⟩
  exact fun x hx ↦ hsub x hx.1 hx.2

end HolomorphicAnosov
