import HolomorphicAnosov.Geometry.Manifold.ChartActionCoordinateGeneratorG1
import HolomorphicAnosov.Geometry.Manifold.EuclideanOrbitMFDerivG1
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
Averaged spatial derivative identities for a continuous real action with smooth time slices give
smooth local tangent sections representing its orbit derivatives.
-/
open scoped Manifold ContDiff Interval Topology _root_.Topology
open Function Set
noncomputable section
namespace HolomorphicAnosov
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- A jointly continuous additive real action with smooth time slices and averaged spatial
derivative identities has a smooth tangent generator on an open neighborhood of each point.
(Bochner–Montgomery, Lemmas 2 and 5, pp. 688–689, 691) -/
theorem local_generator_chart_ball_core_g1
    (a : ℝ → M → M)
    (hcont : Continuous (Function.uncurry a))
    (hzero : ∀ x, a 0 x = x)
    (hadd : ∀ s t x, a s (a t x) = a (s + t) x)
    (hdiff : ∀ t, ∃ g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ x, g x = a t x)
    (haverage : ∀ x : M, ∃ r > 0, ∀ h : ℝ, 0 ≤ h → h ≤ r / 2 →
      ∀ y ∈ Metric.ball (chartAt E x x) (r / 2), ∀ k : ℕ,
        HasFDerivAt
          (fun z ↦ ∫ t in 0..h, iteratedFDeriv ℝ k
            (fun w : E ↦ chartAt E x (a t ((chartAt E x).symm w))) z)
          (∫ t in 0..h, fderiv ℝ (iteratedFDeriv ℝ k
            (fun w : E ↦ chartAt E x (a t ((chartAt E x).symm w)))) y) y) :
    ∀ x : M, ∃ U ∈ 𝓝 x, IsOpen U ∧
      ∃ Y : (y : M) → TangentSpace 𝓘(ℝ, E) y,
        CMDiff[U] ∞ (T% Y) ∧
        ∀ y ∈ U, ∃ L : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ]
            TangentSpace 𝓘(ℝ, E) (a 0 y),
          HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ ↦ a t y) 0 L ∧
          Y y = tangentSpaceCast (𝓘(ℝ, E)) (a 0 y) y
            (L ((tangentSpaceCastModel (𝓘(ℝ, ℝ)) 0).symm 1))  := by
  intro x
  obtain ⟨r, hr, havg⟩ := haverage x
  obtain ⟨W, hWo, hxW, hWt, X, hX, hdX⟩ :=
    chart_action_coordinate_generator_g1 a hcont hzero hadd hdiff x r hr havg
  let e := chartAt E x
  let T := trivializationAt E (TangentSpace 𝓘(ℝ,E)) x
  let U : Set M := e.source ∩ e ⁻¹' W
  have hUo : IsOpen U := e.isOpen_inter_preimage hWo
  have hxU : x ∈ U := ⟨mem_chart_source E x, hxW⟩
  have hUT : U ⊆ T.baseSet := by
    intro y hy
    simpa only [T, TangentBundle.trivializationAt_baseSet] using hy.1
  let Y : (y : M) → TangentSpace 𝓘(ℝ,E) y := fun y ↦ T.symmL ℝ y (X (e y))
  have hY : CMDiff[U] ∞ (T% Y) := by
    apply (T.contMDiffOn_section_iff hUo hUT).mpr
    have hce : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (fun y ↦ X (e y)) U :=
      (contMDiffOn_iff_contDiffOn.mpr hX).comp
        (contMDiffOn_chart.mono (fun y hy ↦ hy.1)) (fun y hy ↦ hy.2)
    apply hce.congr
    intro y hy
    rw [← T.continuousLinearMapAt_apply_of_mem ℝ (hUT hy)]
    exact T.continuousLinearMapAt_symmL (hUT hy) (X (e y))
  refine ⟨U, hUo.mem_nhds hxU, hUo, Y, hY, ?_⟩
  intro y hy
  have hyS : y ∈ e.source := hy.1
  have hyW : e y ∈ W := hy.2
  have hc : HasDerivAt (fun t : ℝ ↦ e (a t y)) (X (e y)) 0 := by
    have hdy := hdX (e y) hyW
    change HasDerivAt (fun t : ℝ ↦ e (a t (e.symm (e y)))) (X (e y)) 0 at hdy
    simpa only [e.left_inv hyS] using hdy
  have hcm := euclidean_orbit_mfderiv_g1 _ _ hc
  have hsym : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm (e y) :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) (IsManifold.chart_mem_maximalAtlas x)
      (e.map_source hyS)).mdifferentiableAt (by simp)
  have hinv : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm (e y) (T.symmL ℝ y) := by
    have ht := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ,E)) hyS
    simp only [extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
      Set.range_id, mfderivWithin_univ] at ht
    rw [show T.symmL ℝ y = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm (e y) from ht]
    exact hsym.hasMFDerivAt
  have hinv0 : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm (e (a 0 y)) (T.symmL ℝ y) := by
    constructor
    · simpa only [hzero y] using hinv.continuousAt
    · convert! hinv.2 using 1 <;> try simp only [hzero y]
  have hcom := hinv0.comp 0 hcm
  have hcy : ContinuousAt (fun t : ℝ ↦ a t y) 0 :=
    (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, a t y ∈ e.source :=
    hcy.preimage_mem_nhds (e.open_source.mem_nhds (by simpa only [hzero y] using hyS))
  have heq : (fun t : ℝ ↦ a t y) =ᶠ[𝓝 0] (fun t : ℝ ↦ e.symm (e (a t y))) := by
    filter_upwards [hevent] with t ht
    exact (e.left_inv ht).symm
  have hfinal := hcom.congr_of_eventuallyEq_abuse heq
  refine ⟨_, hfinal, ?_⟩
  change T.symmL ℝ y (X (e y)) =
    T.symmL ℝ y (((1 : ℝ →L[ℝ] ℝ).smulRight (X (e y))) 1)
  simp

end HolomorphicAnosov
