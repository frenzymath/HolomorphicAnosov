import HolomorphicAnosov.Geometry.HPSNativePlaqueFamilyData
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.ContDiff.Comp

open Set
open scoped Manifold ContDiff _root_.Topology

namespace HolomorphicAnosov

/-- The native plaque family restricted to a smaller center neighborhood. -/
def NativePlaqueFamily.restrictCenters
    {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
    (Φ : NativePlaqueFamily 𝓘(ℝ, E) (V := V) D x)
    (N : Set M) (hN : IsOpen N) (hx : x ∈ N) (hsub : N ⊆ Φ.centerDomain) :
    NativePlaqueFamily 𝓘(ℝ, E) (V := V) D x where
  centerDomain := N
  centerDomain_open := hN
  center_mem := hx
  radius := Φ.radius
  radius_pos := Φ.radius_pos
  plaque p := Φ.plaque ⟨p.val,hsub p.property⟩
  domain_eq p := Φ.domain_eq _
  frame p := Φ.frame ⟨p.val,hsub p.property⟩
  frame_continuous := Φ.frame_continuous.comp
    (((continuous_subtype_val.comp continuous_fst).subtype_mk (fun p ↦ hsub p.1.property)).prodMk continuous_snd)
  receivingAnchor := Φ.receivingAnchor
  receiving_domain p v hv := Φ.receiving_domain _ v hv
  jointly_continuous := Φ.jointly_continuous.comp
    (((continuous_subtype_val.comp continuous_fst).subtype_mk (fun p ↦ hsub p.1.property)).prodMk continuous_snd)
  coordinate_smooth p := Φ.coordinate_smooth _
  jointly_continuous_derivative := Φ.jointly_continuous_derivative.comp
    (((continuous_subtype_val.comp continuous_fst).subtype_mk (fun p ↦ hsub p.1.property)).prodMk continuous_snd)
  compact_C1 K hK hKR p₀ ε hε := by
    obtain ⟨W,hW,hpW,hcontrol⟩ := Φ.compact_C1 K hK hKR ⟨p₀.val,hsub p₀.property⟩ ε hε
    let j : N → Φ.centerDomain := fun p ↦ ⟨p.val,hsub p.property⟩
    exact ⟨j ⁻¹' W, hW.preimage (continuous_subtype_val.subtype_mk _), hpW,
      fun p hp v hv ↦ hcontrol (j p) hp v hv⟩

/-- The native plaque family with a new marked center in its center domain. -/
def NativePlaqueFamily.recenter
    {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
    (Φ : NativePlaqueFamily 𝓘(ℝ, E) (V := V) D x)
    (y : M) (hy : y ∈ Φ.centerDomain) : NativePlaqueFamily 𝓘(ℝ, E) (V := V) D y :=
  { Φ with center_mem := hy }

/-- The total plaque parametrization is continuous at the marked center and zero parameter. -/
theorem NativePlaqueFamily.continuousAt_centered_param
    {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
    (Φ : NativePlaqueFamily 𝓘(ℝ, E) (V := V) D x) :
    ContinuousAt (fun z : Φ.centerDomain × V ↦ (Φ.plaque z.1).param z.2)
      (⟨x, Φ.center_mem⟩, 0) := by
  have hc : ContinuousOn (fun z : Φ.centerDomain × V ↦ (Φ.plaque z.1).param z.2)
      (univ ×ˢ Metric.ball (0 : V) Φ.radius) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact Φ.jointly_continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z ↦ z.property.2)))
  exact hc.continuousAt ((isOpen_univ.prod Metric.isOpen_ball).mem_nhds
    ⟨mem_univ _, Metric.mem_ball_self Φ.radius_pos⟩)

/-- The first spatial derivative of a native finite-C1 plaque family is jointly continuous at the
marked center in the chart centered there. (HPS, pp.61–63) -/
theorem NativePlaqueFamily.continuousAt_centered_coordinate_derivative
    {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
    (Φ : NativePlaqueFamily 𝓘(ℝ, E) (V := V) D x) :
    ContinuousAt (fun z : Φ.centerDomain × V ↦
      fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ, E) x ((Φ.plaque z.1).param v)) z.2)
      (⟨x, Φ.center_mem⟩, 0) := by
  let p₀ : Φ.centerDomain := ⟨x, Φ.center_mem⟩
  let B := Metric.ball (0 : V) Φ.radius
  have h0 : (0 : V) ∈ B := Metric.mem_ball_self Φ.radius_pos
  let old := extChartAt 𝓘(ℝ, E) Φ.receivingAnchor
  let new := extChartAt 𝓘(ℝ, E) x
  let F := fun p : Φ.centerDomain ↦ fun v : V ↦ old ((Φ.plaque p).param v)
  let c := new ∘ old.symm
  have hxold : x ∈ old.source := by
    simpa only [(Φ.plaque p₀).centered] using Φ.receiving_domain p₀ 0 h0
  have hFcont : ContinuousOn (fun z : Φ.centerDomain × V ↦ F z.1 z.2) (univ ×ˢ B) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := (continuousOn_extChartAt (I := 𝓘(ℝ, E)) Φ.receivingAnchor).comp_continuous Φ.jointly_continuous
      (fun z ↦ Φ.receiving_domain z.1 z.2 z.2.property)
    exact hc.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z ↦ z.property.2)))
  have hF0 : F p₀ 0 = old x := by simp only [F, (Φ.plaque p₀).centered]; rfl
  have hDcont : ContinuousOn (fun z : Φ.centerDomain × V ↦ fderiv ℝ (F z.1) z.2)
      (univ ×ˢ B) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact Φ.jointly_continuous_derivative.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z ↦ z.property.2)))
  have hnhds : univ ×ˢ B ∈ 𝓝 (p₀, (0 : V)) :=
    (isOpen_univ.prod Metric.isOpen_ball).mem_nhds ⟨mem_univ _, h0⟩
  have hc : ContDiffAt ℝ 1 c (old x) := by
    rw [← contMDiffAt_iff_contDiffAt]
    have hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 new (old.symm (old x)) := by
      rw [old.left_inv hxold]
      exact contMDiffAt_extChartAt
    exact hn.comp (old x) ((contMDiffOn_extChartAt_symm Φ.receivingAnchor).contMDiffAt
      ((isOpen_extChartAt_target Φ.receivingAnchor).mem_nhds (old.map_source hxold)))
  have hDnew : ContinuousAt (fun z : Φ.centerDomain × V ↦
      (fderiv ℝ c (F z.1 z.2)).comp (fderiv ℝ (F z.1) z.2)) (p₀, 0) := by
    apply ContinuousAt.clm_comp _ (hDcont.continuousAt hnhds)
    rw [← hF0] at hc
    exact (hc.continuousAt_fderiv one_ne_zero).comp (f := fun z : Φ.centerDomain × V ↦ F z.1 z.2) (hFcont.continuousAt hnhds)
  apply hDnew.congr_of_eventuallyEq
  have hcnear : ∀ᶠ z : Φ.centerDomain × V in 𝓝 (p₀, 0),
      ContDiffAt ℝ 1 c (F z.1 z.2) := by
    have ht := (hFcont.continuousAt hnhds).tendsto
    rw [hF0] at ht
    exact ht.eventually (hc.eventually (by simp))
  filter_upwards [hnhds, hcnear] with z hz hcz
  have heq : (fun v ↦ new ((Φ.plaque z.1).param v)) =ᶠ[𝓝 z.2] c ∘ F z.1 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz.2] with v hv
    dsimp only [c, F, Function.comp_apply]
    rw [old.left_inv (Φ.receiving_domain z.1 v hv)]
  rw [heq.fderiv_eq]
  exact fderiv_comp z.2 (hcz.differentiableAt one_ne_zero)
    (((Φ.coordinate_smooth z.1).contDiffAt (Metric.isOpen_ball.mem_nhds hz.2)).differentiableAt (by simp))

end HolomorphicAnosov
