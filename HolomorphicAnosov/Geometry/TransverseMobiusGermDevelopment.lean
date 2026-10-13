import HolomorphicAnosov.Geometry.TransverseMobiusFrameContinuationG4
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import HolomorphicAnosov.Geometry.TransverseMobiusDeckHolonomy
import HolomorphicAnosov.Geometry.MobiusGroupContinuousG9
import HolomorphicAnosov.Geometry.FlatProjectiveFrameCoverG9
import HolomorphicAnosov.Geometry.TransverseMobiusInitialSection
import HolomorphicAnosov.Geometry.TransverseMobiusLocalForm
import HolomorphicAnosov.Geometry.TransverseMobiusGermEqOn
import HolomorphicAnosov.Geometry.TransverseMobiusUniqueness
import HolomorphicAnosov.Geometry.TransverseMobiusComparison
import HolomorphicAnosov.Geometry.TransverseMobiusPlaqueConstancy
import HolomorphicAnosov.Geometry.TransverseMobiusFiberComponents
import HolomorphicAnosov.Geometry.TransverseMobiusContinuation
import HolomorphicAnosov.Geometry.TransverseMobiusSubmersion
import HolomorphicAnosov.Geometry.FlatProjectiveFrameEvaluationG9
import HolomorphicAnosov.Paper.Ghys.ProjectiveLocalGermsEffectiveCocycle
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Geometry.ComplexMobiusOnePointBridge
import HolomorphicAnosov.Topology.LocalHomeomorphLocallyPathConnected
import HolomorphicAnosov.Topology.TransverseSourceLocallyPathConnected

/-! Existence and uniqueness of transverse projective developing maps, with continuation,
deck holonomy, fiber components, and transverse regularity.
(Thurston, §3.5, pp. 34–35 and §4.8, p. 63; Ghys, §5, p. 597) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold


namespace HolomorphicAnosov
open Ghys IsManifold

/-- A transverse projective atlas has a unique developing map on a simply connected cover
with a prescribed initial germ; its fiber components are lifted plaque-chain classes,
its germ continuation is homotopy invariant, and it is equivariant under unique deck holonomy.
The map is unique up to Möbius transformation and is a submersion in compatible differentiable
charts and a local biholomorphism on holomorphic transversals.
(Thurston, §3.5, pp. 34–35 and §4.8, p. 63; Ghys, §5, p. 597) -/
theorem transverse_mobius_germ_development
    {M Y ι : Type*} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (q : ℕ)
    (b : ι → OpenPartialHomeomorph M ((Fin q → ℝ) × ℂ))
    (P : ι → Set (Fin q → ℝ)) (V : ι → Set ℂ)
    (_hP : ∀ i, IsOpen (P i) ∧ IsConnected (P i))
    (_hV : ∀ i, IsOpen (V i))
    (_htarget : ∀ i, (b i).target = P i ×ˢ V i)
    (hcover : ∀ x : M, ∃ i, x ∈ (b i).source)
    (hlocal : ∀ i j x, x ∈ (b i).source ∩ (b j).source →
      ∃ g : ComplexMobiusTransformation,
        ∀ᶠ w in 𝓝 x,
          complexProjectiveLineFinite ((b j w).2) =
            g.apply (complexProjectiveLineFinite ((b i w).2)))
    (p : Y → M) (hp : IsCoveringMap p) (_hsurj : Function.Surjective p)
    (y₀ : Y) (i₀ : ι) (hi₀ : p y₀ ∈ (b i₀).source)
    (g₀ : ComplexMobiusTransformation) :
    let τ : ι → M → ComplexProjectiveLine :=
      fun i x ↦ complexProjectiveLineFinite ((b i x).2)
    let initial : M → ComplexProjectiveLine := fun x ↦ g₀.apply (τ i₀ x)
    let localForm : (Y → ComplexProjectiveLine) → Prop := fun D ↦
      ∀ y, ∃ i, ∃ g : ComplexMobiusTransformation, ∃ U : Set Y,
        IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (b i).source ∧
          EqOn D (fun w ↦ g.apply (τ i (p w))) U
    let compatible : C(Y, ComplexProjectiveLine) → Prop := fun D ↦
      localForm D ∧
        (Filter.Germ.ofFun D : Filter.Germ (𝓝 y₀) ComplexProjectiveLine) =
          Filter.Germ.ofFun (initial ∘ p)
    let continued : ∀ {x : M}, Path (p y₀) x →
        (unitInterval → M → ComplexProjectiveLine) → Prop := fun {_} α η ↦
      (Filter.Germ.ofFun (η 0) : Filter.Germ (𝓝 (p y₀)) ComplexProjectiveLine) =
          Filter.Germ.ofFun initial ∧
      ∀ t, ∃ T : Set unitInterval, IsOpen T ∧ t ∈ T ∧
        ∃ i, ∃ g : ComplexMobiusTransformation, ∃ U : Set M,
          IsOpen U ∧ α t ∈ U ∧ U ⊆ (b i).source ∧
            ∀ s ∈ T, α s ∈ U ∧
              (Filter.Germ.ofFun (η s) : Filter.Germ (𝓝 (α s)) ComplexProjectiveLine) =
                Filter.Germ.ofFun (fun w ↦ g.apply (τ i w))
    let plaqueLink : Y → Y → Prop := fun y z ↦
      ∃ i, ∃ β : Path y z, ∀ t : unitInterval,
        p (β t) ∈ (b i).source ∧ (b i (p (β t))).2 = (b i (p y)).2
    let G : Subgroup (Equiv.Perm ComplexProjectiveLine) :=
      (MulAction.toPermHom (GL (Fin 2) ℂ) ComplexProjectiveLine).range
    (∃! D : C(Y, ComplexProjectiveLine), compatible D) ∧
    ∀ D : C(Y, ComplexProjectiveLine), compatible D →
      (∀ y, connectedComponentIn (D ⁻¹' {D y}) y =
        {z | Relation.ReflTransGen plaqueLink y z}) ∧
      (∀ x (α : Path (p y₀) x),
        (∃ η, continued α η) ∧
        ∀ η η', continued α η → continued α η' → ∀ t,
          (Filter.Germ.ofFun (η t) : Filter.Germ (𝓝 (α t)) ComplexProjectiveLine) =
            Filter.Germ.ofFun (η' t)) ∧
      (∀ x (α β : Path (p y₀) x), α.Homotopic β →
        ∀ η η', continued α η → continued β η' →
          (Filter.Germ.ofFun (η 1) : Filter.Germ (𝓝 x) ComplexProjectiveLine) =
            Filter.Germ.ofFun (η' 1)) ∧
      (∀ y (β : Path y₀ y) (α : Path (p y₀) (p y)),
        (∀ t, p (β t) = α t) → ∀ η, continued α η →
          (Filter.Germ.ofFun ((η 1) ∘ p) : Filter.Germ (𝓝 y) ComplexProjectiveLine) =
            Filter.Germ.ofFun D) ∧
      (∀ D' : C(Y, ComplexProjectiveLine), localForm D' →
        ∃! a : ComplexMobiusTransformation, ∀ y, D' y = a.apply (D y)) ∧
      (∃! H : deck p →* G, ∀ γ : deck p, ∀ y,
        D ((γ : Y ≃ₜ Y) y) = (H γ).val (D y)) ∧
      (∀ (c : OpenPartialHomeomorph Y ((Fin q → ℝ) × ℂ)) y,
        y ∈ c.source → ∀ i, p y ∈ (b i).source →
        ContDiffAt ℝ 1 (fun z ↦ b i (p (c.symm z))) (c y) →
        Function.Bijective (fderiv ℝ (fun z ↦ b i (p (c.symm z))) (c y)) →
        ∃ k : Fin 2,
          D y ∈ complexProjectiveLineChartSource k ∧
          DifferentiableAt ℝ (fun z ↦ complexProjectiveLineChartFun k (D (c.symm z)))
            (c y) ∧
          Function.Surjective
            (fderiv ℝ (fun z ↦ complexProjectiveLineChartFun k (D (c.symm z))) (c y))) ∧
      (∀ (j : ℂ → Y) (W : Set ℂ), IsOpen W → ContinuousOn j W →
        (∀ z ∈ W, ∃ i, ∃ a : OpenPartialHomeomorph ℂ ℂ,
          z ∈ a.source ∧ a.source ⊆ W ∧
          MapsTo j a.source (p ⁻¹' (b i).source) ∧
          EqOn a (fun w ↦ (b i (p (j w))).2) a.source ∧
          DifferentiableOn ℂ a a.source) →
        ∀ z ∈ W, ∃ e : OpenPartialHomeomorph ℂ ComplexProjectiveLine,
          z ∈ e.source ∧ e.source ⊆ W ∧ EqOn e (fun w ↦ D (j w)) e.source ∧
          ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ e e.source ∧
          ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ e.symm e.target ∧
          ∃ i, p (j z) ∈ (b i).source ∧
            deriv (fun w ↦ (b i (p (j w))).2) z ≠ 0) := by
  classical
  intro τ initial localForm compatible continued plaqueLink G
  have hM_lpc : LocallyPathConnectedSpace M :=
    transverseSource_locallyPathConnectedSpace q b hcover
  let : LocallyPathConnectedSpace M := hM_lpc
  have hY_lpc : LocallyPathConnectedSpace Y :=
    locallyPathConnectedSpace_of_isLocalHomeomorph hp.isLocalHomeomorph
  let : LocallyPathConnectedSpace Y := hY_lpc
  
  
  let indexAt : M → ι := fun x ↦ Classical.choose (hcover x)
  have hindex : ∀ x, x ∈ (b (indexAt x)).source :=
    fun x ↦ Classical.choose_spec (hcover x)
  have hlocal' : ∀ i j x, x ∈ (b i).source ∩ (b j).source →
      ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ N ⊆ (b i).source ∩ (b j).source ∧
        ∃ g : MobiusGroup, ∀ y ∈ N,
          ((b j y).2 : OnePoint ℂ) = g.apply ((b i y).2 : OnePoint ℂ) := by
    intro i j x hx
    obtain ⟨g, hg⟩ := hlocal i j x hx
    obtain ⟨N, hNsub, hNopen, hxN⟩ := mem_nhds_iff.mp hg
    refine ⟨N ∩ ((b i).source ∩ (b j).source),
      hNopen.inter ((b i).open_source.inter (b j).open_source), ⟨hxN, hx⟩,
      inter_subset_right, complexMobiusToMobiusGroup g, ?_⟩
    intro y hy
    have he := congrArg (OnePoint.equivProjectivization ℂ).symm (hNsub hy.1)
    simpa only [complexMobiusToMobiusGroup_intertwines,
      complexProjectiveLineFinite_to_onePoint] using he
  obtain ⟨t, htOff, htLocal, htContinuous, htAgrees, htSelf, htComp, htUnique,
    A, hAb, hAi, hAt⟩ :=
    projectiveLocalGermsEffectiveCocycle b indexAt hindex hlocal'
  obtain ⟨Z, hZbase, hZindex, hZchange, hZcover⟩ := flatProjectiveFrameCover A
  have hi₀A : p y₀ ∈ (A.chart i₀).source := by
    rw [hAb]
    exact hi₀
  have hinitial_section := transverse_mobius_initial_section A Z hZbase hZindex hZchange
    hZcover p hp y₀ i₀ g₀ hi₀A
  obtain ⟨sinitial, hsi0, hsiproj, hsiev⟩ := hinitial_section
  have hlocal_initial := transverse_mobius_section_local_form A Z hZbase hZindex hZchange
    p hp.continuous sinitial hsiproj
  let ev : Z.TotalSpace → OnePoint ℂ :=
    fun z ↦ z.2.apply ((A.chart (A.indexAt z.1) z.1).2 : OnePoint ℂ)
  let D₀ : C(Y, ComplexProjectiveLine) :=
    ⟨fun y ↦ (OnePoint.equivProjectivization ℂ) (ev (sinitial y)), by
      exact NativeProjectiveTopology.continuous_onePoint_projectivization.comp
        ((flatProjectiveFrameEvaluation A Z hZbase hZindex hZchange
          (fun g ↦ mobiusGroup_continuous_apply g)).1.comp sinitial.continuous)⟩
  have hlocalD : localForm D₀ := by
    intro y
    obtain ⟨i, g, U, hUo, hyU, hUsub, hEq⟩ := hlocal_initial y
    refine ⟨i, g, U, hUo, hyU, ?_, ?_⟩
    · simpa only [hAb] using hUsub
    · change EqOn D₀ _ U at hEq
      simpa only [hAb, τ] using hEq
  have hlabel₀ : (Z.localTriv i₀ (sinitial y₀)).2 = complexMobiusToMobiusGroup g₀ := by
    rw [hsi0, Z.localTriv_apply, hZchange, hZindex]
    simp
  have hneighborhood : ∃ U : Set Y, IsOpen U ∧ y₀ ∈ U ∧
      EqOn D₀ (fun w ↦ g₀.apply (τ i₀ (p w))) U := by
    obtain ⟨U, hUo, hyU, _, hEq⟩ := transverse_mobius_section_initial_local_form
      A Z hZbase hZindex hZchange p hp.continuous sinitial hsiproj
      y₀ i₀ g₀ hi₀A hlabel₀
    refine ⟨U, hUo, hyU, ?_⟩
    change EqOn D₀ _ U at hEq
    simpa only [hAb, τ] using hEq
  have hcompat : compatible D₀ := by
    refine ⟨hlocalD, ?_⟩
    rw [show (initial ∘ p) = fun w ↦ g₀.apply (τ i₀ (p w)) by rfl]
    exact transverse_mobius_germ_eqOn hneighborhood.choose_spec.1
      hneighborhood.choose_spec.2.1 hneighborhood.choose_spec.2.2
  let rep : Z.TotalSpace → M → ComplexProjectiveLine := fun z w ↦
    (mobiusGroupToComplexMobius z.2).apply
      (complexProjectiveLineFinite ((A.chart (A.indexAt z.proj) w).2))
  have hrep0 : rep (sinitial y₀) =ᶠ[𝓝 (p y₀)] initial := by
    have he := transverse_mobius_frame_germ A Z hZindex hZchange
      (sinitial y₀) i₀ (by rw [hsiproj]; exact hi₀A)
    rw [hsiproj, hlabel₀] at he
    filter_upwards [he] with w hw
    apply (OnePoint.equivProjectivization ℂ).symm.injective
    have hwrep : rep (sinitial y₀) w =
        (mobiusGroupToComplexMobius (complexMobiusToMobiusGroup g₀)).apply
          (complexProjectiveLineFinite ((A.chart i₀ w).2)) := by
      simpa only [rep, hsiproj] using hw
    rw [hwrep,
      mobiusGroupToComplexMobius_apply, Equiv.symm_apply_apply,
      complexMobiusToMobiusGroup_intertwines]
    simp only [τ, hAb]
  have hcanonical : ∀ {x : M} (α : Path (p y₀) x)
      (s : C(unitInterval, Z.TotalSpace)),
      (∀ t, (s t).proj = α t) → s 0 = sinitial y₀ →
      continued α (fun t ↦ rep (s t)) := by
    intro x α s hs hs0
    refine ⟨Filter.Germ.coe_eq.mpr (by simpa only [hs0] using hrep0), ?_⟩
    intro t
    obtain ⟨T,hT,ht,i,g,U,hU,htU,hsub,h⟩ :=
      transverse_mobius_frame_continuation_g4 A Z hZbase hZindex hZchange
        α α.continuous s hs t
    refine ⟨T,hT,ht,i,g,U,hU,htU,?_,?_⟩
    · simpa only [hAb] using hsub
    · intro u hu
      refine ⟨(h u hu).1, Filter.Germ.coe_eq.mpr ?_⟩
      simpa only [rep, τ, hAb] using (h u hu).2
  have hrepEval : ∀ y, (rep (sinitial y) ∘ p) =ᶠ[𝓝 y] D₀ := by
    intro y
    obtain ⟨T,hT,hyT,i,g,U,hU,hyU,hsub,h⟩ :=
      transverse_mobius_frame_continuation_g4 A Z hZbase hZindex hZchange
        p hp.continuous sinitial hsiproj y
    have he := ((h y hyT).2).comp_tendsto hp.continuous.continuousAt
    filter_upwards [he, hT.mem_nhds hyT] with w hw hwT
    change rep (sinitial y) (p w) = _
    change rep (sinitial y) (p w) = _ at hw
    rw [hw]
    have hw' := Filter.EventuallyEq.eq_of_nhds (h w hwT).2
    change g.apply (complexProjectiveLineFinite ((A.chart i (p w)).2)) =
      (OnePoint.equivProjectivization ℂ) (ev (sinitial w))
    rw [← hw']
    change (mobiusGroupToComplexMobius (show MobiusGroup from (sinitial w).2)).apply _ = _
    rw [mobiusGroupToComplexMobius_apply, complexProjectiveLineFinite_to_onePoint]
    simp only [ev, hsiproj]
  constructor
  · refine ⟨D₀, hcompat, ?_⟩
    intro D' hD'
    apply ContinuousMap.coe_injective
    apply transverse_projective_eq_of_initial_germ A p hp.continuous hp.isOpenMap
      D' D₀ ?_ ?_ y₀ (hD'.2.trans hcompat.2.symm)
    · simpa only [localForm, τ, ← hAb] using hD'.1
    · simpa only [localForm, τ, ← hAb] using hlocalD
  intro D hD
  have hDD : D = D₀ := by
    apply ContinuousMap.coe_injective
    apply transverse_projective_eq_of_initial_germ A p hp.continuous hp.isOpenMap
      D D₀ ?_ ?_ y₀ (hD.2.trans hcompat.2.symm)
    · simpa only [localForm, τ, ← hAb] using hD.1
    · simpa only [localForm, τ, ← hAb] using hlocalD
  have hcontEq : ∀ {x : M} (α : Path (p y₀) x) η η',
      continued α η → continued α η' → ∀ t,
      (Filter.Germ.ofFun (η t) : Filter.Germ (𝓝 (α t)) ComplexProjectiveLine) =
        Filter.Germ.ofFun (η' t) := by
    intro x α η η' hη hη'
    apply transverse_projective_continuation_unique A α α.continuous η η'
      (by simpa only [τ, ← hAb] using hη.2)
      (by simpa only [τ, ← hAb] using hη'.2) 0
    rw [α.source]
    exact hη.1.trans hη'.1.symm
  have hcomparison : ∀ D' : C(Y, ComplexProjectiveLine), localForm D' →
      ∃! a : ComplexMobiusTransformation, ∀ y, D' y = a.apply (D y) := by
    intro D' hD'
    exact transverse_projective_comparison A p hp.continuous hp.isOpenMap D D'
      (by simpa only [localForm, τ, ← hAb] using hD.1)
      (by simpa only [localForm, τ, ← hAb] using hD') y₀
  refine ⟨?_, ?_, ?_, ?_, hcomparison,
    transverse_mobius_deck_holonomy q b p D hD.1 hcomparison,
    transverse_mobius_submersion q b hlocal p hp.continuous D hD.1, ?_⟩
  · intro y
    apply Set.Subset.antisymm
    · exact transverse_projective_fiber_component_subset_plaque_chain b p
        hp.isLocalHomeomorph D hD.1 y
    · intro z hz
      induction hz with
      | refl => exact mem_connectedComponentIn rfl
      | @tail z w hyz hzw ih =>
        obtain ⟨i, β, hβ⟩ := hzw
        have hconst : ∀ t, D (β t) = D z := by
          have hc := transverse_projective_constant_on_plaque A p hp.continuous D
            (by simpa only [localForm, τ, ← hAb] using hD.1)
            β β.continuous i 0
            (by intro t; simpa only [hAb] using (hβ t).1)
            (by intro t; simpa only [hAb, Path.source] using (hβ t).2)
          simpa only [Path.source] using hc
        have hzD : D z = D y := connectedComponentIn_subset (D ⁻¹' {D y}) y ih
        have hsub : Set.range β ⊆ D ⁻¹' {D y} := by
          rintro v ⟨t, rfl⟩
          exact (hconst t).trans hzD
        have hw : w ∈ connectedComponentIn (D ⁻¹' {D y}) z :=
          (isConnected_range β.continuous).2.subset_connectedComponentIn
            ⟨0, β.source⟩ hsub ⟨1, β.target⟩
        rwa [connectedComponentIn_eq ih]
  · intro x α
    constructor
    · let s := hZcover.liftPath α.toContinuousMap (sinitial y₀)
        (α.source.trans (hsiproj y₀).symm)
      exact ⟨fun t ↦ rep (s t), hcanonical α s
        (fun t ↦ congrFun (hZcover.liftPath_lifts ..) t) (hZcover.liftPath_zero ..)⟩
    · intro η η' hη hη'
      apply transverse_projective_continuation_unique A α α.continuous η η'
        (by simpa only [τ, ← hAb] using hη.2)
        (by simpa only [τ, ← hAb] using hη'.2) 0
      rw [α.source]
      exact hη.1.trans hη'.1.symm
  · intro x α β hαβ η η' hη hη'
    let sa := hZcover.liftPath α.toContinuousMap (sinitial y₀)
      (α.source.trans (hsiproj y₀).symm)
    let sb := hZcover.liftPath β.toContinuousMap (sinitial y₀)
      (β.source.trans (hsiproj y₀).symm)
    have hsa : continued α (fun t ↦ rep (sa t)) :=
      hcanonical α sa (fun t ↦ congrFun (hZcover.liftPath_lifts ..) t)
        (hZcover.liftPath_zero ..)
    have hsb : continued β (fun t ↦ rep (sb t)) :=
      hcanonical β sb (fun t ↦ congrFun (hZcover.liftPath_lifts ..) t)
        (hZcover.liftPath_zero ..)
    have hend : sa 1 = sb 1 := hZcover.liftPath_apply_one_eq_of_homotopicRel
      hαβ (sinitial y₀) _ _
    have ha := hcontEq α η (fun t ↦ rep (sa t)) hη hsa 1
    have hb := hcontEq β η' (fun t ↦ rep (sb t)) hη' hsb 1
    rw [α.target] at ha
    rw [β.target] at hb
    exact ha.trans (hend ▸ hb.symm)
  · intro y β α hβα η hη
    let s : C(unitInterval, Z.TotalSpace) := sinitial.comp β.toContinuousMap
    have hs : continued α (fun t ↦ rep (s t)) :=
      hcanonical α s (fun t ↦ (hsiproj (β t)).trans (hβα t))
        (by simp [s])
    have he := hcontEq α η (fun t ↦ rep (s t)) hη hs 1
    rw [α.target] at he
    apply Filter.Germ.coe_eq.mpr
    have he' := (Filter.Germ.coe_eq.mp he).comp_tendsto hp.continuous.continuousAt
    have hsy : s 1 = sinitial y := by simp [s]
    rw [hsy] at he'
    exact he'.trans (hDD ▸ hrepEval y)
  · intro j W hW hj hcharts z hz
    obtain ⟨i,a,hza,haW,hja,haeq,ha⟩ := hcharts z hz
    have hji : p (j z) ∈ (b i).source := hja hza
    obtain ⟨k,gk,U,hU,hjzU,hUsub,hDU⟩ := hD.1 (j z)
    obtain ⟨gt,hgt⟩ := hlocal i k (p (j z)) ⟨hji,hUsub hjzU⟩
    let g : ComplexMobiusTransformation :=
      ⟨gt.val.trans gk.val, by
        obtain ⟨B,hB⟩ := gk.property
        obtain ⟨C,hC⟩ := gt.property
        refine ⟨B * C, ?_⟩
        intro w
        change gk.val (gt.val w) = (B * C) • w
        rw [hB,hC,mul_smul]⟩
    have hjz : ContinuousAt j z := (hj z hz).continuousAt (hW.mem_nhds hz)
    have heq : (fun w ↦ D (j w)) =ᶠ[𝓝 z]
        (fun w ↦ g.apply (complexProjectiveLineFinite (a w))) := by
      have ht := (hp.continuous.continuousAt.comp hjz).eventually hgt
      filter_upwards [hjz.eventually (hU.mem_nhds hjzU), ht,
        a.open_source.mem_nhds hza] with w hwU htw hwa
      change D (j w) = gk.apply (gt.apply (complexProjectiveLineFinite (a w)))
      rw [hDU hwU]
      change gk.apply (complexProjectiveLineFinite ((b k (p (j w))).2)) = _
      dsimp only [Function.comp_apply] at htw
      rw [htw, haeq hwa]
    obtain ⟨N,hNsub,hN,hzN⟩ := mem_nhds_iff.mp heq
    let r := a.restr N
    have hzr : z ∈ r.source := by
      change z ∈ a.source ∩ interior N
      simpa only [hN.interior_eq] using (show z ∈ a.source ∩ N from ⟨hza,hzN⟩)
    have hrsub : r.source ⊆ a.source := inter_subset_left
    have hrN : r.source ⊆ N := fun w hw ↦ interior_subset hw.2
    have hainv : DifferentiableOn ℂ a.symm a.target := by
      intro w hw
      exact (a.hasDerivAt_symm hw
        (lebl_scalar_deriv_ne_zero a.open_source ha a.injOn _ (a.map_target hw))
        (ha.differentiableAt (a.open_source.mem_nhds (a.map_target hw))).hasDerivAt
        ).differentiableAt.differentiableWithinAt
    let ar : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ∞ :=
      { toPartialEquiv := r.toPartialEquiv
        open_source := r.open_source
        open_target := r.open_target
        contMDiffOn_toFun := (ha.contDiffOn a.open_source).contMDiffOn.mono hrsub
        contMDiffOn_invFun := (hainv.contDiffOn a.open_target).contMDiffOn.mono
          (by intro w hw; exact hw.1) }
    let scalar : PartialDiffeomorph 𝓘(ℂ) (complexModel 1) ℂ (ComplexModel 1) ∞ :=
      { toPartialEquiv := canonicalPlaneCoordinate.symm.toPartialEquiv
        open_source := canonicalPlaneCoordinate.symm.open_source
        open_target := canonicalPlaneCoordinate.symm.open_target
        contMDiffOn_toFun := canonicalPlaneCoordinate_properties.2.1.2
        contMDiffOn_invFun := canonicalPlaneCoordinate_properties.2.1.1 }
    have hcatlas : complexProjectiveLineChart 1 ∈
        maximalAtlas (complexModel 1) ∞ ComplexProjectiveLine :=
      subset_maximalAtlas ⟨1, rfl⟩
    let chart : PartialDiffeomorph (complexModel 1) (complexModel 1)
        (ComplexModel 1) ComplexProjectiveLine ∞ :=
      { toPartialEquiv := (complexProjectiveLineChart 1).symm.toPartialEquiv
        open_source := (complexProjectiveLineChart 1).symm.open_source
        open_target := (complexProjectiveLineChart 1).symm.open_target
        contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas hcatlas
        contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hcatlas }
    obtain ⟨ag,hag,_⟩ := complex_mobius_psl_normalization g
    let action : Diffeomorph (complexModel 1) (complexModel 1)
        ComplexProjectiveLine ComplexProjectiveLine ∞ :=
      { toEquiv := MulAction.toPerm ag
        contMDiff_toFun := projective_special_linear_action_contMDiff ag
        contMDiff_invFun := projective_special_linear_action_contMDiff ag⁻¹ }
    let e := ((ar.trans scalar).trans chart).trans action.toPartialDiffeomorph
    have hsource : e.source = r.source := by
      ext w
      simp [e, Diffeomorph.toPartialDiffeomorph, scalar, chart, action,
        ar, canonicalPlaneCoordinate, complexProjectiveLineChart]
    have hefun (w : ℂ) : e w = g.apply (complexProjectiveLineFinite (a w)) := by
      change ag • (complexProjectiveLineChartInv 1 (fun _ ↦ a w)) = _
      exact hag _
    refine ⟨e.toOpenPartialHomeomorph, ?_, ?_, ?_,
      e.contMDiffOn_toFun, e.contMDiffOn_invFun, i,hji,?_⟩
    · change z ∈ e.source
      rw [hsource]
      exact hzr
    · change e.source ⊆ W
      rw [hsource]
      exact hrsub.trans haW
    · intro w hw
      have hwN : w ∈ N := hrN (hsource ▸ hw)
      exact (hefun w).trans (hNsub hwN).symm
    · have hderiv : deriv a z ≠ 0 := lebl_scalar_deriv_ne_zero a.open_source ha a.injOn z hza
      have heqa : (a : ℂ → ℂ) =ᶠ[𝓝 z] (fun w ↦ (b i (p (j w))).2) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨a.source,a.open_source.mem_nhds hza,haeq⟩
      rwa [← heqa.deriv_eq]

end HolomorphicAnosov
