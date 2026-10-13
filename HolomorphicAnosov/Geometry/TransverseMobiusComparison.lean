import HolomorphicAnosov.Geometry.TransverseMobiusUniqueness

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- Two developing maps for a flat projective atlas differ by a unique effective Möbius
transformation. (Thurston, §3.5, pp. 34–35) -/
theorem effective_projective_comparison
    {X Y L ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    [PreconnectedSpace Y]
    (A : FlatProjectiveAtlas X L ι) (p : Y → X) (hp : Continuous p)
    (hpo : IsOpenMap p) (f g : Y → OnePoint ℂ)
    (hf : ∀ y, ∃ i, ∃ a : MobiusGroup, ∃ U : Set Y,
      IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (A.chart i).source ∧
        EqOn f (fun w ↦ a.apply ((A.chart i (p w)).2 : OnePoint ℂ)) U)
    (hg : ∀ y, ∃ i, ∃ a : MobiusGroup, ∃ U : Set Y,
      IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (A.chart i).source ∧
        EqOn g (fun w ↦ a.apply ((A.chart i (p w)).2 : OnePoint ℂ)) U)
    (y₀ : Y) : ∃! c : MobiusGroup, ∀ y, g y = c.apply (f y) := by
  obtain ⟨i, a, U, hU, hxU, hUsub, hfeq⟩ := hf y₀
  obtain ⟨j, b, V, hV, hxV, hVsub, hgeq⟩ := hg y₀
  have hxij : p y₀ ∈ (A.chart i).source ∩ (A.chart j).source :=
    ⟨hUsub hxU, hVsub hxV⟩
  have htransAt : ContinuousAt (A.transition i j) (p y₀) :=
    (A.transition_continuous i j).continuousAt
      (((A.chart i).open_source.inter (A.chart j).open_source).mem_nhds hxij)
  have ht : ∀ᶠ z in 𝓝 (p y₀), A.transition i j z = A.transition i j (p y₀) :=
    htransAt.eventually ((isOpen_discrete {A.transition i j (p y₀)}).mem_nhds rfl)
  have htp : ∀ᶠ w in 𝓝 y₀, A.transition i j (p w) = A.transition i j (p y₀) :=
    hp.continuousAt ht
  let c : MobiusGroup := (b * A.transition i j (p y₀)) * a⁻¹
  have hca : c * a = b * A.transition i j (p y₀) := by simp [c, mul_assoc]
  have hcf : ∀ y, ∃ k, ∃ d : MobiusGroup, ∃ W : Set Y,
      IsOpen W ∧ y ∈ W ∧ W ⊆ p ⁻¹' (A.chart k).source ∧
        EqOn (fun w ↦ c.apply (f w))
          (fun w ↦ d.apply ((A.chart k (p w)).2 : OnePoint ℂ)) W := by
    intro y
    obtain ⟨k, d, W, hW, hyW, hWsub, heq⟩ := hf y
    refine ⟨k, c * d, W, hW, hyW, hWsub, ?_⟩
    intro w hw
    change c.apply (f w) = c.apply (d.apply _)
    exact congrArg c.apply (heq hw)
  have hinit : g =ᶠ[𝓝 y₀] (fun w ↦ c.apply (f w)) := by
    filter_upwards [hU.mem_nhds hxU, hV.mem_nhds hxV, htp] with w hwU hwV hwT
    rw [hfeq hwU, hgeq hwV]
    change b.apply ((A.chart j (p w)).2 : OnePoint ℂ) =
      (c * a).apply ((A.chart i (p w)).2 : OnePoint ℂ)
    rw [hca]
    change b.apply ((A.chart j (p w)).2 : OnePoint ℂ) =
      b.apply ((A.transition i j (p y₀)).apply ((A.chart i (p w)).2 : OnePoint ℂ))
    rw [A.transition_agrees i j (p w) ⟨hUsub hwU, hVsub hwV⟩, hwT]
  have hall : ∀ y, g y = c.apply (f y) :=
    congrFun (effective_projective_eq_of_initial_germ A p hp hpo g
      (fun w ↦ c.apply (f w)) hg hcf y₀ hinit)
  refine ⟨c, hall, ?_⟩
  intro d hd
  have hda : d * a = c * a := by
    apply mobius_eq_of_chart_eqOn (A.chart i) p hpo U hU ⟨y₀, hxU⟩ hUsub
    intro w hw
    change d.apply (a.apply _) = c.apply (a.apply _)
    have hwf : f w = a.apply ((A.chart i (p w)).2 : OnePoint ℂ) := hfeq hw
    rw [← hwf]
    exact (hd w).symm.trans (hall w)
  exact mul_right_cancel hda

/-- Two projective developing maps for a flat atlas differ by a unique global Möbius
transformation. (Thurston, §3.5, pp. 34–35) -/
theorem transverse_projective_comparison
    {X Y L ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    [PreconnectedSpace Y]
    (A : FlatProjectiveAtlas X L ι) (p : Y → X) (hp : Continuous p)
    (hpo : IsOpenMap p) (f g : Y → ComplexProjectiveLine)
    (hf : ∀ y, ∃ i, ∃ a : ComplexMobiusTransformation, ∃ U : Set Y,
      IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (A.chart i).source ∧
        EqOn f (fun w ↦ a.apply (complexProjectiveLineFinite ((A.chart i (p w)).2))) U)
    (hg : ∀ y, ∃ i, ∃ a : ComplexMobiusTransformation, ∃ U : Set Y,
      IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (A.chart i).source ∧
        EqOn g (fun w ↦ a.apply (complexProjectiveLineFinite ((A.chart i (p w)).2))) U)
    (y₀ : Y) : ∃! c : ComplexMobiusTransformation, ∀ y, g y = c.apply (f y) := by
  let ep := (OnePoint.equivProjectivization ℂ).symm
  have convert (d : Y → ComplexProjectiveLine)
      (hd : ∀ y, ∃ i, ∃ a : ComplexMobiusTransformation, ∃ U : Set Y,
        IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (A.chart i).source ∧
          EqOn d (fun w ↦ a.apply (complexProjectiveLineFinite ((A.chart i (p w)).2))) U) :
      ∀ y, ∃ i, ∃ a : MobiusGroup, ∃ U : Set Y,
        IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (A.chart i).source ∧
          EqOn (ep ∘ d) (fun w ↦ a.apply ((A.chart i (p w)).2 : OnePoint ℂ)) U := by
    intro y
    obtain ⟨i, a, U, hU, hyU, hsub, heq⟩ := hd y
    refine ⟨i, complexMobiusToMobiusGroup a, U, hU, hyU, hsub, ?_⟩
    intro w hw
    have he := congrArg ep (heq hw)
    simpa only [ep, Function.comp_apply, complexMobiusToMobiusGroup_intertwines,
      complexProjectiveLineFinite_to_onePoint] using he
  obtain ⟨c, hc, hcu⟩ := effective_projective_comparison A p hp hpo
    (ep ∘ f) (ep ∘ g) (convert f hf) (convert g hg) y₀
  refine ⟨mobiusGroupToComplexMobius c, ?_, ?_⟩
  · intro y
    apply ep.injective
    simpa only [ep, Function.comp_apply, mobiusGroupToComplexMobius_apply,
      Equiv.symm_apply_apply] using hc y
  · intro d hd
    have hdc : complexMobiusToMobiusGroup d = c := by
      apply hcu
      intro y
      have he := congrArg ep (hd y)
      simpa only [ep, Function.comp_apply, complexMobiusToMobiusGroup_intertwines] using he
    apply Subtype.ext
    apply Equiv.ext
    intro z
    change d.apply z = (mobiusGroupToComplexMobius c).apply z
    apply ep.injective
    simp only [ep, complexMobiusToMobiusGroup_intertwines,
      mobiusGroupToComplexMobius_apply, Equiv.symm_apply_apply, hdc]

end HolomorphicAnosov.Ghys

