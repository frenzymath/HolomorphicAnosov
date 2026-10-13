import HolomorphicAnosov.Geometry.TransverseMobiusUniqueness

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- Projective germs with locally fixed representatives and the same initial germ
have unique continuation along a connected parameter space. (Thurston, §3.5, pp. 34–35) -/
theorem effective_projective_continuation_unique
    {X L ι K : Type*} [TopologicalSpace X] [TopologicalSpace L]
    [TopologicalSpace K] [PreconnectedSpace K]
    (A : FlatProjectiveAtlas X L ι) (α : K → X) (hα : Continuous α)
    (η η' : K → X → OnePoint ℂ)
    (hη : ∀ t, ∃ T : Set K, IsOpen T ∧ t ∈ T ∧ ∃ i, ∃ a : MobiusGroup,
      ∃ U : Set X, IsOpen U ∧ α t ∈ U ∧ U ⊆ (A.chart i).source ∧
        ∀ s ∈ T, α s ∈ U ∧ η s =ᶠ[𝓝 (α s)]
          (fun w ↦ a.apply ((A.chart i w).2 : OnePoint ℂ)))
    (hη' : ∀ t, ∃ T : Set K, IsOpen T ∧ t ∈ T ∧ ∃ i, ∃ a : MobiusGroup,
      ∃ U : Set X, IsOpen U ∧ α t ∈ U ∧ U ⊆ (A.chart i).source ∧
        ∀ s ∈ T, α s ∈ U ∧ η' s =ᶠ[𝓝 (α s)]
          (fun w ↦ a.apply ((A.chart i w).2 : OnePoint ℂ)))
    (t₀ : K) (h₀ : η t₀ =ᶠ[𝓝 (α t₀)] η' t₀) :
    ∀ t, η t =ᶠ[𝓝 (α t)] η' t := by
  let S : Set K := {t | η t =ᶠ[𝓝 (α t)] η' t}
  have hprop : ∀ t, ∃ T : Set K, IsOpen T ∧ t ∈ T ∧
      ∀ s ∈ T, s ∈ S → T ⊆ S := by
    intro t
    obtain ⟨T₁, hT₁, ht₁, i, a, U, hU, htU, hUsub, hηU⟩ := hη t
    obtain ⟨T₂, hT₂, ht₂, j, b, V, hV, htV, hVsub, hηV⟩ := hη' t
    have htij : α t ∈ (A.chart i).source ∩ (A.chart j).source :=
      ⟨hUsub htU, hVsub htV⟩
    have htransAt : ContinuousAt (A.transition i j) (α t) :=
      (A.transition_continuous i j).continuousAt
        (((A.chart i).open_source.inter (A.chart j).open_source).mem_nhds htij)
    have hevent : ∀ᶠ x in 𝓝 (α t), A.transition i j x = A.transition i j (α t) :=
      htransAt.eventually ((isOpen_discrete {A.transition i j (α t)}).mem_nhds rfl)
    obtain ⟨W, hWsub, hW, htW⟩ := mem_nhds_iff.mp hevent
    let N := U ∩ V ∩ W
    have hN : IsOpen N := (hU.inter hV).inter hW
    have htN : α t ∈ N := ⟨⟨htU, htV⟩, htW⟩
    let T := T₁ ∩ T₂ ∩ α ⁻¹' N
    have hT : IsOpen T := (hT₁.inter hT₂).inter (hN.preimage hα)
    have htrans : EqOn (fun w ↦ b.apply ((A.chart j w).2 : OnePoint ℂ))
        (fun w ↦ (b * A.transition i j (α t)).apply ((A.chart i w).2 : OnePoint ℂ)) N := by
      intro w hw
      change b.apply _ = b.apply ((A.transition i j (α t)).apply _)
      rw [A.transition_agrees i j w ⟨hUsub hw.1.1, hVsub hw.1.2⟩, hWsub hw.2]
    refine ⟨T, hT, ⟨⟨ht₁, ht₂⟩, htN⟩, ?_⟩
    intro s hs hsS
    have heq : (fun w ↦ a.apply ((A.chart i w).2 : OnePoint ℂ)) =ᶠ[𝓝 (α s)]
        (fun w ↦ b.apply ((A.chart j w).2 : OnePoint ℂ)) :=
      (hηU s hs.1.1).2.symm.trans (hsS.trans (hηV s hs.1.2).2)
    obtain ⟨Q, hQsub, hQ, hsQ⟩ := mem_nhds_iff.mp heq
    have hab : a = b * A.transition i j (α t) := by
      apply mobius_eq_of_chart_eqOn (A.chart i) id IsOpenMap.id
        (N ∩ Q) (hN.inter hQ) ⟨α s, hs.2, hsQ⟩ (fun w hw ↦ hUsub hw.1.1.1)
      intro w hw
      exact (hQsub hw.2).trans (htrans hw.1)
    intro u hu
    apply (hηU u hu.1.1).2.trans
    apply EventuallyEq.trans ?_ (hηV u hu.1.2).2.symm
    filter_upwards [hN.mem_nhds hu.2] with w hw
    rw [hab]
    exact (htrans hw).symm
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨T, hT, htT, hp⟩ := hprop t
    exact mem_of_superset (hT.mem_nhds htT) (hp t htT ht)
  have hSc : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨T, hT, htT, hp⟩ := hprop t
    apply mem_of_superset (hT.mem_nhds htT)
    intro s hs hsS
    exact ht (hp s hs hsS htT)
  have hS : S = univ := (show IsClopen S from ⟨isOpen_compl_iff.mp hSc, hSo⟩).eq_univ ⟨t₀, h₀⟩
  intro t
  change t ∈ S
  rw [hS]
  trivial

/-- Projective-line germs with locally fixed Möbius representatives and the same initial
germ coincide along a connected parameter space. -/
theorem transverse_projective_continuation_unique
    {X L ι K : Type*} [TopologicalSpace X] [TopologicalSpace L]
    [TopologicalSpace K] [PreconnectedSpace K]
    (A : FlatProjectiveAtlas X L ι) (α : K → X) (hα : Continuous α)
    (η η' : K → X → ComplexProjectiveLine)
    (hη : ∀ t, ∃ T : Set K, IsOpen T ∧ t ∈ T ∧ ∃ i, ∃ a : ComplexMobiusTransformation,
      ∃ U : Set X, IsOpen U ∧ α t ∈ U ∧ U ⊆ (A.chart i).source ∧
        ∀ s ∈ T, α s ∈ U ∧ (Filter.Germ.ofFun (η s) : Filter.Germ (𝓝 (α s)) _ ) =
          Filter.Germ.ofFun (fun w ↦ a.apply (complexProjectiveLineFinite ((A.chart i w).2))))
    (hη' : ∀ t, ∃ T : Set K, IsOpen T ∧ t ∈ T ∧ ∃ i, ∃ a : ComplexMobiusTransformation,
      ∃ U : Set X, IsOpen U ∧ α t ∈ U ∧ U ⊆ (A.chart i).source ∧
        ∀ s ∈ T, α s ∈ U ∧ (Filter.Germ.ofFun (η' s) : Filter.Germ (𝓝 (α s)) _ ) =
          Filter.Germ.ofFun (fun w ↦ a.apply (complexProjectiveLineFinite ((A.chart i w).2))))
    (t₀ : K) (h₀ : (Filter.Germ.ofFun (η t₀) : Filter.Germ (𝓝 (α t₀)) _) =
      Filter.Germ.ofFun (η' t₀)) : ∀ t, (Filter.Germ.ofFun (η t) : Filter.Germ (𝓝 (α t)) _) =
        Filter.Germ.ofFun (η' t) := by
  let ep := (OnePoint.equivProjectivization ℂ).symm
  let ηe : K → X → OnePoint ℂ := fun t x ↦ ep (η t x)
  let ηe' : K → X → OnePoint ℂ := fun t x ↦ ep (η' t x)
  have hηe : ∀ t, ∃ T : Set K, IsOpen T ∧ t ∈ T ∧ ∃ i, ∃ a : MobiusGroup,
      ∃ U : Set X, IsOpen U ∧ α t ∈ U ∧ U ⊆ (A.chart i).source ∧
        ∀ s ∈ T, α s ∈ U ∧ ηe s =ᶠ[𝓝 (α s)]
          (fun w ↦ a.apply ((A.chart i w).2 : OnePoint ℂ)) := by
    intro t; obtain ⟨T,hT,ht,i,a,U,hU,htU,hsub,h⟩ := hη t
    refine ⟨T,hT,ht,i,complexMobiusToMobiusGroup a,U,hU,htU,hsub,?_⟩
    intro s hs
    refine ⟨(h s hs).1, ?_⟩
    have he := Filter.Germ.coe_eq.mp (h s hs).2
    filter_upwards [he] with w hw
    simpa only [ηe,ep,Function.comp_apply,complexMobiusToMobiusGroup_intertwines,
      complexProjectiveLineFinite_to_onePoint] using congrArg ep hw
  have hηe' : ∀ t, ∃ T : Set K, IsOpen T ∧ t ∈ T ∧ ∃ i, ∃ a : MobiusGroup,
      ∃ U : Set X, IsOpen U ∧ α t ∈ U ∧ U ⊆ (A.chart i).source ∧
        ∀ s ∈ T, α s ∈ U ∧ ηe' s =ᶠ[𝓝 (α s)]
          (fun w ↦ a.apply ((A.chart i w).2 : OnePoint ℂ)) := by
    intro t; obtain ⟨T,hT,ht,i,a,U,hU,htU,hsub,h⟩ := hη' t
    refine ⟨T,hT,ht,i,complexMobiusToMobiusGroup a,U,hU,htU,hsub,?_⟩
    intro s hs
    refine ⟨(h s hs).1, ?_⟩
    have he := Filter.Germ.coe_eq.mp (h s hs).2
    filter_upwards [he] with w hw
    simpa only [ηe',ep,Function.comp_apply,complexMobiusToMobiusGroup_intertwines,
      complexProjectiveLineFinite_to_onePoint] using congrArg ep hw
  have heq0 : ηe t₀ =ᶠ[𝓝 (α t₀)] ηe' t₀ := by
    filter_upwards [Filter.Germ.coe_eq.mp h₀] with w hw
    exact congrArg ep hw
  have heq := effective_projective_continuation_unique A α hα ηe ηe' hηe hηe' t₀ heq0
  intro t
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [heq t] with w hw
  exact (show η t w = η' t w from (OnePoint.equivProjectivization ℂ).symm.injective hw)

end HolomorphicAnosov.Ghys
