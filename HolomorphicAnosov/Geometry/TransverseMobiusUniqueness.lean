import HolomorphicAnosov.Geometry.TransverseMobiusLocalForm
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- Effective Möbius transformations agreeing on infinitely many finite points agree
everywhere. -/
theorem mobius_eq_of_infinite_finite_eq (g h : MobiusGroup) (V : Set ℂ)
    (hVinf : V.Infinite)
    (heq : ∀ z ∈ V, g.apply (z : OnePoint ℂ) = h.apply (z : OnePoint ℂ)) : g = h := by
  obtain ⟨A, hA⟩ := g.property
  obtain ⟨B, hB⟩ := h.property
  have heq' : ∀ z : ℂ, z ∈ V → A • (z : OnePoint ℂ) = B • (z : OnePoint ℂ) := by
    intro z hz
    have e := heq z hz
    change g.val (z : OnePoint ℂ) = h.val (z : OnePoint ℂ) at e
    rw [← hA, ← hB] at e
    exact e
  let Q : GL (Fin 2) ℂ := B⁻¹ * A
  have hfix : ∀ z : ℂ, z ∈ V → Q • (z : OnePoint ℂ) = z := by
    intro z hz
    dsimp [Q]
    rw [mul_smul]
    rw [heq' z hz]
    simp
  have hroot : Set.Infinite {z : ℂ | Polynomial.IsRoot (Matrix.GeneralLinearGroup.fixpointPolynomial Q) z} := by
    apply hVinf.mono
    intro z hz
    exact (Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff).2 (hfix z hz)
  have hpoly : Matrix.GeneralLinearGroup.fixpointPolynomial Q = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ hroot
  have hq10 : Q 1 0 = 0 := by
    simpa [Matrix.GeneralLinearGroup.fixpointPolynomial] using congrArg (Polynomial.coeff · 2) hpoly
  have hfixall : ∀ z : ℂ, Q • (z : OnePoint ℂ) = z := by
    intro z
    apply (Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff).1
    rw [hpoly]
    simp
  have hinf : Q • (OnePoint.infty : OnePoint ℂ) = OnePoint.infty := OnePoint.smul_infty_eq_self_iff.2 hq10
  have hQid : (MulAction.toPermHom (GL (Fin 2) ℂ) (OnePoint ℂ)) Q = 1 := by
    apply Equiv.Perm.ext
    intro z
    cases z with
    | infty => simpa using hinf
    | coe z => simpa using hfixall z
  let φ : GL (Fin 2) ℂ → Equiv.Perm (OnePoint ℂ) :=
    MulAction.toPermHom (GL (Fin 2) ℂ) (OnePoint ℂ)
  have hBAperm : (φ B)⁻¹ * φ A = 1 := by
    simpa only [Q, φ, map_mul, map_inv] using hQid
  have hAB : φ A = φ B := by
    have hmul := congrArg (fun p : Equiv.Perm (OnePoint ℂ) ↦ φ B * p) hBAperm
    simpa [← mul_assoc] using hmul

  apply Subtype.ext
  exact hA.symm.trans (hAB.trans hB)

/-- Möbius transformations agree if their transverse-coordinate expressions agree on a
nonempty open set in an open pullback of a product chart. -/
theorem mobius_eq_of_chart_eqOn
    {X Y L : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (c : OpenPartialHomeomorph X (L × ℂ)) (p : Y → X) (hp : IsOpenMap p)
    (U : Set Y) (hU : IsOpen U) (hne : U.Nonempty) (hsub : U ⊆ p ⁻¹' c.source)
    (g h : MobiusGroup)
    (heq : ∀ y ∈ U, g.apply ((c (p y)).2 : OnePoint ℂ) =
      h.apply ((c (p y)).2 : OnePoint ℂ)) : g = h := by
  have hpsub : p '' U ⊆ c.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact hsub hy
  have hopen : IsOpen (c '' (p '' U)) :=
    c.isOpen_image_of_subset_source (hp U hU) hpsub
  obtain ⟨y, hy⟩ := hne
  have hmem : c (p y) ∈ c '' (p '' U) := ⟨p y, ⟨y, hy, rfl⟩, rfl⟩
  obtain ⟨P, V, _, hP, hVo, hV, hPV⟩ := mem_nhds_prod_iff'.mp (hopen.mem_nhds hmem)
  apply mobius_eq_of_infinite_finite_eq g h V (infinite_of_mem_nhds _ (hVo.mem_nhds hV))
  intro z hz
  have hzmem : ((c (p y)).1, z) ∈ c '' (p '' U) := hPV ⟨hP, hz⟩
  obtain ⟨x, ⟨w, hw, rfl⟩, hc⟩ := hzmem
  have hcz := congrArg Prod.snd hc
  simpa only [hcz] using heq w hw

/-- Local propagation of germ equality gives global equality on a connected space. -/
theorem eq_of_locally_propagating_germs
    {Y T : Type*} [TopologicalSpace Y] [PreconnectedSpace Y]
    (f g : Y → T)
    (hprop : ∀ x, ∃ U : Set Y, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, f =ᶠ[𝓝 y] g → EqOn f g U)
    (y₀ : Y) (h₀ : f =ᶠ[𝓝 y₀] g) : f = g := by
  let S : Set Y := {y | f =ᶠ[𝓝 y] g}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hSc : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hxU, hpropU⟩ := hprop x
    apply mem_of_superset (hU.mem_nhds hxU)
    intro y hy hyeq
    apply hx
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact hpropU y hy hyeq hz
  have hS : S = univ := (show IsClopen S from ⟨hSc, hSo⟩).eq_univ ⟨y₀, h₀⟩
  funext y
  have hy : f =ᶠ[𝓝 y] g := by
    change y ∈ S
    rw [hS]
    trivial
  exact hy.self_of_nhds



/-- Locally projective evaluations with the same initial germ coincide on a connected base. -/
theorem effective_projective_eq_of_initial_germ
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
    (y₀ : Y) (h₀ : f =ᶠ[𝓝 y₀] g) : f = g := by
  apply eq_of_locally_propagating_germs f g ?_ y₀ h₀
  intro x
  obtain ⟨i, a, U, hU, hxU, hUsub, hfeq⟩ := hf x
  obtain ⟨j, b, V, hV, hxV, hVsub, hgeq⟩ := hg x
  have hxij : p x ∈ (A.chart i).source ∩ (A.chart j).source := ⟨hUsub hxU, hVsub hxV⟩
  have htransAt : ContinuousAt (A.transition i j) (p x) :=
    (A.transition_continuous i j).continuousAt
      (((A.chart i).open_source.inter (A.chart j).open_source).mem_nhds hxij)
  have ht : ∀ᶠ z in 𝓝 (p x), A.transition i j z = A.transition i j (p x) :=
    htransAt.eventually ((isOpen_discrete {A.transition i j (p x)}).mem_nhds rfl)
  have htp : ∀ᶠ w in 𝓝 x, A.transition i j (p w) = A.transition i j (p x) :=
    hp.continuousAt ht
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp htp
  let N := U ∩ V ∩ W
  have hN : IsOpen N := (hU.inter hV).inter hW
  have hNsub : N ⊆ p ⁻¹' (A.chart i).source := fun w hw ↦ hUsub hw.1.1
  have hgN : EqOn g (fun w ↦ (b * A.transition i j (p x)).apply
      ((A.chart i (p w)).2 : OnePoint ℂ)) N := by
    intro w hw
    calc
      g w = b.apply ((A.chart j (p w)).2 : OnePoint ℂ) := hgeq hw.1.2
      _ = b.apply ((A.transition i j (p x)).apply
          ((A.chart i (p w)).2 : OnePoint ℂ)) := by
        rw [A.transition_agrees i j (p w) ⟨hUsub hw.1.1, hVsub hw.1.2⟩, hWsub hw.2]
      _ = _ := rfl
  refine ⟨N, hN, ⟨⟨hxU, hxV⟩, hxW⟩, ?_⟩
  intro y hy heq
  obtain ⟨Q, hQsub, hQ, hyQ⟩ := mem_nhds_iff.mp heq
  have hab : a = b * A.transition i j (p x) := by
    apply mobius_eq_of_chart_eqOn (A.chart i) p hpo (N ∩ Q) (hN.inter hQ)
      ⟨y, hy, hyQ⟩ (fun w hw ↦ hNsub hw.1)
    intro w hw
    exact (hfeq hw.1.1.1).symm.trans ((hQsub hw.2).trans (hgN hw.1))
  intro w hw
  rw [hfeq hw.1.1, hgN hw, hab]



/-- Projective maps with local Möbius chart expressions and equal initial germs agree
on a connected covering space. -/
theorem transverse_projective_eq_of_initial_germ
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
    (y₀ : Y) (h₀ : (Filter.Germ.ofFun f : Filter.Germ (𝓝 y₀) ComplexProjectiveLine) =
      Filter.Germ.ofFun g) : f = g := by
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
  have heq : ep ∘ f = ep ∘ g :=
    effective_projective_eq_of_initial_germ A p hp hpo (ep ∘ f) (ep ∘ g)
      (convert f hf) (convert g hg) y₀ (by
        filter_upwards [Filter.Germ.coe_eq.mp h₀] with y hy
        exact congrArg ep hy)
  funext y
  exact ep.injective (congrFun heq y)


end HolomorphicAnosov.Ghys
