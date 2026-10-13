import HolomorphicAnosov.Geometry.TransverseMobiusPlaqueConstancy
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- In a Euclidean product chart, sufficiently close points with the same transverse
coordinate are joined by a path in that plaque. (Thurston, §4.8, p. 63) -/
theorem product_chart_local_plaque_paths
    {Y E F : Type*} [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace F] (c : OpenPartialHomeomorph Y (E × F)) (y : Y)
    (hy : y ∈ c.source) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ U ⊆ c.source ∧
      ∀ z ∈ U, (c z).2 = (c y).2 →
        ∃ β : Path y z, ∀ t, β t ∈ c.source ∧ (c (β t)).2 = (c y).2 := by
  obtain ⟨P, Q, hPo, hyP, hQo, hyQ, hPQ⟩ :=
    mem_nhds_prod_iff'.mp (c.open_target.mem_nhds (c.map_source hy))
  obtain ⟨r, hr, hrP⟩ := Metric.mem_nhds_iff.mp (hPo.mem_nhds hyP)
  let B : Set (E × F) := Metric.ball (c y).1 r ×ˢ Q
  have hB : IsOpen B := Metric.isOpen_ball.prod hQo
  have hBt : B ⊆ c.target := fun v hv ↦ hPQ ⟨hrP hv.1, hv.2⟩
  have hyB : c y ∈ B := ⟨Metric.mem_ball_self hr, hyQ⟩
  let U := c.symm '' B
  have hU : IsOpen U := c.symm.isOpen_image_of_subset_source hB hBt
  have hUs : U ⊆ c.source := by
    rintro z ⟨v, hv, rfl⟩
    exact c.map_target (hBt hv)
  refine ⟨U, hU, ⟨c y, hyB, c.left_inv hy⟩, hUs, ?_⟩
  intro z hz hcoord
  have hzB : c z ∈ B := by
    obtain ⟨v, hv, rfl⟩ := hz
    simpa only [c.right_inv (hBt hv)] using hv
  obtain ⟨γ, hγ⟩ := (Metric.isPathConnected_ball hr).joinedIn (c y).1 hyB.1 (c z).1 hzB.1
  have hδ : ∀ t, (γ t, (c y).2) ∈ c.target :=
    fun t ↦ hBt ⟨hγ t, hyQ⟩
  have hcont : Continuous (fun t ↦ c.symm (γ t, (c y).2)) :=
    c.symm.continuousOn.comp_continuous (γ.continuous.prodMk continuous_const) hδ
  let β : Path y z := ⟨⟨_, hcont⟩, by
    simp only [γ.source, Prod.eta, c.left_inv hy], by
    change c.symm (γ 1, (c y).2) = z
    rw [γ.target, ← hcoord, Prod.eta, c.left_inv (hUs hz)]⟩
  refine ⟨β, ?_⟩
  intro t
  refine ⟨c.map_target (hδ t), ?_⟩
  change (c (c.symm (γ t, (c y).2))).2 = (c y).2
  rw [c.right_inv (hδ t)]

/-- Each point has a neighborhood in which points of its fiber under a locally projective
map are joined to it by lifted plaque paths. -/
theorem transverse_projective_fiber_local_plaque_paths
    {X Y E ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ι → OpenPartialHomeomorph X (E × ℂ)) (p : Y → X)
    (hp : IsLocalHomeomorph p) (D : Y → ComplexProjectiveLine)
    (hD : ∀ y, ∃ i, ∃ a : ComplexMobiusTransformation, ∃ U : Set Y,
      IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (b i).source ∧
        EqOn D (fun w ↦ a.apply (complexProjectiveLineFinite ((b i (p w)).2))) U)
    (y : Y) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∀ z ∈ U, D z = D y →
      ∃ i, ∃ β : Path y z, ∀ t,
        p (β t) ∈ (b i).source ∧ (b i (p (β t))).2 = (b i (p y)).2 := by
  obtain ⟨i, g, V, hV, hyV, hVsub, hEq⟩ := hD y
  obtain ⟨e, hye, he⟩ := hp y
  let c := (e.trans (b i)).restr V
  have hcs : c.source = (e.source ∩ p ⁻¹' (b i).source) ∩ V := by
    simp only [c, OpenPartialHomeomorph.restr_source' _ V hV,
      OpenPartialHomeomorph.trans_source, ← he]
  have hcapply (w : Y) : c w = b i (p w) := by
    simp only [c, OpenPartialHomeomorph.restr_apply, OpenPartialHomeomorph.trans_apply, ← he]
  have hyc : y ∈ c.source := by rw [hcs]; exact ⟨⟨hye, hVsub hyV⟩, hyV⟩
  obtain ⟨U, hU, hyU, hUc, hpath⟩ := product_chart_local_plaque_paths c y hyc
  refine ⟨U, hU, hyU, ?_⟩
  intro z hz hDz
  have hzV : z ∈ V := (hcs ▸ hUc hz).2
  have hfin : complexProjectiveLineFinite ((b i (p z)).2) =
      complexProjectiveLineFinite ((b i (p y)).2) :=
    g.val.injective ((hEq hzV).symm.trans (hDz.trans (hEq hyV)))
  have hcoords : (c z).2 = (c y).2 := by
    simp only [hcapply]
    apply OnePoint.coe_injective
    simpa only [complexProjectiveLineFinite_to_onePoint] using
      congrArg (OnePoint.equivProjectivization ℂ).symm hfin
  obtain ⟨β, hβ⟩ := hpath z hz hcoords
  refine ⟨i, β, ?_⟩
  intro t
  refine ⟨(hcs ▸ (hβ t).1).1.2, ?_⟩
  simpa only [hcapply] using (hβ t).2

/-- An equivalence relation whose classes are locally full in a subspace contains every
connected component of that subspace in a single class. -/
theorem connectedComponentIn_subset_of_local_relation
    {Y : Type*} [TopologicalSpace Y] (F : Set Y) (r : Y → Y → Prop)
    (hrefl : ∀ z, r z z) (hsymm : ∀ z w, r z w → r w z)
    (htrans : ∀ z w v, r z w → r w v → r z v)
    (hlocal : ∀ z ∈ F, ∃ U : Set Y, IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, w ∈ F → r z w)
    (y : Y) (hy : y ∈ F) : connectedComponentIn F y ⊆ {z | r y z} := by
  let S : Set F := {z | r y z}
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨U, hU, hzU, hUr⟩ := hlocal z z.property
    apply mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hzU)
    intro w hw
    exact htrans y z w hz (hUr w hw w.property)
  have hSc : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨U, hU, hzU, hUr⟩ := hlocal z z.property
    apply mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hzU)
    intro w hw hwr
    exact hz (htrans y w z hwr (hsymm z w (hUr w hw w.property)))
  have hcl : IsClopen S := ⟨isOpen_compl_iff.mp hSc, hSo⟩
  intro z hz
  rw [connectedComponentIn_eq_image hy] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact hcl.connectedComponent_subset (hrefl y) hw

/-- Every point of a fiber connected component is reachable by a finite chain of lifted
plaque paths. (Thurston, §4.8, p. 63) -/
theorem transverse_projective_fiber_component_subset_plaque_chain
    {X Y E ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ι → OpenPartialHomeomorph X (E × ℂ)) (p : Y → X)
    (hp : IsLocalHomeomorph p) (D : Y → ComplexProjectiveLine)
    (hD : ∀ y, ∃ i, ∃ a : ComplexMobiusTransformation, ∃ U : Set Y,
      IsOpen U ∧ y ∈ U ∧ U ⊆ p ⁻¹' (b i).source ∧
        EqOn D (fun w ↦ a.apply (complexProjectiveLineFinite ((b i (p w)).2))) U)
    (y : Y) :
    let link : Y → Y → Prop := fun z w ↦
      ∃ i, ∃ β : Path z w, ∀ t,
        p (β t) ∈ (b i).source ∧ (b i (p (β t))).2 = (b i (p z)).2
    connectedComponentIn (D ⁻¹' {D y}) y ⊆ {z | Relation.ReflTransGen link y z} := by
  intro link
  have hs : ∀ z w, link z w → link w z := by
    intro z w h
    obtain ⟨i, β, hβ⟩ := h
    have hw : (b i (p w)).2 = (b i (p z)).2 := by simpa using (hβ 1).2
    refine ⟨i, β.symm, ?_⟩
    intro t
    exact ⟨(hβ (unitInterval.symm t)).1, ((hβ (unitInterval.symm t)).2).trans hw.symm⟩
  apply connectedComponentIn_subset_of_local_relation (D ⁻¹' {D y})
    (Relation.ReflTransGen link) (fun _ ↦ .refl) ?_ (fun _ _ _ ↦ Relation.ReflTransGen.trans)
    ?_ y rfl
  · intro z w h
    induction h with
    | refl => exact .refl
    | tail hab hbc ih => exact ih.head (hs _ _ hbc)
  · intro z hz
    obtain ⟨U, hU, hzU, hpath⟩ := transverse_projective_fiber_local_plaque_paths b p hp D hD z
    refine ⟨U, hU, hzU, ?_⟩
    intro w hw hwF
    exact .single (hpath w hw ((show D w = D y from hwF).trans (show D z = D y from hz).symm))

end HolomorphicAnosov.Ghys


