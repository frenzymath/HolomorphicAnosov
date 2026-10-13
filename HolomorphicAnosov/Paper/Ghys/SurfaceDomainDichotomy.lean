import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingInjectiveBaseStage
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingStageInduction
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Topology.SurfaceInjectivityKernel
import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveProduct
import HolomorphicAnosov.Paper.Ghys.CompleteLiftedProjectiveLeaves
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology
import Mathlib.Topology.Maps.Proper.Basic

/-!
Global injectivity of the ordered surface developing map and classification of its range
as either a homeomorphism graph complement or a product of two punctured projective lines.
(Ghys, Lemma 5.2, pp. 599–600; Theorem A, p. 600)
-/

open Set _root_.Topology
open scoped ContDiff

namespace HolomorphicAnosov.SurfaceDomainClassificationKernel

theorem graph_complement_ne_punctured_product
    {P : Type*} [TopologicalSpace P] [Nontrivial P]
    (h : P ≃ₜ P) (a b : P) :
    ({z : P × P | z.2 ≠ h z.1} : Set (P × P)) ≠ ({a}ᶜ ×ˢ {b}ᶜ) := by
  intro he
  obtain ⟨q, hq⟩ := exists_ne (h a)
  have hm : (a, q) ∈ ({z : P × P | z.2 ≠ h z.1} : Set (P × P)) := hq
  rw [he] at hm
  exact hm.1 (by simp)

/-- A set with continuous punctured-fibre descriptions in both coordinates, each with at most
one exceptional base point, is either the complement of a homeomorphism graph or a product
of two punctured spaces. Exactly one alternative holds. -/
theorem classify_two_punctured_fibre_descriptions
    {P : Type*} [TopologicalSpace P] [Nontrivial P]
    (E : Set (P × P)) (F G : Set P)
    (hF : F = ∅ ∨ ∃ a, F = {a}) (hG : G = ∅ ∨ ∃ b, G = {b})
    (u : C({p : P // p ∉ F}, P)) (v : C({q : P // q ∉ G}, P))
    (hEu : E = {z | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩})
    (hEv : E = {z | ∃ hq : z.2 ∉ G, z.1 ≠ v ⟨z.2, hq⟩}) :
    Xor (∃ h : P ≃ₜ P, E = {z | z.2 ≠ h z.1})
      (∃ a b : P, E = ({a}ᶜ ×ˢ {b}ᶜ)) := by
  classical
  have hrow (p b : P) (hp : p ∉ F) (hb : b ∈ G) : u ⟨p, hp⟩ = b := by
    by_contra h
    have hm : (p, b) ∈ E := by
      rw [hEu]
      exact ⟨hp, Ne.symm h⟩
    rw [hEv] at hm
    obtain ⟨hg, _⟩ := hm
    exact hg hb
  have hcol (a q : P) (ha : a ∈ F) (hq : q ∉ G) : v ⟨q, hq⟩ = a := by
    by_contra h
    have hm : (a, q) ∈ E := by
      rw [hEv]
      exact ⟨hq, Ne.symm h⟩
    rw [hEu] at hm
    obtain ⟨hf, _⟩ := hm
    exact hf ha
  have hdisjoint : ¬ ((∃ h : P ≃ₜ P, E = {z | z.2 ≠ h z.1}) ∧
      (∃ a b : P, E = ({a}ᶜ ×ˢ {b}ᶜ))) := by
    rintro ⟨⟨h, hh⟩, ⟨a, b, hab⟩⟩
    exact graph_complement_ne_punctured_product h a b (hh.symm.trans hab)
  have halt : (∃ h : P ≃ₜ P, E = {z | z.2 ≠ h z.1}) ∨
      (∃ a b : P, E = ({a}ᶜ ×ˢ {b}ᶜ)) := by
    rcases hF with hF | ⟨a, hF⟩ <;> rcases hG with hG | ⟨b, hG⟩
    · subst F
      subst G
      let U : P → P := fun p ↦ u ⟨p, by simp⟩
      let V : P → P := fun q ↦ v ⟨q, by simp⟩
      have heq (p q : P) : q ≠ U p ↔ p ≠ V q := by
        have he := congrArg (fun A : Set (P × P) ↦ (p, q) ∈ A) (hEu.symm.trans hEv)
        simpa [U, V] using he
      have hleft (p : P) : V (U p) = p := by
        by_contra hn
        have hn' : p ≠ V (U p) := Ne.symm hn
        exact ((heq p (U p)).mpr hn') rfl
      have hright (q : P) : U (V q) = q := by
        by_contra hn
        have hn' : q ≠ U (V q) := Ne.symm hn
        exact ((heq (V q) q).mp hn') rfl
      let h : P ≃ₜ P :=
        { toFun := U, invFun := V, left_inv := hleft, right_inv := hright
          continuous_toFun := u.continuous.comp (continuous_id.subtype_mk _)
          continuous_invFun := v.continuous.comp (continuous_id.subtype_mk _) }
      exact Or.inl ⟨h, by simpa [h, U] using hEu⟩
    · subst F
      subst G
      obtain ⟨q, hqb⟩ := exists_ne b
      have hq : q ∉ ({b} : Set P) := by simpa using hqb
      let p := v ⟨q, hq⟩
      have hp : p ∉ (∅ : Set P) := by simp
      have hm : (p, q) ∈ E := by
        rw [hEu]
        exact ⟨hp, by rw [hrow p b hp (by simp)]; exact hqb⟩
      rw [hEv] at hm
      obtain ⟨hq', hn⟩ := hm
      exact False.elim (hn rfl)
    · subst F
      subst G
      obtain ⟨p, hpa⟩ := exists_ne a
      have hp : p ∉ ({a} : Set P) := by simpa using hpa
      let q := u ⟨p, hp⟩
      have hq : q ∉ (∅ : Set P) := by simp
      have hm : (p, q) ∈ E := by
        rw [hEv]
        exact ⟨hq, by rw [hcol a q (by simp) hq]; exact hpa⟩
      rw [hEu] at hm
      obtain ⟨hp', hn⟩ := hm
      exact False.elim (hn rfl)
    · subst F
      subst G
      refine Or.inr ⟨a, b, ?_⟩
      ext z
      rw [hEu]
      constructor
      · rintro ⟨hp, hn⟩
        refine ⟨hp, ?_⟩
        rw [hrow z.1 b hp (by simp)] at hn
        exact hn
      · rintro ⟨hp, hq⟩
        exact ⟨hp, by rw [hrow z.1 b hp (by simp)]; exact hq⟩
  rcases halt with hl | hr
  · exact Or.inl ⟨hl, fun hr ↦ hdisjoint ⟨hl, hr⟩⟩
  · exact Or.inr ⟨hr, fun hl ↦ hdisjoint ⟨hl, hr⟩⟩

end HolomorphicAnosov.SurfaceDomainClassificationKernel

namespace HolomorphicAnosov.Ghys

universe u v w

namespace SurfaceDomainPreparation

/-- Any two members of a nonempty open cover of a preconnected space are joined by a finite
chain of nonempty intersections. (Ghys, p. 599) -/
theorem open_cover_intersection_chains {X ι : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty)
    (hcover : (⋃ i, U i) = Set.univ) (a b : ι) :
    Relation.ReflTransGen (fun i j ↦ (U i ∩ U j).Nonempty) a b := by
  have hc : IsPreconnected (⋃ i, U i) := hcover.symm ▸ isPreconnected_univ
  exact (hc.transGen_of_iUnion hopen a b (hne a) (hne b)).to_reflTransGen

/-- A finite intersection chain of connected sets extends to a sequence joining its endpoints,
with nonempty consecutive intersections and connected positive prefix unions. -/
theorem sequence_of_intersection_chain {X ι : Type*} [TopologicalSpace X]
    (U : ι → Set X) (hconn : ∀ i, IsConnected (U i)) {a b : ι}
    (hchain : Relation.ReflTransGen (fun i j ↦ (U i ∩ U j).Nonempty) a b) :
    ∃ (x : ℕ → ι) (n : ℕ), x 0 = a ∧ x n = b ∧
      (∀ i, (U (x i) ∩ U (x (i + 1))).Nonempty) ∧
      (∀ k, 1 ≤ k → IsConnected (⋃ i ∈ Finset.range k, U (x i))) := by
  classical
  have hseq : ∃ (x : ℕ → ι) (n : ℕ), x 0 = a ∧ x n = b ∧
      ∀ i, (U (x i) ∩ U (x (i + 1))).Nonempty := by
    induction hchain with
    | refl =>
      refine ⟨fun _ ↦ a, 0, rfl, rfl, fun _ ↦ ?_⟩
      obtain ⟨z, hz⟩ := (hconn a).nonempty
      exact ⟨z, hz, hz⟩
    | @tail b c _ hbc ih =>
      obtain ⟨x, n, hx0, hxn, hx⟩ := ih
      let y : ℕ → ι := fun i ↦ if i ≤ n then x i else c
      refine ⟨y, n + 1, by simpa [y] using hx0, by simp [y], ?_⟩
      intro i
      by_cases hi : i < n
      · simpa [y, show i ≤ n by omega, show i + 1 ≤ n by omega] using hx i
      · by_cases hieq : i = n
        · subst i
          simpa [y, hxn] using hbc
        · obtain ⟨z, hz⟩ := (hconn c).nonempty
          have hi' : ¬ i ≤ n := by omega
          have hi'' : ¬ i + 1 ≤ n := by omega
          simpa [y, hi', hi''] using (show (U c ∩ U c).Nonempty from ⟨z, hz, hz⟩)
  obtain ⟨x, n, hx0, hxn, hx⟩ := hseq
  refine ⟨x, n, hx0, hxn, hx, ?_⟩
  intro k hk
  have h := IsConnected.biUnion_of_chain (s := fun i ↦ U (x i))
    (t := Set.Iio k) ⟨0, by change 0 < k; omega⟩ Set.ordConnected_Iio
    (fun i _ ↦ hconn (x i)) (fun i _ _ ↦ hx i)
  simpa only [← Finset.coe_range, Finset.mem_coe] using h

/-- The total space of a covering map to a Hausdorff space is Hausdorff. -/
theorem covering_t2Space {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {p : X → Y} (hp : IsCoveringMap p) :
    T2Space X := by
  constructor
  intro x y hxy
  by_cases h : p x = p y
  · exact hp.isSeparatedMap x y h hxy
  · obtain ⟨U, V, hU, hV, hx, hy, hdisj⟩ := t2_separation h
    exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous,
      hV.preimage hp.continuous, hx, hy, hdisj.preimage p⟩

/-- A function into a compact space is continuous if its graph complement over its domain
is open. (Ghys, p. 600) -/
theorem continuous_of_open_graph_complement {P : Type*} [TopologicalSpace P]
    [CompactSpace P] (F : Set P) (u : {p : P // p ∉ F} → P)
    (E : Set (P × P)) (hE : IsOpen E)
    (hgraph : E = {z | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩}) :
    Continuous u := by
  apply continuous_of_isClosed_graph
  have hopen : IsOpen ((fun z : {p : P // p ∉ F} × P ↦ (z.1.val, z.2)) ⁻¹' E) :=
    hE.preimage (continuous_subtype_val.prodMap continuous_id)
  have heq : Function.graph u =
      ((fun z : {p : P // p ∉ F} × P ↦ (z.1.val, z.2)) ⁻¹' E)ᶜ := by
    ext z
    simp [Function.graph, hgraph, eq_comm, z.1.property]
  rw [heq]
  exact hopen.isClosed_compl

/-- For an injective development whose leaves partition the source and map onto punctured
vertical lines, every nonempty vertical fibre of its range is a punctured line.
(Ghys, p. 600) -/
theorem punctured_fibre_of_injective_complete_leaves {X P : Type*} [Infinite P]
    (D : X → P × P) (L : X → Set X) (hinj : Function.Injective D)
    (hself : ∀ x, x ∈ L x)
    (hpartition : ∀ x y z, z ∈ L x → z ∈ L y → L x = L y)
    (hfull : ∀ x, ∃ c, D '' L x = {q | q.1 = (D x).1 ∧ q.2 ≠ c}) (x : X) :
    ∃ c, ∀ q, ((D x).1, q) ∈ Set.range D ↔ q ≠ c := by
  classical
  obtain ⟨c, hc⟩ := hfull x
  refine ⟨c, fun q ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨d, hd⟩ := hfull y
    obtain ⟨r, hr⟩ := (Set.finite_singleton c |>.union (Set.finite_singleton d)).exists_notMem
    have hrc : r ≠ c := fun h ↦ hr (Or.inl h)
    have hrd : r ≠ d := fun h ↦ hr (Or.inr h)
    have hx : ((D x).1, r) ∈ D '' L x := by rw [hc]; exact ⟨rfl, hrc⟩
    have hyp : (D y).1 = (D x).1 := by simpa only using congrArg (fun z : P × P ↦ z.1) hy
    have hy' : ((D x).1, r) ∈ D '' L y := by rw [hd]; exact ⟨hyp.symm, hrd⟩
    obtain ⟨z, hz, hDz⟩ := hx
    obtain ⟨w, hw, hDw⟩ := hy'
    have hzw : z = w := hinj (hDz.trans hDw.symm)
    have hL : L x = L y := hpartition x y z hz (hzw.symm ▸ hw)
    have hDy : D y ∈ D '' L x := Set.mem_image_of_mem D (hL.symm ▸ hself y)
    rw [hc] at hDy
    simpa only [hy] using hDy.2
  · intro hq
    have hq' : ((D x).1, q) ∈ D '' L x := by rw [hc]; exact ⟨rfl, hq⟩
    exact Set.image_subset_range D _ hq'

/-- An injective development with complete punctured vertical leaves, an open range, and a
punctured horizontal line in its range has a continuous graph-complement description
with at most one exceptional base point. (Ghys, p. 600) -/
theorem graph_of_injective_complete_leaves {X P : Type*}
    [TopologicalSpace P] [CompactSpace P] [Infinite P]
    (D : X → P × P) (L : X → Set X) (hinj : Function.Injective D)
    (hself : ∀ x, x ∈ L x)
    (hpartition : ∀ x y z, z ∈ L x → z ∈ L y → L x = L y)
    (hfull : ∀ x, ∃ c, D '' L x = {q | q.1 = (D x).1 ∧ q.2 ≠ c})
    (hbase : ∃ a b, ∀ p, p ≠ a → (p, b) ∈ Set.range D)
    (hopen : IsOpen (Set.range D)) :
    ∃ (F : Set P) (u : C({p : P // p ∉ F}, P)),
      (F = ∅ ∨ ∃ pole, F = {pole}) ∧
      Set.range D = {z | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩} := by
  classical
  let F : Set P := {p | ∀ q, (p, q) ∉ Set.range D}
  have hx (p : {p : P // p ∉ F}) : ∃ x, (D x).1 = p.val := by
    have hp : ¬∀ q, (p.val, q) ∉ Set.range D := p.property
    push Not at hp
    obtain ⟨q, x, hx⟩ := hp
    exact ⟨x, congrArg Prod.fst hx⟩
  let x : {p : P // p ∉ F} → X := fun p ↦ Classical.choose (hx p)
  have hxp p : (D (x p)).1 = p.val := Classical.choose_spec (hx p)
  have hc p := punctured_fibre_of_injective_complete_leaves D L hinj hself hpartition hfull (x p)
  choose c hc using hc
  have hgraph : Set.range D = {z | ∃ hp : z.1 ∉ F, z.2 ≠ c ⟨z.1, hp⟩} := by
    ext z
    constructor
    · intro hz
      have hp : z.1 ∉ F := fun h ↦ h z.2 hz
      refine ⟨hp, (hc ⟨z.1, hp⟩ z.2).mp ?_⟩
      simpa only [hxp, Prod.eta] using hz
    · rintro ⟨hp, hq⟩
      have hz := (hc ⟨z.1, hp⟩ z.2).mpr hq
      simpa only [hxp, Prod.eta] using hz
  have hsmall : F = ∅ ∨ ∃ pole, F = {pole} := by
    obtain ⟨a, b, hab⟩ := hbase
    have hsub : F ⊆ {a} := by
      intro p hp
      by_contra hpa
      exact hp b (hab p hpa)
    rcases Set.subset_singleton_iff_eq.mp hsub with h | h
    · exact Or.inl h
    · exact Or.inr ⟨a, h⟩
  exact ⟨F, ⟨c, continuous_of_open_graph_complement F c _ hopen hgraph⟩, hsmall, hgraph⟩

/-- Intersecting connected components of coordinate level sets coincide. -/
theorem coordinate_component_partition {X P : Type*} [TopologicalSpace X]
    (c : X → P) (x y z : X)
    (hx : z ∈ connectedComponentIn {q | c q = c x} x)
    (hy : z ∈ connectedComponentIn {q | c q = c y} y) :
    connectedComponentIn {q | c q = c x} x =
      connectedComponentIn {q | c q = c y} y := by
  have hcx : c z = c x := connectedComponentIn_subset _ x hx
  have hcy : c z = c y := connectedComponentIn_subset _ y hy
  have hF : {q | c q = c x} = {q | c q = c y} := by rw [← hcx, ← hcy]
  rw [← hF] at hy ⊢
  exact (connectedComponentIn_eq hx).trans (connectedComponentIn_eq hy).symm

section NativeCompleteImages
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    {A : OrderedProjectiveProductAtlas.{u, v} f a}
    {X : Type w} [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X]
    [IsManifold (complexModel 2) ∞ X] {p : X → S}
    (D : OrderedProjectiveProductDevelopment A p)
    (hLeaves : CompleteLiftedProjectiveLeaves D)

include hLeaves

/-- Each complete stable developing leaf maps onto a horizontal projective line with one
point removed. -/
theorem complete_stable_image (x : X) : ∃ pole : ComplexProjectiveLine,
    D.developingMap '' stableDevelopingLeaf D x =
      {q | q.1 ≠ pole ∧ q.2 = (D.developingMap x).2} := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  obtain ⟨lift, _, _, _, hrange, pole, e, _, _, _, _, _, hfull⟩ := hLeaves.1 x
  refine ⟨pole, ?_⟩
  rw [← hrange]
  simpa only [← Set.range_comp, Function.comp_def] using hfull

/-- Each complete unstable developing leaf maps onto a vertical projective line with one
point removed. -/
theorem complete_unstable_image (x : X) : ∃ pole : ComplexProjectiveLine,
    D.developingMap '' unstableDevelopingLeaf D x =
      {q | q.1 = (D.developingMap x).1 ∧ q.2 ≠ pole} := by
  let : MetricSpace S := A.metric.replaceTopology A.metric_topology
  obtain ⟨lift, _, _, _, hrange, pole, e, _, _, _, _, _, hfull⟩ := hLeaves.2 x
  refine ⟨pole, ?_⟩
  rw [← hrange]
  simpa only [← Set.range_comp, Function.comp_def] using hfull

/-- An injective development with complete lifted projective leaves has a range described
by a continuous omitted second coordinate, with at most one exceptional first coordinate. -/
theorem native_vertical_graph_of_injective [CompactSpace ComplexProjectiveLine]
    [Infinite ComplexProjectiveLine] (hinj : Function.Injective D.developingMap) :
    ∃ (F : Set ComplexProjectiveLine)
      (u : C({p : ComplexProjectiveLine // p ∉ F}, ComplexProjectiveLine)),
      (F = ∅ ∨ ∃ pole, F = {pole}) ∧
      Set.range D.developingMap = {z | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩} := by
  let : SimplyConnectedSpace X := D.simplyConnected
  let x : X := Classical.choice (inferInstance : Nonempty X)
  apply graph_of_injective_complete_leaves D.developingMap (unstableDevelopingLeaf D) hinj
  · intro y
    exact mem_connectedComponentIn rfl
  · intro y z w hy hz
    exact coordinate_component_partition (fun q ↦ (D.developingMap q).1) y z w hy hz
  · exact complete_unstable_image D hLeaves
  · obtain ⟨a, ha⟩ := complete_stable_image D hLeaves x
    refine ⟨a, (D.developingMap x).2, fun q hq ↦ ?_⟩
    apply Set.image_subset_range D.developingMap (stableDevelopingLeaf D x)
    rw [ha]
    exact ⟨hq, rfl⟩
  · rw [← Set.image_univ]
    exact D.localBiholomorph.isOpenMap _ isOpen_univ

/-- An injective development with complete lifted projective leaves has a range described
by a continuous omitted first coordinate, with at most one exceptional second coordinate. -/
theorem native_horizontal_graph_of_injective [CompactSpace ComplexProjectiveLine]
    [Infinite ComplexProjectiveLine] (hinj : Function.Injective D.developingMap) :
    ∃ (G : Set ComplexProjectiveLine)
      (v : C({q : ComplexProjectiveLine // q ∉ G}, ComplexProjectiveLine)),
      (G = ∅ ∨ ∃ pole, G = {pole}) ∧
      Set.range D.developingMap = {z | ∃ hq : z.2 ∉ G, z.1 ≠ v ⟨z.2, hq⟩} := by
  let : SimplyConnectedSpace X := D.simplyConnected
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let E : X → ComplexProjectiveLine × ComplexProjectiveLine := fun y ↦ (D.developingMap y).swap
  have hEinj : Function.Injective E := fun y z h ↦ hinj (Prod.swap_injective h)
  have hfull (y : X) : ∃ c, E '' stableDevelopingLeaf D y =
      {q | q.1 = (E y).1 ∧ q.2 ≠ c} := by
    obtain ⟨c, hc⟩ := complete_stable_image D hLeaves y
    refine ⟨c, ?_⟩
    calc
      E '' stableDevelopingLeaf D y = Prod.swap ''
          (D.developingMap '' stableDevelopingLeaf D y) :=
        (Set.image_image Prod.swap D.developingMap _).symm
      _ = _ := by
        rw [hc]
        ext ⟨r, s⟩
        simp [E, and_comm, eq_comm]
  have hbase : ∃ a b, ∀ q, q ≠ a → (q, b) ∈ Set.range E := by
    obtain ⟨a, ha⟩ := complete_unstable_image D hLeaves x
    refine ⟨a, (D.developingMap x).1, fun q hq ↦ ?_⟩
    have hq' : ((D.developingMap x).1, q) ∈ D.developingMap '' unstableDevelopingLeaf D x := by
      rw [ha]
      exact ⟨rfl, hq⟩
    obtain ⟨y, _, hy⟩ := hq'
    exact ⟨y, by simp only [E, hy, Prod.swap_prod_mk]⟩
  have hopen : IsOpen (Set.range E) := by
    have hswap : Set.range E = (Homeomorph.prodComm _ _) '' Set.range D.developingMap := by
      rw [← Set.range_comp]
      rfl
    rw [hswap]
    apply (Homeomorph.prodComm _ _).isOpenMap
    rw [← Set.image_univ]
    exact D.localBiholomorph.isOpenMap _ isOpen_univ
  obtain ⟨G, v, hG, hv⟩ := graph_of_injective_complete_leaves E (stableDevelopingLeaf D)
    hEinj (fun _ ↦ mem_connectedComponentIn rfl)
    (fun y z w hy hz ↦ coordinate_component_partition (fun q ↦ (D.developingMap q).2) y z w hy hz)
    hfull hbase hopen
  refine ⟨G, v, hG, ?_⟩
  ext q
  have heq : q ∈ Set.range D.developingMap ↔ q.swap ∈ Set.range E := by
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, Prod.swap_injective hy⟩
  rw [heq, hv]
  rfl

/-- The range of an injective development with complete lifted projective leaves is either
the complement of a projective-line homeomorphism graph or a product of two punctured
projective lines. Exactly one alternative holds. -/
theorem native_dichotomy_of_injective [CompactSpace ComplexProjectiveLine]
    [Infinite ComplexProjectiveLine] (hinj : Function.Injective D.developingMap) :
    Xor
      (∃ h : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine,
        Set.range D.developingMap = {z | z.2 ≠ h z.1})
      (∃ poleS poleU : ComplexProjectiveLine,
        Set.range D.developingMap = ({poleS}ᶜ ×ˢ {poleU}ᶜ)) := by
  let : Nontrivial ComplexProjectiveLine :=
    NativeProjectiveTopology.nontrivial_native_projective_line
  obtain ⟨F, u, hF, hu⟩ := native_vertical_graph_of_injective D hLeaves hinj
  obtain ⟨G, v, hG, hv⟩ := native_horizontal_graph_of_injective D hLeaves hinj
  exact SurfaceDomainClassificationKernel.classify_two_punctured_fibre_descriptions
    (Set.range D.developingMap) F G hF hG u v hu hv

end NativeCompleteImages

/-- Injectivity on every connected positive finite prefix of open unstable saturations
implies global injectivity of the developing map. (Ghys, Lemma 5.2) -/
theorem native_injective_of_finite_prefix_assertion
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {X : Type w} [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X]
    [IsManifold (complexModel 2) ∞ X] {p : X → S}
    (D : OrderedProjectiveProductDevelopment A p)
    (hLeaves : CompleteLiftedProjectiveLeaves D)
    (hfinite : ∀ (x : ℕ → X),
      (∀ i, IsOpen (unstableSaturation D (x i))) →
      (∀ n, 1 ≤ n → IsConnected (⋃ i ∈ Finset.range n, unstableSaturation D (x i))) →
      ∀ n, 1 ≤ n → Set.InjOn D.developingMap
        (⋃ i ∈ Finset.range n, unstableSaturation D (x i))) :
    Function.Injective D.developingMap := by
  let : SimplyConnectedSpace X := D.simplyConnected
  have hbase (x : X) := surface_developing_injective_base_stage A D hLeaves x
  have hopen (x : X) : IsOpen (unstableSaturation D x) := by
    obtain ⟨_, _, _, _, h, _⟩ := hbase x
    exact h
  have hconn (x : X) : IsConnected (unstableSaturation D x) := by
    obtain ⟨_, _, _, _, _, h, _⟩ := hbase x
    exact h
  have hself (x : X) : x ∈ unstableSaturation D x :=
    ⟨x, mem_connectedComponentIn rfl, mem_connectedComponentIn rfl⟩
  have hcover : (⋃ x, unstableSaturation D x) = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    exact fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hself x⟩
  intro y z hyz
  have hchain := open_cover_intersection_chains (unstableSaturation D) hopen
    (fun x ↦ (hconn x).nonempty) hcover y z
  obtain ⟨x, n, hx0, hxn, _, hprefix⟩ :=
    sequence_of_intersection_chain (unstableSaturation D) hconn hchain
  have hi := hfinite x (fun i ↦ hopen (x i)) hprefix (n + 1) (by omega)
  apply hi _ _ hyz
  · exact Set.mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr (by omega), hx0.symm ▸ hself y⟩
  · exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr (by omega), hxn.symm ▸ hself z⟩

/-- The finite-prefix injectivity hypothesis implies global injectivity and exactly one
range description: a homeomorphism graph complement or a product of two punctured
projective lines. -/
theorem native_dichotomy_of_finite_prefix_assertion
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {X : Type w} [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X]
    [IsManifold (complexModel 2) ∞ X] {p : X → S}
    (D : OrderedProjectiveProductDevelopment A p)
    (hLeaves : CompleteLiftedProjectiveLeaves D)
    [CompactSpace ComplexProjectiveLine] [Infinite ComplexProjectiveLine]
    (hfinite : ∀ (x : ℕ → X),
      (∀ i, IsOpen (unstableSaturation D (x i))) →
      (∀ n, 1 ≤ n → IsConnected (⋃ i ∈ Finset.range n, unstableSaturation D (x i))) →
      ∀ n, 1 ≤ n → Set.InjOn D.developingMap
        (⋃ i ∈ Finset.range n, unstableSaturation D (x i))) :
    Function.Injective D.developingMap ∧
      Xor
        (∃ h : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine,
          Set.range D.developingMap = {z | z.2 ≠ h z.1})
        (∃ poleS poleU : ComplexProjectiveLine,
          Set.range D.developingMap = ({poleS}ᶜ ×ˢ {poleU}ᶜ)) := by
  have hinj := native_injective_of_finite_prefix_assertion f a A D hLeaves hfinite
  exact ⟨hinj, native_dichotomy_of_injective D hLeaves hinj⟩

end SurfaceDomainPreparation

/-- The ordered surface developing map is injective, and its range is either the complement
of a projective-line homeomorphism graph or a product of two punctured projective lines.
Exactly one alternative holds. (Ghys, Lemma 5.2, pp. 599–600; Theorem A, p. 600) -/
theorem surface_domain_dichotomy
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {X : Type w} [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X]
    [IsManifold (complexModel 2) ∞ X] {p : X → S}
    (D : OrderedProjectiveProductDevelopment A p)
    (hLeaves : CompleteLiftedProjectiveLeaves D) :
    Function.Injective D.developingMap ∧
      Xor
        (∃ h : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine,
          Set.range D.developingMap = {z | z.2 ≠ h z.1})
        (∃ poleS poleU : ComplexProjectiveLine,
          Set.range D.developingMap = ({poleS}ᶜ ×ˢ {poleU}ᶜ)) := by
  let : T2Space X := SurfaceDomainPreparation.covering_t2Space D.covering
  let : CompactSpace ComplexProjectiveLine :=
    NativeProjectiveTopology.compact_native_projective_line
  let : Infinite ComplexProjectiveLine := Infinite.of_injective
    NativeProjectiveTopology.nativeProjectiveLineHomeomorphOnePoint.symm
    NativeProjectiveTopology.nativeProjectiveLineHomeomorphOnePoint.symm.injective
  exact SurfaceDomainPreparation.native_dichotomy_of_finite_prefix_assertion
    f a A D hLeaves (fun x hopen hprefix n hn ↦
      (surface_developing_injective_finite_prefix f a A p D hLeaves x hopen hprefix n hn).1)

end HolomorphicAnosov.Ghys
