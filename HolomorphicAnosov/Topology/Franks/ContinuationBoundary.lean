import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Path
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Filter Set
open scoped Topology
namespace HolomorphicAnosov.FranksOriginalCover

/-- Franks (1969), Lemma 1.6, p.121, the local-product limit calculation.
Two moving side points converge inside one product box. The mixed box point
lies on their specified leaves, and at-most-one intersection identifies every
existing continuation value with this mixed point. Continuity of the box and
its inverse therefore gives the boundary limit. The local branch incidence
laws and at-most-one intersection are explicit; global same-leaf membership
alone is not silently treated as membership in a single plaque. -/
theorem continuation_tendsto_of_local_product
    {P U V A : Type*} [TopologicalSpace P] [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : P → P → Prop)
    (hunique : ∀ a b z z', Lu a z → Ls b z → Lu a z' → Ls b z' → z = z')
    (e : OpenPartialHomeomorph P (U × V))
    (hcross : ∀ a b, a ∈ e.source → b ∈ e.source →
      ((e a).1, (e b).2) ∈ e.target ∧
        Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    {l : Filter A} {α β θ : A → P} {a b : P}
    (ha : a ∈ e.source) (hb : b ∈ e.source)
    (hα : Tendsto α l (𝓝 a)) (hβ : Tendsto β l (𝓝 b))
    (hθ : ∀ᶠ t in l, Lu (α t) (θ t) ∧ Ls (β t) (θ t)) :
    Tendsto θ l (𝓝 (e.symm ((e a).1, (e b).2))) := by
  have ht := (hcross a b ha hb).1
  have hc : Tendsto (fun t ↦ e.symm ((e (α t)).1, (e (β t)).2)) l
      (𝓝 (e.symm ((e a).1, (e b).2))) :=
    (e.continuousAt_symm ht).tendsto.comp
      ((continuous_fst.tendsto _ |>.comp ((e.continuousAt ha).tendsto.comp hα)).prodMk_nhds
        (continuous_snd.tendsto _ |>.comp ((e.continuousAt hb).tendsto.comp hβ)))
  apply hc.congr'
  filter_upwards [hα (e.open_source.mem_nhds ha), hβ (e.open_source.mem_nhds hb), hθ]
    with t hαt hβt hθt
  obtain ⟨_, hu, hs⟩ := hcross (α t) (β t) hαt hβt
  exact hunique (α t) (β t) _ _ hu hs hθt.1 hθt.2

/-- Franks (1969), Lemma 1.6, p.121, recovery of the two side endpoints
from a convergent corner subsequence. A fixed interior corner `c` and the
moving diagonal `δ` lie in one product box. The existing row and column
values have limits `a,b`; uniqueness identifies those values with the two
mixed box points. Hausdorff uniqueness of limits puts both endpoints inside
the box, and their opposite leaves meet at the diagonal limit `v`.
In particular, endpoint membership in the product box is proved, not assumed. -/
theorem continuation_corner_of_cluster
    {P U V A : Type*} [TopologicalSpace P] [T2Space P]
    [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : Setoid P)
    (hunique : ∀ a b z z', Lu a z → Ls b z → Lu a z' → Ls b z' → z = z')
    (e : OpenPartialHomeomorph P (U × V))
    (hcross : ∀ a b, a ∈ e.source → b ∈ e.source →
      ((e a).1, (e b).2) ∈ e.target ∧
        Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    {l : Filter A} [NeBot l] {α β δ : A → P} {a b c v : P}
    (hc : c ∈ e.source) (hv : v ∈ e.source)
    (hα : Tendsto α l (𝓝 a)) (hβ : Tendsto β l (𝓝 b))
    (hδ : Tendsto δ l (𝓝 v))
    (hrow : ∀ᶠ t in l, Lu c (α t) ∧ Ls (δ t) (α t))
    (hcol : ∀ᶠ t in l, Lu (δ t) (β t) ∧ Ls c (β t)) :
    a ∈ e.source ∧ b ∈ e.source ∧ Lu b v ∧ Ls a v := by
  have ha := tendsto_nhds_unique hα
    (continuation_tendsto_of_local_product Lu Ls hunique e hcross
      hc hv tendsto_const_nhds hδ hrow)
  have hb := tendsto_nhds_unique hβ
    (continuation_tendsto_of_local_product Lu Ls hunique e hcross
      hv hc hδ tendsto_const_nhds hcol)
  rw [ha, hb]
  exact ⟨e.map_target (hcross c v hc hv).1,
    e.map_target (hcross v c hv hc).1,
    Lu.symm (hcross v c hv hc).2.1, Ls.symm (hcross c v hc hv).2.2⟩

private noncomputable def intervalApproach (x : unitInterval) (n : ℕ) : unitInterval :=
  ⟨x.val * (1 - 1 / ((n : ℝ) + 1)), by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hp : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hq : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 hn
    constructor
    · exact mul_nonneg x.property.1 (sub_nonneg.mpr hq)
    · calc x.val * (1 - 1 / ((n : ℝ) + 1)) ≤ x.val :=
            mul_le_of_le_one_right x.property.1 (by linarith)
           _ ≤ 1 := x.property.2⟩

private theorem intervalApproach_lt (x : unitInterval) (hx : 0 < x.val) (n : ℕ) :
    (intervalApproach x n).val < x.val := by
  change x.val * (1 - 1 / ((n : ℝ) + 1)) < x.val
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  nlinarith

private theorem intervalApproach_tendsto (x : unitInterval) :
    Tendsto (intervalApproach x) atTop (𝓝 x) := by
  apply tendsto_subtype_rng.2
  simpa only [intervalApproach, sub_zero, mul_one] using
    (tendsto_const_nhds (x := x.val)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat)

/-- Compact continuation fills the whole rectangle. This is an agent-written
version of Franks (1969), Lemma 1.6, pp.121–122, using a minimum of the sum of
the two coordinates instead of two successive suprema. If a missing point
minimizes that sum, both coordinates are positive because the axes are already
in the domain. Approach it strictly from below in both coordinates. Compactness
provides a convergent subsequence of continuation values. Fix one earlier
corner in a product box about the limit. Both opposite side endpoints have
smaller coordinate sum, so the continuation is already continuous there.
`continuation_corner_of_cluster` recovers the missing intersection, a
contradiction. Openness and continuity of the partial continuation are explicit
inputs, to be obtained from native plaque-chain holonomy. -/
theorem continuation_domain_eq_univ
    {P U V : Type*} [TopologicalSpace P] [T2Space P] [FirstCountableTopology P]
    [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : Setoid P)
    (hunique : ∀ a b z z', Lu a z → Ls b z → Lu a z' → Ls b z' → z = z')
    (hboxes : ∀ v : P, ∃ e : OpenPartialHomeomorph P (U × V), v ∈ e.source ∧
      ∀ a b, a ∈ e.source → b ∈ e.source →
        ((e a).1, (e b).2) ∈ e.target ∧
          Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    (γ ρ : unitInterval → P) (D : Set (unitInterval × unitInterval))
    (hD : IsOpen D)
    (haxes : ∀ r t, (r = 0 ∨ t = 0) → (r,t) ∈ D)
    (hdom : ∀ z, z ∈ D ↔ ∃ p, Lu (γ z.1) p ∧ Ls (ρ z.2) p)
    (θ : unitInterval × unitInterval → P) (hcont : ContinuousOn θ D)
    (hθ : ∀ z ∈ D, Lu (γ z.1) (θ z) ∧ Ls (ρ z.2) (θ z))
    (K : Set P) (hK : IsCompact K) (hbound : MapsTo θ D K) : D = univ := by
  classical
  by_contra hne
  have hne' : Dᶜ.Nonempty := Set.nonempty_compl.mpr hne
  let s : unitInterval × unitInterval → ℝ := fun z ↦ z.1.val + z.2.val
  have hs : Continuous s :=
    (continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)
  obtain ⟨z₀, hz₀, hmin⟩ := hD.isClosed_compl.isCompact.exists_isMinOn hne' hs.continuousOn
  have hsmall : ∀ z, s z < s z₀ → z ∈ D := by
    intro z hz
    by_contra hn
    exact (not_le_of_gt hz) (hmin hn)
  have hr : 0 < z₀.1.val := by
    by_contra hn
    have he : z₀.1 = 0 := Subtype.ext (le_antisymm (not_lt.mp hn) z₀.1.property.1)
    exact hz₀ (haxes z₀.1 z₀.2 (Or.inl he))
  have ht : 0 < z₀.2.val := by
    by_contra hn
    have he : z₀.2 = 0 := Subtype.ext (le_antisymm (not_lt.mp hn) z₀.2.property.1)
    exact hz₀ (haxes z₀.1 z₀.2 (Or.inr he))
  let z : ℕ → unitInterval × unitInterval :=
    fun n ↦ (intervalApproach z₀.1 n, intervalApproach z₀.2 n)
  have hzr : ∀ n, (z n).1.val < z₀.1.val := intervalApproach_lt z₀.1 hr
  have hzt : ∀ n, (z n).2.val < z₀.2.val := intervalApproach_lt z₀.2 ht
  have hzD : ∀ n, z n ∈ D := fun n ↦ hsmall _ (add_lt_add (hzr n) (hzt n))
  have hzlim : Tendsto z atTop (𝓝 z₀) :=
    (intervalApproach_tendsto z₀.1).prodMk_nhds (intervalApproach_tendsto z₀.2)
  obtain ⟨v, _, φ, hφ, hδ⟩ := hK.tendsto_subseq (fun n ↦ hbound (hzD n))
  obtain ⟨e, hv, hcross⟩ := hboxes v
  have hNev : ∀ᶠ n in atTop, θ (z (φ n)) ∈ e.source :=
    hδ (e.open_source.mem_nhds hv)
  obtain ⟨N, hN⟩ := hNev.exists
  let r := (z (φ N)).1
  let t := (z (φ N)).2
  have hra : (r, z₀.2) ∈ D := hsmall _ (by dsimp [s, r]; linarith [hzr (φ N)])
  have htb : (z₀.1, t) ∈ D := hsmall _ (by dsimp [s, t]; linarith [hzt (φ N)])
  have hrowD : ∀ n, (r, (z (φ n)).2) ∈ D :=
    fun n ↦ hsmall _ (add_lt_add (hzr (φ N)) (hzt (φ n)))
  have hcolD : ∀ n, ((z (φ n)).1, t) ∈ D :=
    fun n ↦ hsmall _ (add_lt_add (hzr (φ n)) (hzt (φ N)))
  have hsub := hzlim.comp hφ.tendsto_atTop
  have hα : Tendsto (fun n ↦ θ (r, (z (φ n)).2)) atTop (𝓝 (θ (r,z₀.2))) :=
    (hcont.continuousAt (hD.mem_nhds hra)).tendsto.comp
      (tendsto_const_nhds.prodMk_nhds (continuous_snd.tendsto _ |>.comp hsub))
  have hβ : Tendsto (fun n ↦ θ ((z (φ n)).1, t)) atTop (𝓝 (θ (z₀.1,t))) :=
    (hcont.continuousAt (hD.mem_nhds htb)).tendsto.comp
      ((continuous_fst.tendsto _ |>.comp hsub).prodMk_nhds tendsto_const_nhds)
  have hc := hθ (z (φ N)) (hzD (φ N))
  have hrow : ∀ᶠ n in atTop,
      Lu (θ (z (φ N))) (θ (r, (z (φ n)).2)) ∧
      Ls (θ (z (φ n))) (θ (r, (z (φ n)).2)) := .of_forall fun n ↦ by
    have hd := hθ (z (φ n)) (hzD (φ n))
    have ha := hθ (r, (z (φ n)).2) (hrowD n)
    exact ⟨Lu.trans (Lu.symm hc.1) ha.1, Ls.trans (Ls.symm hd.2) ha.2⟩
  have hcol : ∀ᶠ n in atTop,
      Lu (θ (z (φ n))) (θ ((z (φ n)).1, t)) ∧
      Ls (θ (z (φ N))) (θ ((z (φ n)).1, t)) := .of_forall fun n ↦ by
    have hd := hθ (z (φ n)) (hzD (φ n))
    have hb := hθ ((z (φ n)).1, t) (hcolD n)
    exact ⟨Lu.trans (Lu.symm hd.1) hb.1, Ls.trans (Ls.symm hc.2) hb.2⟩
  obtain ⟨_, _, huv, hsv⟩ := continuation_corner_of_cluster
    Lu Ls hunique e hcross hN hv hα hβ hδ hrow hcol
  exact hz₀ ((hdom z₀).2 ⟨v,
    Lu.trans (hθ (z₀.1,t) htb).1 huv, Ls.trans (hθ (r,z₀.2) hra).2 hsv⟩)

/-- Open saturation transports a small product box at an intersection to
neighborhoods of its possibly distant side points. Crossing representatives
inside the box gives all nearby intersections, and uniqueness forces every
selected value into that box. Arbitrarily small boxes therefore prove both
openness of the exact intersection domain and continuity of its selection.
This supplies the topological input to Franks' rectangle continuation without
assuming that distant side points are in the same box. -/
theorem intersection_domain_open_and_continuous
    {P U V X : Type*} [TopologicalSpace P] [TopologicalSpace U] [TopologicalSpace V]
    [TopologicalSpace X]
    (Lu Ls : Setoid P)
    (hunique : ∀ a b z z', Lu a z → Ls b z → Lu a z' → Ls b z' → z = z')
    (hsatu : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Lu x y})
    (hsats : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Ls x y})
    (hboxes : ∀ (p : P) (O : Set P), IsOpen O → p ∈ O →
      ∃ e : OpenPartialHomeomorph P (U × V), p ∈ e.source ∧ e.source ⊆ O ∧
        ∀ a b, a ∈ e.source → b ∈ e.source →
          ((e a).1, (e b).2) ∈ e.target ∧
            Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    (a b : X → P) (ha : Continuous a) (hb : Continuous b)
    (D : Set X) (hdom : ∀ t, t ∈ D ↔ ∃ p, Lu (a t) p ∧ Ls (b t) p)
    (θ : X → P) (hθ : ∀ t ∈ D, Lu (a t) (θ t) ∧ Ls (b t) (θ t)) :
    IsOpen D ∧ ContinuousOn θ D := by
  have hlocal : ∀ z ∈ D, ∀ O : Set P, IsOpen O → θ z ∈ O →
      ∃ W : Set X, IsOpen W ∧ z ∈ W ∧ ∀ t ∈ W, t ∈ D ∧ θ t ∈ O := by
    intro z hz O hO hzO
    obtain ⟨e, hez, heO, hcross⟩ := hboxes (θ z) O hO hzO
    let Wu : Set P := {x | ∃ y ∈ e.source, Lu x y}
    let Ws : Set P := {x | ∃ y ∈ e.source, Ls x y}
    refine ⟨a ⁻¹' Wu ∩ b ⁻¹' Ws,
      ((hsatu _ e.open_source).preimage ha).inter ((hsats _ e.open_source).preimage hb),
      ⟨⟨θ z, hez, (hθ z hz).1⟩, ⟨θ z, hez, (hθ z hz).2⟩⟩, ?_⟩
    rintro t ⟨⟨u, hu, htu⟩, ⟨v, hv, htv⟩⟩
    obtain ⟨hm, hum, hvm⟩ := hcross u v hu hv
    have htm := Lu.trans htu hum
    have hsm := Ls.trans htv hvm
    have htD := (hdom t).2 ⟨_, htm, hsm⟩
    refine ⟨htD, ?_⟩
    have heq := hunique (a t) (b t) (θ t) _ (hθ t htD).1 (hθ t htD).2 htm hsm
    rw [heq]
    exact heO (e.map_target hm)
  constructor
  · apply isOpen_iff_forall_mem_open.2
    intro z hz
    obtain ⟨W, hW, hzW, hsub⟩ := hlocal z hz univ isOpen_univ (mem_univ _)
    exact ⟨W, fun t ht ↦ (hsub t ht).1, hW, hzW⟩
  · intro z hz
    apply ContinuousAt.continuousWithinAt
    change Tendsto θ (𝓝 z) (𝓝 (θ z))
    rw [tendsto_def]
    intro S hS
    obtain ⟨O, hOS, hO, hzO⟩ := mem_nhds_iff.1 hS
    obtain ⟨W, hW, hzW, hsub⟩ := hlocal z hz O hO hzO
    exact mem_of_superset (hW.mem_nhds hzW) (fun t ht ↦ hOS (hsub t ht).2)

/-- Franks' compact rectangle argument constructs the opposite endpoint
intersection. The partial domain and its selector are defined internally.
Only the two side paths, leaf equivalences, independent unique intersections,
open saturation, small product boxes, and a compact bound on possible
intersections are supplied. No all-pairs intersection is an input. -/
theorem opposite_endpoint_intersection_of_compact_continuation
    {P U V : Type*} [TopologicalSpace P] [T2Space P] [FirstCountableTopology P]
    [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : Setoid P)
    (hunique : ∀ a b z z', Lu a z → Ls b z → Lu a z' → Ls b z' → z = z')
    (hsatu : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Lu x y})
    (hsats : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Ls x y})
    (hboxes : ∀ (p : P) (O : Set P), IsOpen O → p ∈ O →
      ∃ e : OpenPartialHomeomorph P (U × V), p ∈ e.source ∧ e.source ⊆ O ∧
        ∀ a b, a ∈ e.source → b ∈ e.source →
          ((e a).1, (e b).2) ∈ e.target ∧
            Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    (γ ρ : unitInterval → P) (hγ : Continuous γ) (hρ : Continuous ρ)
    (hγleaf : ∀ r, Ls (ρ 0) (γ r)) (hρleaf : ∀ t, Lu (γ 0) (ρ t))
    (K : Set P) (hK : IsCompact K)
    (hbound : ∀ r t p, Lu (γ r) p → Ls (ρ t) p → p ∈ K) :
    ∃ p, Lu (γ 1) p ∧ Ls (ρ 1) p := by
  classical
  let D : Set (unitInterval × unitInterval) :=
    {z | ∃ p, Lu (γ z.1) p ∧ Ls (ρ z.2) p}
  let θ : unitInterval × unitInterval → P :=
    fun z ↦ if h : z ∈ D then Classical.choose h else γ 0
  have hθ : ∀ z ∈ D, Lu (γ z.1) (θ z) ∧ Ls (ρ z.2) (θ z) := by
    intro z hz
    simpa only [θ, dite_eq_left hz] using Classical.choose_spec hz
  have hdom : ∀ z, z ∈ D ↔ ∃ p, Lu (γ z.1) p ∧ Ls (ρ z.2) p := fun _ ↦ Iff.rfl
  obtain ⟨hopen, hcont⟩ := intersection_domain_open_and_continuous
    Lu Ls hunique hsatu hsats hboxes (γ ∘ Prod.fst) (ρ ∘ Prod.snd)
    (hγ.comp continuous_fst) (hρ.comp continuous_snd) D hdom θ hθ
  have haxes : ∀ r t, (r = 0 ∨ t = 0) → (r,t) ∈ D := by
    intro r t h
    rcases h with rfl | rfl
    · exact ⟨ρ t, hρleaf t, Ls.refl _⟩
    · exact ⟨γ r, Lu.refl _, hγleaf r⟩
  have hboxes' : ∀ v : P, ∃ e : OpenPartialHomeomorph P (U × V), v ∈ e.source ∧
      ∀ a b, a ∈ e.source → b ∈ e.source →
        ((e a).1, (e b).2) ∈ e.target ∧
          Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)) := by
    intro v
    obtain ⟨e, hv, _, he⟩ := hboxes v univ isOpen_univ (mem_univ _)
    exact ⟨e, hv, he⟩
  have hfull := continuation_domain_eq_univ Lu Ls hunique hboxes' γ ρ D hopen haxes
    hdom θ hcont hθ K hK (fun z hz ↦ hbound z.1 z.2 (θ z) (hθ z hz).1 (hθ z hz).2)
  exact (hdom (1,1)).1 (hfull ▸ mem_univ _)

/-- Once the rectangle argument lets the two leaf relations commute, joint
boxes and connectedness turn local products into all-pairs intersections.
The composite relation is an equivalence relation. Each of its classes is
open because a box about any class point lies in that class, and its
complement is open because it is a union of other classes. Connectedness
therefore leaves only one class. This is the saturation step in Franks (1969),
Lemma 1.6, expressed without a global leaf coordinate system. -/
theorem global_intersection_of_commuting_leaf_relations
    {P U V : Type*} [TopologicalSpace P] [PreconnectedSpace P]
    [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : Setoid P)
    (hswap : ∀ a b c, Ls a b → Lu b c → ∃ d, Lu a d ∧ Ls d c)
    (hboxes : ∀ v : P, ∃ e : OpenPartialHomeomorph P (U × V), v ∈ e.source ∧
      ∀ a b, a ∈ e.source → b ∈ e.source →
        ((e a).1, (e b).2) ∈ e.target ∧
          Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2))) :
    ∀ a b, ∃ p, Lu a p ∧ Ls b p := by
  let R : P → P → Prop := fun a b ↦ ∃ p, Lu a p ∧ Ls p b
  have hrefl : ∀ a, R a a := fun a ↦ ⟨a, Lu.refl _, Ls.refl _⟩
  have hsymm : ∀ {a b}, R a b → R b a := by
    rintro a b ⟨p, hu, hs⟩
    exact hswap b p a (Ls.symm hs) (Lu.symm hu)
  have htrans : ∀ {a b c}, R a b → R b c → R a c := by
    rintro a b c ⟨p, hap, hpb⟩ ⟨q, hbq, hqc⟩
    obtain ⟨d, hpd, hdq⟩ := hswap p b q hpb hbq
    exact ⟨d, Lu.trans hap hpd, Ls.trans hdq hqc⟩
  have hopen : ∀ a, IsOpen {b | R a b} := by
    intro a
    apply isOpen_iff_forall_mem_open.2
    intro b hab
    obtain ⟨e, hb, hcross⟩ := hboxes b
    refine ⟨e.source, ?_, e.open_source, hb⟩
    intro c hc
    obtain ⟨_, hu, hs⟩ := hcross b c hb hc
    exact htrans hab ⟨_, hu, Ls.symm hs⟩
  intro a b
  have hclosed : IsClosed {c | R a c} := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_forall_mem_open.2
    intro c hc
    refine ⟨{d | R c d}, ?_, hopen c, hrefl c⟩
    intro d hcd had
    exact hc (htrans had (hsymm hcd))
  have hfull : {c | R a c} = univ :=
    (show IsClopen {c | R a c} from ⟨hclosed, hopen a⟩).eq_univ ⟨a, hrefl a⟩
  have hb : b ∈ {c | R a c} := hfull ▸ mem_univ b
  obtain ⟨p, hu, hs⟩ := hb
  exact ⟨p, hu, Ls.symm hs⟩

/-- Global product from native topological leaves and compact continuation.
Paths inside each equivalence class form the two sides of a rectangle. The
endpoint theorem commutes a stable leg past an unstable leg; connectedness
and joint boxes then give every opposite-leaf intersection. The compactness
premise bounds only possible intersections of compact side families and is
provided by a proper semiconjugacy with complementary projected side data. -/
theorem global_intersection_of_compact_continuation
    {P U V : Type*} [TopologicalSpace P] [T2Space P] [FirstCountableTopology P]
    [PreconnectedSpace P] [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : Setoid P)
    (hunique : ∀ a b z z', Lu a z → Ls b z → Lu a z' → Ls b z' → z = z')
    (hsatu : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Lu x y})
    (hsats : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Ls x y})
    (hboxes : ∀ (p : P) (O : Set P), IsOpen O → p ∈ O →
      ∃ e : OpenPartialHomeomorph P (U × V), p ∈ e.source ∧ e.source ⊆ O ∧
        ∀ a b, a ∈ e.source → b ∈ e.source →
          ((e a).1, (e b).2) ∈ e.target ∧
            Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    (hpathu : ∀ x y, Lu x y → ∃ γ : Path x y, ∀ t, Lu x (γ t))
    (hpaths : ∀ x y, Ls x y → ∃ γ : Path x y, ∀ t, Ls x (γ t))
    (hcompact : ∀ γ ρ : unitInterval → P, Continuous γ → Continuous ρ →
      ∃ K : Set P, IsCompact K ∧ ∀ r t p, Lu (γ r) p → Ls (ρ t) p → p ∈ K) :
    ∀ a b, ∃ p, Lu a p ∧ Ls b p := by
  apply global_intersection_of_commuting_leaf_relations (U := U) (V := V) Lu Ls
  · intro a b c hab hbc
    obtain ⟨γ, hγ⟩ := hpaths b a (Ls.symm hab)
    obtain ⟨ρ, hρ⟩ := hpathu b c hbc
    obtain ⟨K, hK, hbound⟩ := hcompact γ ρ γ.continuous ρ.continuous
    obtain ⟨p, hu, hs⟩ := opposite_endpoint_intersection_of_compact_continuation
      Lu Ls hunique hsatu hsats hboxes γ ρ γ.continuous ρ.continuous
      (by simpa only [Path.source] using hγ) (by simpa only [Path.source] using hρ)
      K hK hbound
    exact ⟨p, by simpa only [Path.target] using hu, Ls.symm (by simpa only [Path.target] using hs)⟩
  · intro v
    obtain ⟨e, hv, _, he⟩ := hboxes v univ isOpen_univ (mem_univ _)
    exact ⟨e, hv, he⟩

/-- A rectangular product box has arbitrarily small rectangular subboxes,
with the same ambient coordinate types and the same leaf incidence laws.
Choose a product neighborhood in the coordinate image of the desired open
set and restrict the inverse chart to that product. -/
theorem exists_small_rectangular_box
    {P U V : Type*} [TopologicalSpace P] [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : P → P → Prop) (e : OpenPartialHomeomorph P (U × V))
    (hcross : ∀ a b, a ∈ e.source → b ∈ e.source →
      ((e a).1, (e b).2) ∈ e.target ∧
        Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    (p : P) (hp : p ∈ e.source) (O : Set P) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ f : OpenPartialHomeomorph P (U × V), p ∈ f.source ∧ f.source ⊆ O ∧
      ∀ a b, a ∈ f.source → b ∈ f.source →
        ((f a).1, (f b).2) ∈ f.target ∧
          Lu a (f.symm ((f a).1, (f b).2)) ∧ Ls b (f.symm ((f a).1, (f b).2)) := by
  have hT := e.isOpen_image_source_inter hO
  have hpT : e p ∈ e '' (e.source ∩ O) := ⟨p, ⟨hp, hpO⟩, rfl⟩
  obtain ⟨A, B, hA, hpA, hB, hpB, hAB⟩ := mem_nhds_prod_iff'.1 (hT.mem_nhds hpT)
  let f := (e.symm.restrOpen (A ×ˢ B) (hA.prod hB)).symm
  refine ⟨f, ?_, ?_, ?_⟩
  · exact ⟨hp, hpA, hpB⟩
  · intro x hx
    obtain ⟨y, ⟨hys, hyO⟩, hyx⟩ := hAB hx.2
    have hy : y = x := e.injOn hys hx.1 hyx
    exact hy ▸ hyO
  · intro a b ha hb
    obtain ⟨hm, hu, hs⟩ := hcross a b ha.1 hb.1
    exact ⟨⟨hm, ha.2.1, hb.2.2⟩, hu, hs⟩

/-- Version whose chart input is just a rectangular box cover. Arbitrarily
small boxes are supplied by coordinate restriction, so this interface matches
the ordinary local-product output of the native foliation construction. -/
theorem global_intersection_of_rectangular_box_cover
    {P U V : Type*} [TopologicalSpace P] [T2Space P] [FirstCountableTopology P]
    [PreconnectedSpace P] [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : Setoid P)
    (hunique : ∀ a b z z', Lu a z → Ls b z → Lu a z' → Ls b z' → z = z')
    (hsatu : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Lu x y})
    (hsats : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Ls x y})
    (hboxes : ∀ v : P, ∃ e : OpenPartialHomeomorph P (U × V), v ∈ e.source ∧
      ∀ a b, a ∈ e.source → b ∈ e.source →
        ((e a).1, (e b).2) ∈ e.target ∧
          Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    (hpathu : ∀ x y, Lu x y → ∃ γ : Path x y, ∀ t, Lu x (γ t))
    (hpaths : ∀ x y, Ls x y → ∃ γ : Path x y, ∀ t, Ls x (γ t))
    (hcompact : ∀ γ ρ : unitInterval → P, Continuous γ → Continuous ρ →
      ∃ K : Set P, IsCompact K ∧ ∀ r t p, Lu (γ r) p → Ls (ρ t) p → p ∈ K) :
    ∀ a b, ∃ p, Lu a p ∧ Ls b p := by
  apply global_intersection_of_compact_continuation Lu Ls hunique hsatu hsats
    (U := U) (V := V) _ hpathu hpaths hcompact
  intro p O hO hpO
  obtain ⟨e, hp, hcross⟩ := hboxes p
  exact exists_small_rectangular_box Lu Ls e hcross p hp O hO hpO

/-- Global intersections vary continuously with both endpoints, and the
same-leaf relations are closed in the product space. The selector is the
unique intersection of Lu(x) with Ls(y). A pair is in Lu exactly when its
crossing equals y, and in Ls exactly when its crossing equals x. Thus both
relations are equality loci of continuous maps. -/
theorem continuous_global_intersection_and_closed_relations
    {P U V : Type*} [TopologicalSpace P] [T2Space P]
    [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : Setoid P)
    (hunique : ∀ a b z z', Lu a z → Ls b z → Lu a z' → Ls b z' → z = z')
    (hsatu : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Lu x y})
    (hsats : ∀ O : Set P, IsOpen O → IsOpen {x | ∃ y ∈ O, Ls x y})
    (hboxes : ∀ v : P, ∃ e : OpenPartialHomeomorph P (U × V), v ∈ e.source ∧
      ∀ a b, a ∈ e.source → b ∈ e.source →
        ((e a).1, (e b).2) ∈ e.target ∧
          Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    (hproduct : ∀ a b, ∃ p, Lu a p ∧ Ls b p) :
    (∃ J : C(P × P, P), ∀ a b, Lu a (J (a,b)) ∧ Ls b (J (a,b))) ∧
      IsClosed {z : P × P | Lu z.1 z.2} ∧ IsClosed {z : P × P | Ls z.1 z.2} := by
  classical
  let J : P × P → P := fun z ↦ Classical.choose (hproduct z.1 z.2)
  have hJ : ∀ z, Lu z.1 (J z) ∧ Ls z.2 (J z) :=
    fun z ↦ Classical.choose_spec (hproduct z.1 z.2)
  have hsmall : ∀ (p : P) (O : Set P), IsOpen O → p ∈ O →
      ∃ e : OpenPartialHomeomorph P (U × V), p ∈ e.source ∧ e.source ⊆ O ∧
        ∀ a b, a ∈ e.source → b ∈ e.source →
          ((e a).1, (e b).2) ∈ e.target ∧
            Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)) := by
    intro p O hO hpO
    obtain ⟨e, hp, he⟩ := hboxes p
    exact exists_small_rectangular_box Lu Ls e he p hp O hO hpO
  have hdom : ∀ z : P × P, z ∈ (univ : Set (P × P)) ↔ ∃ p, Lu z.1 p ∧ Ls z.2 p :=
    fun z ↦ ⟨fun _ ↦ hproduct z.1 z.2, fun _ ↦ mem_univ _⟩
  have hcont : Continuous J := continuousOn_univ.1
    (intersection_domain_open_and_continuous Lu Ls hunique hsatu hsats hsmall
      Prod.fst Prod.snd continuous_fst continuous_snd univ hdom J (fun z _ ↦ hJ z)).2
  have hRu : {z : P × P | Lu z.1 z.2} = {z | J z = z.2} := by
    ext z
    constructor
    · intro hz
      exact hunique z.1 z.2 _ _ (hJ z).1 (hJ z).2 hz (Ls.refl _)
    · intro hz
      change J z = z.2 at hz
      change Lu z.1 z.2
      simpa only [hz] using (hJ z).1
  have hRs : {z : P × P | Ls z.1 z.2} = {z | J z = z.1} := by
    ext z
    constructor
    · intro hz
      exact hunique z.1 z.2 _ _ (hJ z).1 (hJ z).2 (Lu.refl _) (Ls.symm hz)
    · intro hz
      change J z = z.1 at hz
      exact Ls.symm (by simpa only [hz] using (hJ z).2)
  exact ⟨⟨⟨J, hcont⟩, fun a b ↦ hJ (a,b)⟩,
    hRu ▸ isClosed_eq hcont continuous_snd, hRs ▸ isClosed_eq hcont continuous_fst⟩

/-- Inside a joint box, unique opposite-leaf intersections force points on
the same global Lu-leaf to have the same first coordinate. This is the local
plaque protection needed to apply native orbit-core estimates to nearby
globally related pairs. -/
theorem same_leaf_iff_same_first_coordinate
    {P U V : Type*} [TopologicalSpace P] [TopologicalSpace U] [TopologicalSpace V]
    (Lu Ls : Setoid P)
    (hunique : ∀ a b z z', Lu a z → Ls b z → Lu a z' → Ls b z' → z = z')
    (e : OpenPartialHomeomorph P (U × V))
    (hcross : ∀ a b, a ∈ e.source → b ∈ e.source →
      ((e a).1, (e b).2) ∈ e.target ∧
        Lu a (e.symm ((e a).1, (e b).2)) ∧ Ls b (e.symm ((e a).1, (e b).2)))
    {x y : P} (hx : x ∈ e.source) (hy : y ∈ e.source) :
    Lu x y ↔ (e x).1 = (e y).1 := by
  obtain ⟨hm, hu, hs⟩ := hcross x y hx hy
  constructor
  · intro hxy
    have he := hunique x y _ y hu hs hxy (Ls.refl y)
    have hc := congrArg (fun z ↦ (e z).1) he
    simpa only [e.right_inv hm] using hc
  · intro he
    have hm' : e.symm ((e x).1, (e y).2) = y := by
      rw [he]
      exact e.left_inv hy
    exact hm' ▸ hu

end HolomorphicAnosov.FranksOriginalCover
