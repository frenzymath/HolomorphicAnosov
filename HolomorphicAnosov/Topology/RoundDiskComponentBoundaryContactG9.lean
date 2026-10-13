import HolomorphicAnosov.Topology.FrontierConnectedComponentIn
import HolomorphicAnosov.Topology.RoundDiskBoundaryComponentConstancy
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex

open Set Metric

namespace HolomorphicAnosov

/-- If a closed obstacle has connected plane complement, every component of its
complement in the unit disk accumulates at a circle point outside the obstacle.

Source: agent-written component argument for Cairns (1951), Lemma 5.1, p.866.
The component is open and its frontier is contained in the obstacle together
with the unit circle. If its frontier had no point outside the obstacle, the
component would be relatively closed as well as open in the connected obstacle
complement, and would therefore equal that entire complement. This contradicts
the assumed point of the complement outside the closed disk. -/
theorem roundDisk_component_boundary_contact
    {K : Set ℂ} (hK : IsClosed K) (hc : IsPreconnected Kᶜ)
    (hout : ∃ z ∉ closedBall (0 : ℂ) 1, z ∉ K)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) 1 \ K) :
    ∃ a ∈ sphere (0 : ℂ) 1 \ K,
      a ∈ closure (connectedComponentIn (ball (0 : ℂ) 1 \ K) x) := by
  have : LocallyConnectedSpace ℂ := locallyConnectedSpace_of_connected_bases
    (fun x r ↦ Metric.ball x r) (fun _ r ↦ 0 < r)
    (fun _ ↦ Metric.nhds_basis_ball)
    (fun _ _ _ ↦ (convex_ball _ _).isPreconnected)
  let U := connectedComponentIn (ball (0 : ℂ) 1 \ K) x
  have hUo : IsOpen U := (isOpen_ball.sdiff hK).connectedComponentIn
  have hUs : U ⊆ ball (0 : ℂ) 1 \ K := connectedComponentIn_subset _ _
  have hxU : x ∈ U := mem_connectedComponentIn hx
  have hfront : frontier U ⊆ (ball (0 : ℂ) 1 \ K)ᶜ :=
    frontier_connectedComponentIn_subset_compl (isOpen_ball.sdiff hK) x
  have hcl : closure U ⊆ closedBall (0 : ℂ) 1 := by
    rw [← closure_ball (0 : ℂ) one_ne_zero]
    exact closure_mono (hUs.trans sdiff_subset)
  by_contra hnot
  have hfK : frontier U ⊆ K := by
    intro a ha
    by_contra haK
    have hanot : a ∉ ball (0 : ℂ) 1 := fun hab ↦ hfront ha ⟨hab, haK⟩
    have hasphere : a ∈ sphere (0 : ℂ) 1 := by
      have haClosed := hcl (frontier_subset_closure ha)
      simpa only [mem_sphere, mem_closedBall, mem_ball, not_lt] using
        le_antisymm haClosed (not_lt.mp hanot)
    exact hnot ⟨a, ⟨hasphere, haK⟩, frontier_subset_closure ha⟩
  have hall : Kᶜ ⊆ U := hc.subset_of_closure_inter_subset hUo ⟨x, hx.2, hxU⟩ (by
    rintro a ⟨ha, haK⟩
    by_contra haU
    exact haK (hfK (hUo.frontier_eq.symm ▸ ⟨ha, haU⟩)))
  obtain ⟨z, hz, hzK⟩ := hout
  exact hz (ball_subset_closedBall ((hUs (hall hzK)).1))

/-- Two connected arcs covering the unobstructed circle classify the disk
components when the obstacle has connected plane complement and the disk
complement is disconnected. The cap at a point of each arc determines one
component. Every component has a boundary contact by the preceding theorem,
and constancy along each arc identifies it with one of these two. The assumed
distinct components make the selected components distinct. A boundary point
away from the obstacle belongs to its selected circle arc by uniqueness of
the incident component.

Source: agent-written expansion of Cairns (1951), Lemma 5.1, p.866. -/
theorem roundDisk_components_of_two_boundary_arcs
    {K : Set ℂ} (hK : IsClosed K) (hc : IsPreconnected Kᶜ)
    (hout : ∃ z ∉ closedBall (0 : ℂ) 1, z ∉ K)
    (A : Fin 2 → Set ℂ)
    (hA : ∀ i, IsConnected (A i))
    (hAs : ∀ i, A i ⊆ sphere (0 : ℂ) 1 \ K)
    (hcover : (⋃ i, A i) = sphere (0 : ℂ) 1 \ K)
    (hdisconnected : ∃ x y, x ∈ ball (0 : ℂ) 1 \ K ∧
      y ∈ ball (0 : ℂ) 1 \ K ∧
      connectedComponentIn (ball (0 : ℂ) 1 \ K) x ≠
        connectedComponentIn (ball (0 : ℂ) 1 \ K) y) :
    ∃ V : Fin 2 → Set ℂ,
      (∀ i, (V i).Nonempty ∧ IsConnected (V i) ∧ IsOpen (V i)) ∧
      Disjoint (V 0) (V 1) ∧
      (⋃ i, V i) = ball (0 : ℂ) 1 \ K ∧
      (∀ x ∈ ball (0 : ℂ) 1 \ K,
        ∃ i, connectedComponentIn (ball (0 : ℂ) 1 \ K) x = V i) ∧
      (∀ i, frontier (V i) ⊆ K ∪ A i) ∧
      (∀ i, A i ⊆ closure (V i)) := by
  classical
  have : LocallyConnectedSpace ℂ := locallyConnectedSpace_of_connected_bases
    (fun x r ↦ Metric.ball x r) (fun _ r ↦ 0 < r)
    (fun _ ↦ Metric.nhds_basis_ball)
    (fun _ _ _ ↦ (convex_ball _ _).isPreconnected)
  let Ω := ball (0 : ℂ) 1 \ K
  have hΩ : IsOpen Ω := isOpen_ball.sdiff hK
  have hchoose (i : Fin 2) : ∃ x ∈ Ω, ∃ a ∈ A i,
      a ∈ closure (connectedComponentIn Ω x) := by
    obtain ⟨a, ha⟩ := (hA i).nonempty
    obtain ⟨ε, hε, hd, x, hx, hcap, hf, _⟩ :=
      roundDisk_boundary_component hK (hAs i ha).1 (hAs i ha).2
    exact ⟨x, ⟨hx.2, fun hxK ↦ disjoint_left.mp hd hx.1 hxK⟩,
      a, ha, frontier_subset_closure hf⟩
  choose x hx a ha hax using hchoose
  let V : Fin 2 → Set ℂ := fun i ↦ connectedComponentIn Ω (x i)
  have hV (i) : (V i).Nonempty ∧ IsConnected (V i) ∧ IsOpen (V i) :=
    ⟨⟨x i, mem_connectedComponentIn (hx i)⟩,
      isConnected_connectedComponentIn_iff.mpr (hx i), hΩ.connectedComponentIn⟩
  have hclass (z) (hz : z ∈ Ω) : ∃ i, connectedComponentIn Ω z = V i := by
    obtain ⟨b, hb, hbcl⟩ := roundDisk_component_boundary_contact hK hc hout hz
    obtain ⟨i, hbi⟩ := mem_iUnion.mp (hcover.symm ▸ hb)
    exact ⟨i, roundDisk_boundary_component_constancy hK (hA i).isPreconnected
      (hAs i) hbi (ha i) hz (hx i) hbcl (hax i)⟩
  have hne : V 0 ≠ V 1 := by
    intro heq
    obtain ⟨z, w, hz, hw, hzw⟩ := hdisconnected
    obtain ⟨i, hi⟩ := hclass z hz
    obtain ⟨j, hj⟩ := hclass w hw
    apply hzw
    rw [hi, hj]
    fin_cases i <;> fin_cases j <;> simp_all
  have hinj : Function.Injective V := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hdis : Disjoint (V 0) (V 1) := by
    apply disjoint_left.mpr
    intro z hz₀ hz₁
    exact hne ((connectedComponentIn_eq hz₀).trans (connectedComponentIn_eq hz₁).symm)
  have hunion : (⋃ i, V i) = Ω := by
    apply Subset.antisymm
    · exact iUnion_subset (fun i ↦ connectedComponentIn_subset _ _)
    · intro z hz
      obtain ⟨i, hi⟩ := hclass z hz
      exact mem_iUnion.mpr ⟨i, hi ▸ mem_connectedComponentIn hz⟩
  refine ⟨V, hV, hdis, hunion, hclass, ?_, ?_⟩
  · intro i z hz
    by_cases hzK : z ∈ K
    · exact Or.inl hzK
    right
    have hzcl : z ∈ closure (V i) := frontier_subset_closure hz
    have hzcb : z ∈ closedBall (0 : ℂ) 1 := by
      rw [← closure_ball (0 : ℂ) one_ne_zero]
      exact closure_mono ((connectedComponentIn_subset Ω (x i)).trans sdiff_subset) hzcl
    have hznb : z ∉ ball (0 : ℂ) 1 := by
      intro hzb
      exact frontier_connectedComponentIn_subset_compl hΩ (x i) hz ⟨hzb, hzK⟩
    have hzS : z ∈ sphere (0 : ℂ) 1 :=
      le_antisymm hzcb (not_lt.mp hznb)
    have hzbdy : z ∈ sphere (0 : ℂ) 1 \ K := ⟨hzS, hzK⟩
    obtain ⟨j, hzj⟩ := mem_iUnion.mp (hcover.symm ▸ hzbdy)
    have hij : V i = V j := roundDisk_boundary_component_constancy hK
      (hA j).isPreconnected (hAs j) hzj (ha j) (hx i) (hx j) hzcl (hax j)
    simpa only [hinj hij] using hzj
  · intro i b hb
    obtain ⟨ε, hε, hd, z, hz, _, hf, _⟩ :=
      roundDisk_boundary_component hK (hAs i hb).1 (hAs i hb).2
    have hzΩ : z ∈ Ω := ⟨hz.2, fun hzK ↦ disjoint_left.mp hd hz.1 hzK⟩
    have heq : connectedComponentIn Ω z = V i :=
      roundDisk_boundary_component_constancy hK (hA i).isPreconnected (hAs i)
        hb (ha i) hzΩ (hx i) (frontier_subset_closure hf) (hax i)
    exact heq ▸ frontier_subset_closure hf

end HolomorphicAnosov

