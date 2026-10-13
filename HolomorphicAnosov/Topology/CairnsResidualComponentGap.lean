import HolomorphicAnosov.Topology.CairnsExponentialIntervalFrontier
import HolomorphicAnosov.Topology.BoundedOpenRealInterval
import HolomorphicAnosov.Topology.CairnsNormalizedCircleGap
import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsRefinement

/-! `Circle` is a quotient of the real line by a full turn.  Mathlib exposes
the quotient's local path-connectedness, but does not register the transported
instance for `Circle`; this short adapter makes the component-openness theorem
available below. -/

theorem circle_locallyPathConnectedSpace : LocallyPathConnectedSpace Circle := by
  let : LocallyPathConnectedSpace ℝ := inferInstance
  let : LocallyPathConnectedSpace (AddCircle (2 * Real.pi)) := by
    exact isQuotientMap_quotient_mk'.locallyPathConnectedSpace
  exact AddCircle.homeomorphCircle'.locallyPathConnectedSpace

/-! The following elementary projections of `ResidualComponent` are useful when
constructing angular endpoints.  They expose exactly the component facts supplied
by Mathlib, without asserting any endpoint or interval parametrization. -/

theorem residual_component_nonempty (S : Set Circle) (i : ResidualComponent S) :
    i.val.Nonempty := by
  rcases i.property with ⟨x, hx, hxi⟩
  refine ⟨x, ?_⟩
  rw [← hxi]
  exact mem_connectedComponentIn hx

theorem residual_component_subset_compl (S : Set Circle) (i : ResidualComponent S) :
    i.val ⊆ Sᶜ := by
  rcases i.property with ⟨x, hx, hxi⟩
  rw [← hxi]
  exact connectedComponentIn_subset _ _

theorem residual_component_isPreconnected (S : Set Circle) (i : ResidualComponent S) :
    IsPreconnected i.val := by
  rcases i.property with ⟨x, hx, hxi⟩
  rw [← hxi]
  exact isPreconnected_connectedComponentIn

theorem residual_component_isConnected (S : Set Circle) (i : ResidualComponent S) :
    IsConnected i.val := by
  exact ⟨residual_component_nonempty S i, residual_component_isPreconnected S i⟩

/-! An open connected subset of the real line with finite lower and upper
bounds is the open interval between its infimum and supremum.  This is the
order-theoretic interval step used after cutting the parameter circle at one
retained contact. -/

theorem cairns_open_preconnected_bdd_interval
    (A : Set ℝ) (hAne : A.Nonempty) (hAopen : IsOpen A)
    (hApre : IsPreconnected A) (hbelow : BddBelow A) (habove : BddAbove A) :
    ∃ l u : ℝ, l < u ∧ A = Ioo l u := by
  obtain ⟨l,u,hlu,hA,-,-⟩ := HolomorphicAnosov.bounded_open_connected_real_interval
    hAopen ⟨hAne,hApre⟩ (Metric.isBounded_of_bddAbove_of_bddBelow habove hbelow)
  exact ⟨l,u,hlu,hA⟩

theorem cairns_open_preconnected_bdd_interval_frontier
    (A : Set ℝ) (hAne : A.Nonempty) (hAopen : IsOpen A)
    (hApre : IsPreconnected A) (hbelow : BddBelow A) (habove : BddAbove A) :
    ∃ l u : ℝ, l < u ∧ A = Ioo l u ∧ frontier A = {l, u} := by
  obtain ⟨l, u, hlu, hA⟩ :=
    cairns_open_preconnected_bdd_interval A hAne hAopen hApre hbelow habove
  refine ⟨l, u, hlu, hA, ?_⟩
  rw [hA, frontier_Ioo hlu]

theorem residual_component_isOpen (S : Set Circle) (hS : IsClosed S)
    (i : ResidualComponent S) : IsOpen i.val := by
  let : LocallyPathConnectedSpace Circle := circle_locallyPathConnectedSpace
  rcases i.property with ⟨x, hx, hxi⟩
  rw [← hxi]
  exact hS.isOpen_compl.connectedComponentIn

theorem residual_component_ssubset_univ (S : Set Circle) (hS : S.Nonempty)
    (i : ResidualComponent S) : i.val ⊂ (Set.univ : Set Circle) := by
  refine ⟨subset_univ _, ?_⟩
  rcases hS with ⟨s, hs⟩
  intro hi
  exact (residual_component_subset_compl S i (hi (mem_univ s))) hs

/-! A boundary point of a residual component is a retained point.  This is the
local endpoint fact used by the angular classification: local path connectedness
makes every complementary component open, so a boundary point outside `S` would
have an open complementary component neighborhood meeting `i`, forcing the two
components to coincide. -/

theorem residual_component_frontier_subset (S : Set Circle) (hS : IsClosed S)
    (i : ResidualComponent S) : frontier i.val ⊆ S := by
  let : LocallyPathConnectedSpace Circle := circle_locallyPathConnectedSpace
  intro y hy
  by_contra hyS
  have hycomp : y ∈ Sᶜ := hyS
  have hopen : IsOpen (connectedComponentIn Sᶜ y) :=
    hS.isOpen_compl.connectedComponentIn
  have hy_nhds : connectedComponentIn Sᶜ y ∈ nhds y :=
    hopen.mem_nhds (mem_connectedComponentIn hycomp)
  rw [frontier] at hy
  have hyclosure : y ∈ closure i.val := hy.1
  rcases (mem_closure_iff_nhds.mp hyclosure) _ hy_nhds with ⟨z, hzcy, hzi⟩
  rcases i.property with ⟨x, hx, hxi⟩
  have hzcomp : connectedComponentIn Sᶜ z = i.val := by
    have hzx : z ∈ connectedComponentIn Sᶜ x := by
      rw [hxi]
      exact hzi
    calc
      connectedComponentIn Sᶜ z = connectedComponentIn Sᶜ y :=
        (connectedComponentIn_eq hzcy).symm
      _ = connectedComponentIn Sᶜ x :=
        (connectedComponentIn_eq hzcy).trans (connectedComponentIn_eq hzx).symm
      _ = i.val := hxi
  have hyinz : y ∈ connectedComponentIn Sᶜ z := by
    rw [← connectedComponentIn_eq hzcy]
    exact mem_connectedComponentIn hycomp
  have hzyi : y ∈ i.val := by
    rw [← hzcomp]
    exact hyinz
  exact hy.2 (mem_interior_iff_mem_nhds.2
    ((residual_component_isOpen S hS i).mem_nhds hzyi))

theorem residual_component_frontier_nonempty (S : Set Circle) (_hS : IsClosed S)
    (hSne : S.Nonempty) (i : ResidualComponent S) : (frontier i.val).Nonempty := by
  apply nonempty_frontier_iff.2
  exact ⟨residual_component_nonempty S i, (residual_component_ssubset_univ S hSne i).ne⟩

theorem residual_component_closure_subset (S : Set Circle) (hS : IsClosed S)
    (i : ResidualComponent S) : closure i.val ⊆ S ∪ i.val := by
  rw [closure_eq_self_union_frontier]
  intro z hz
  rcases hz with hz | hz
  · exact Or.inr hz
  · exact Or.inl (residual_component_frontier_subset S hS i hz)

theorem residual_component_frontier_contact (S : Set Circle) (hS : IsClosed S)
    (hSne : S.Nonempty) (i : ResidualComponent S) :
    ∃ z : Circle, z ∈ frontier i.val ∧ z ∈ S := by
  obtain ⟨z, hz⟩ := residual_component_frontier_nonempty S hS hSne i
  exact ⟨z, hz, residual_component_frontier_subset S hS i hz⟩

theorem residual_component_frontier_contact_lift (S : Set Circle) (hS : IsClosed S)
    (hSne : S.Nonempty) (i : ResidualComponent S) :
    ∃ a : ℝ, Circle.exp a ∈ frontier i.val ∧ Circle.exp a ∈ S := by
  obtain ⟨z, hzfr, hzS⟩ := residual_component_frontier_contact S hS hSne i
  exact ⟨(z : ℂ).arg, by simpa using hzfr, by simpa using hzS⟩

/-- Cut the parameter circle at a retained contact and apply the real interval
classification to the inverse image of a residual component.  The quotient
chart is a homeomorphism on one open period; openness and connectedness transport
to the real line, and its closed period bounds both interval endpoints.
This is an agent-written expansion of Cairns (1951), §4(C), pp.864–865. -/
theorem cairns_residual_component_cut_chart
    (S : Set Circle) (hS : IsClosed S)
    (i : ResidualComponent S) (p : Circle) (hp : p ∈ S) (r : ℝ)
    (hr : Circle.exp r = p) :
    ∃ l u : ℝ, l < u ∧ l ∈ Icc r (r + 2 * Real.pi) ∧
      u ∈ Icc r (r + 2 * Real.pi) ∧ Circle.exp '' Ioo l u = i.val := by
  let period : ℝ := 2 * Real.pi
  let : Fact (0 < period) := ⟨Real.two_pi_pos⟩
  let eAdd := AddCircle.openPartialHomeomorphCoe period r
  let eCircle := eAdd.transHomeomorph AddCircle.homeomorphCircle'
  have hsource : eCircle.source = Ioo r (r + period) := rfl
  have hfun : (eCircle : ℝ → Circle) = Circle.exp := rfl
  have htarget : eCircle.target = ({p} : Set Circle)ᶜ := by
    ext z
    change (AddCircle.homeomorphCircle'.symm z ≠ (r : AddCircle period)) ↔ z ≠ p
    rw [← hr, ← AddCircle.homeomorphCircle'_apply_mk r]
    exact not_congr (AddCircle.homeomorphCircle'.symm_apply_eq)
  have hisub : i.val ⊆ eCircle.target := by
    rw [htarget]
    intro z hz hzp
    apply (residual_component_subset_compl S i hz)
    simp only [mem_singleton_iff] at hzp
    exact hzp.symm ▸ hp
  let A : Set ℝ := eCircle.symm '' i.val
  have hAne : A.Nonempty := by
    rcases residual_component_nonempty S i with ⟨z,hz⟩
    exact ⟨eCircle.symm z, ⟨z,hz,rfl⟩⟩
  have hAopen : IsOpen A := by
    exact eCircle.isOpen_image_symm_of_subset_target
      (residual_component_isOpen S hS i) hisub
  have hApre : IsPreconnected A := by
    exact (residual_component_isConnected S i).isPreconnected.image _
      (eCircle.symm.continuousOn.mono hisub)
  have hAbelow : BddBelow A := by
    refine ⟨r, ?_⟩
    rintro x ⟨z,hz,rfl⟩
    have hx : eCircle.symm z ∈ eCircle.source := eCircle.map_target (hisub hz)
    rw [hsource] at hx
    exact hx.1.le
  have hAabove : BddAbove A := by
    refine ⟨r + period, ?_⟩
    rintro x ⟨z,hz,rfl⟩
    have hx : eCircle.symm z ∈ eCircle.source := eCircle.map_target (hisub hz)
    rw [hsource] at hx
    exact hx.2.le
  obtain ⟨l,u,hlu,hAeq,hAfr⟩ :=
    cairns_open_preconnected_bdd_interval_frontier A hAne hAopen hApre hAbelow hAabove
  have hAsub : A ⊆ Icc r (r + period) := by
    rintro x ⟨z,hz,rfl⟩
    have hx := eCircle.map_target (hisub hz)
    change r < eCircle.symm z ∧ eCircle.symm z < r + period at hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hclsub : closure A ⊆ Icc r (r + period) :=
    closure_minimal hAsub isClosed_Icc
  have hlcl : l ∈ closure A := frontier_subset_closure (by rw [hAfr]; simp)
  have hucl : u ∈ closure A := frontier_subset_closure (by rw [hAfr]; simp)
  refine ⟨l,u,hlu,hclsub hlcl,hclsub hucl,?_⟩
  rw [← hAeq, ← hfun]
  change eCircle '' (eCircle.symm '' i.val) = i.val
  apply Subset.antisymm
  · rintro z ⟨x,⟨y,hy,rfl⟩,rfl⟩
    simpa only [eCircle.right_inv (hisub hy)] using hy
  · intro z hz
    exact ⟨eCircle.symm z, ⟨z,hz,rfl⟩, eCircle.right_inv (hisub hz)⟩

theorem cairns_residual_component_frontier_finite
    (S : Set Circle) (hS : IsClosed S) (hSne : S.Nonempty)
    (i : ResidualComponent S) :
    ∃ u v : Circle, frontier i.val = {u, v} := by
  obtain ⟨p,hp⟩ := hSne
  obtain ⟨r,hr⟩ := Circle.exp_surjective p
  obtain ⟨l,u,hlu,hl,hu,harc⟩ :=
    cairns_residual_component_cut_chart S hS i p hp r hr
  refine ⟨Circle.exp l, Circle.exp u, ?_⟩
  rw [← harc]
  exact cairns_exp_interval_frontier l u hlu (by linarith [hl.1,hu.2])

theorem cairns_residual_component_interval_normalization
    (S : Set Circle) (hS : IsClosed S) (hSne : S.Nonempty)
    (i : ResidualComponent S) :
    ∃ a b : ℝ, a < b ∧ Circle.exp a ∈ frontier i.val ∧
      Circle.exp b ∈ frontier i.val ∧ Circle.exp '' Ioo a b = i.val := by
  obtain ⟨r, hrF, hrS⟩ := residual_component_frontier_contact_lift S hS hSne i
  obtain ⟨l,u,hlu,hl,hu,harc⟩ :=
    cairns_residual_component_cut_chart S hS i (Circle.exp r) hrS r rfl
  have hfr : frontier i.val = {Circle.exp l, Circle.exp u} := by
    rw [← harc]
    exact cairns_exp_interval_frontier l u hlu (by linarith [hl.1,hu.2])
  exact ⟨l,u,hlu,by rw [hfr]; simp,by rw [hfr]; simp,harc⟩

/-!
Endpoint normalization on the periodic angular cover is proved above by cutting
at a retained contact and transferring the real interval through the quotient chart.  The endpoint theorem is DAG node
`topo.cairns_residual_component_lift_endpoint_normalization_g20`: cut the circle at a retained contact, classify the inverse image as a bounded
real open interval, and use the other retained contacts to rule out a full turn.
This is the complementary-arc argument in Cairns (1951), §4(C), pp.864–865.
-/

theorem cairns_residual_component_boundary_lift
    (S : Set Circle) (hS : IsClosed S)
    (hSne : S.Nonempty)
    (i : ResidualComponent S) :
    ∃ a b : ℝ, a < b ∧ Circle.exp a ∈ S ∧
      Circle.exp b ∈ S ∧ Circle.exp '' Ioo a b = i.val := by
  /- Cairns §4(C): lift the open component to the real universal cover. The two
     finite boundary points project into the closed retained set S, and maximality
     identifies the component with the open exponential interval between them. -/
  obtain ⟨a, b, hab, haF, hbF, harc⟩ :=
    cairns_residual_component_interval_normalization S hS hSne i
  exact ⟨a, b, hab, residual_component_frontier_subset S hS i haF,
    residual_component_frontier_subset S hS i hbF, harc⟩

theorem cairns_residual_component_no_full_turn
    (S : Set Circle) (_hS : IsClosed S)
    (hfour : ∃ t₁ t₂ t₃ t₄ : Circle, t₁ ∈ S ∧ t₂ ∈ S ∧ t₃ ∈ S ∧ t₄ ∈ S ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄)
    (i : ResidualComponent S) {a b : ℝ}
    (_hab : a < b) (_haS : Circle.exp a ∈ S) (_hbS : Circle.exp b ∈ S)
    (harc : Circle.exp '' Ioo a b = i.val) : b - a < 2 * Real.pi := by
  by_contra hlt
  have hge : 2 * Real.pi ≤ b - a := le_of_not_gt hlt
  obtain ⟨t₁, t₂, t₃, t₄, ht₁, ht₂, ht₃, ht₄,
      h12, h13, h14, h23, h24, h34⟩ := hfour
  obtain ⟨t, htS, hta⟩ : ∃ t : Circle, t ∈ S ∧ t ≠ Circle.exp a := by
    by_cases h : t₁ = Circle.exp a
    · exact ⟨t₂, ht₂, by intro e; exact h12 (h.trans e.symm)⟩
    · exact ⟨t₁, ht₁, h⟩
  obtain ⟨r, hr⟩ := Circle.exp_surjective t
  obtain ⟨y, hy, hyeq⟩ := Circle.periodic_exp.exists_mem_Ioc
    Real.two_pi_pos r a
  have hyIoo : y ∈ Ioo a b := by
    refine ⟨hy.1, ?_⟩
    have hyb : y ≤ b := le_trans hy.2 (by linarith)
    refine lt_of_le_of_ne hyb ?_
    intro hybeq
    apply hta
    have hba : b = a + 2 * Real.pi := by linarith [hge, hy.2]
    have hper : Circle.exp b = Circle.exp a := by
      rw [hba]
      simp
    have hperY : Circle.exp y = Circle.exp a := by rw [hybeq]; exact hper
    exact (hyeq.symm.trans hr).symm.trans hperY
  have hti : t ∈ i.val := by
    rw [← harc]
    exact ⟨y, hyIoo, hyeq.symm.trans hr⟩
  exact (residual_component_subset_compl S i hti) htS

theorem cairns_residual_component_lift_endpoint_normalization
    (S : Set Circle) (hS : IsClosed S)
    (hfour : ∃ t₁ t₂ t₃ t₄ : Circle, t₁ ∈ S ∧ t₂ ∈ S ∧ t₃ ∈ S ∧ t₄ ∈ S ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄)
    (i : ResidualComponent S) :
    ∃ a b : ℝ, a < b ∧ b - a < 2 * Real.pi ∧ Circle.exp a ∈ S ∧
      Circle.exp b ∈ S ∧ Circle.exp '' Ioo a b = i.val := by
  obtain ⟨a, b, hab, haS, hbS, harc⟩ :=
    cairns_residual_component_boundary_lift S hS (by
      obtain ⟨t₁, t₂, t₃, t₄, ht₁, ht₂, ht₃, ht₄, -⟩ := hfour
      exact ⟨t₁, ht₁⟩) i
  have hturn := cairns_residual_component_no_full_turn S hS hfour i hab haS hbS harc
  exact ⟨a, b, hab, hturn, haS, hbS, harc⟩

theorem cairns_residual_component_angular_classification
    (S : Set Circle) (hS : IsClosed S)
    (hfour : ∃ t₁ t₂ t₃ t₄ : Circle, t₁ ∈ S ∧ t₂ ∈ S ∧ t₃ ∈ S ∧ t₄ ∈ S ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄)
    (i : ResidualComponent S) :
    ∃ a b : ℝ, a < b ∧ b - a < 2 * Real.pi ∧ Circle.exp a ∈ S ∧
      Circle.exp b ∈ S ∧ Circle.exp '' Ioo a b = i.val := by
  exact cairns_residual_component_lift_endpoint_normalization S hS hfour i

/-!
# Angular gap extraction for a Cairns residual component

Source: Cairns (1951), §4(C), printed pp.864–865, the complementary arcs of
retained contacts and Lemma 4.1.  A residual component of the complement of a
closed retained contact set is represented by a proper oriented angular gap;
its endpoints are retained contacts and its open arc is exactly the component.
The four-contact hypothesis excludes the degenerate full-circle case.
-/
theorem cairns_gap_of_residual_component
    (S : Set Circle) (hS : IsClosed S)
    (hfour : ∃ t₁ t₂ t₃ t₄ : Circle, t₁ ∈ S ∧ t₂ ∈ S ∧ t₃ ∈ S ∧ t₄ ∈ S ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₁ ≠ t₄ ∧ t₂ ≠ t₃ ∧ t₂ ≠ t₄ ∧ t₃ ≠ t₄)
    (i : ResidualComponent S) :
    ∃ g : CairnsCircleGap, g.IsGapOf S ∧ g.openArc = i.val := by
  obtain ⟨a, b, hab, hturn, haS, hbS, harc⟩ :=
    cairns_residual_component_angular_classification S hS hfour i
  let g : CairnsCircleGap :=
    { start := a, stop := b, start_lt_stop := hab, shorter_than_turn := hturn }
  refine ⟨g, ?_, ?_⟩
  · refine ⟨haS, hbS, ?_⟩
    exact ⟨Classical.choose i.property, (Classical.choose_spec i.property).1,
      (Classical.choose_spec i.property).2.trans harc.symm⟩
  · change Circle.exp '' Ioo a b = i.val
    exact harc

end HolomorphicAnosov.Topology.Plane

