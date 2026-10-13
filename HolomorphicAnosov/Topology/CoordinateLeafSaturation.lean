import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Open coordinate-component saturations

DAG node: `topo.coordinate_component_saturation_open_g6`.
Agent-written expansion of Ghys Lemma 5.2 p.599, omitted openness argument.
-/

open Set Topology _root_.Topology Filter

namespace HolomorphicAnosov.Topology

/-- The union of vertical fibre components meeting one horizontal fibre component
of a local homeomorphism into a product of locally connected spaces is open.

Source: Ghys, Holomorphic Anosov systems, Lemma 5.2, p.599, the assertion that
U(s) is open. This proof expands the source's omitted local-product argument.
A rectangular inverse chart through a point of the horizontal component lies in
the saturation: join first horizontally to a meeting point, then vertically to
the desired point. Thus the entire horizontal component is in the interior of
the saturation. In any vertical plaque box, interior membership is constant
along each vertical plaque, because projecting an open subset is open and its
plaque saturation stays in the original saturated set. This is locally constant
on each connected vertical fibre component, hence constant there. Each such
component meeting the horizontal one is therefore contained in the interior,
so the saturation equals its interior. No global injectivity or leaf topology
identification is used. -/
theorem isOpen_coordinate_component_saturation {X P Q : Type*} [TopologicalSpace X]
    [TopologicalSpace P] [TopologicalSpace Q]
    [LocallyConnectedSpace P] [LocallyConnectedSpace Q]
    (D : X → P × Q) (hD : IsLocalHomeomorph D) (x : X) :
    IsOpen {z | ∃ y ∈ connectedComponentIn {t | (D t).2 = (D x).2} x,
      z ∈ connectedComponentIn {t | (D t).1 = (D y).1} y} := by
  have interior_saturated_of_openMap (f : X → P) (hf : Continuous f) (ho : IsOpenMap f)
      (hbox : ∀ x : X, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
        ∀ y ∈ N, ∀ z ∈ N, f y = f z →
          z ∈ connectedComponentIn {t | f t = f y} y)
      (S : Set X)
      (hs : ∀ x ∈ S, connectedComponentIn {t | f t = f x} x ⊆ S)
      {x : X} (hx : x ∈ interior S) :
      connectedComponentIn {t | f t = f x} x ⊆ interior S := by
    have hprop (N : Set X) (hN : IsOpen N)
        (hb : ∀ y ∈ N, ∀ z ∈ N, f y = f z →
          z ∈ connectedComponentIn {t | f t = f y} y)
        {y z : X} (hy : y ∈ N) (hz : z ∈ N) (he : f y = f z)
        (hyI : y ∈ interior S) : z ∈ interior S := by
      let W := N ∩ f ⁻¹' (f '' (interior S ∩ N))
      have hW : IsOpen W := hN.inter ((ho _ (isOpen_interior.inter hN)).preimage hf)
      apply mem_interior_iff_mem_nhds.mpr
      apply Filter.mem_of_superset (hW.mem_nhds ⟨hz, y, ⟨hyI, hy⟩, he⟩)
      rintro t ⟨ht, w, ⟨hwI, hw⟩, hwt⟩
      exact hs w (interior_subset hwI) (hb w hw t ht hwt)
    let F := connectedComponentIn {t | f t = f x} x
    let : PreconnectedSpace F := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
    have hlocal : IsLocallyConstant (fun y : F ↦ y.val ∈ interior S) := by
      apply (IsLocallyConstant.iff_exists_open _).mpr
      intro y
      obtain ⟨N, hN, hy, hb⟩ := hbox y.val
      refine ⟨Subtype.val ⁻¹' N, hN.preimage continuous_subtype_val, hy, ?_⟩
      intro z hz
      have he : f y.val = f z.val :=
        (connectedComponentIn_subset _ _ y.property).trans
          (connectedComponentIn_subset _ _ z.property).symm
      apply propext
      exact ⟨hprop N hN hb hz hy he.symm, hprop N hN hb hy hz he⟩
    intro y hy
    have he := hlocal.apply_eq_of_preconnectedSpace ⟨y, hy⟩ ⟨x, mem_connectedComponentIn rfl⟩
    exact he.mpr hx
  have coordinate_component_boxes (D : X → P × Q) (hD : IsLocalHomeomorph D) (x : X) :
      ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
        (∀ y ∈ N, ∀ z ∈ N, (D y).1 = (D z).1 →
          z ∈ connectedComponentIn {t | (D t).1 = (D y).1} y) ∧
        (∀ y ∈ N, ∀ z ∈ N, (D y).2 = (D z).2 →
          z ∈ connectedComponentIn {t | (D t).2 = (D y).2} y) ∧
        (∀ y ∈ N, ∃ z ∈ N,
          (D z).1 = (D y).1 ∧ (D z).2 = (D x).2) := by
    obtain ⟨e, hx, he⟩ := hD x
    have ht := e.open_target.mem_nhds (e.map_source hx)
    obtain ⟨B₀, hB₀, C₀, hC₀, hBC₀⟩ := mem_nhds_prod_iff.mp ht
    obtain ⟨B, ⟨hB, hxB, hcB⟩, hBB₀⟩ :=
      (LocallyConnectedSpace.open_connected_basis (e x).1).mem_iff.mp hB₀
    obtain ⟨C, ⟨hC, hxC, hcC⟩, hCC₀⟩ :=
      (LocallyConnectedSpace.open_connected_basis (e x).2).mem_iff.mp hC₀
    have hBC : B ×ˢ C ⊆ e.target := (Set.prod_mono hBB₀ hCC₀).trans hBC₀
    let N := e.source ∩ e ⁻¹' (B ×ˢ C)
    have hN : IsOpen N := e.continuousOn.isOpen_inter_preimage e.open_source (hB.prod hC)
    have hxN : x ∈ N := ⟨hx, hxB, hxC⟩
    have hv (y : X) (hy : y ∈ N) :
        IsPreconnected ((fun q : Q ↦ e.symm ((e y).1, q)) '' C) := by
      apply hcC.isPreconnected.image
      exact e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun q hq ↦ hBC ⟨hy.2.1, hq⟩)
    have hh (y : X) (hy : y ∈ N) :
        IsPreconnected ((fun p : P ↦ e.symm (p, (e y).2)) '' B) := by
      apply hcB.isPreconnected.image
      exact e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun p hp ↦ hBC ⟨hp, hy.2.2⟩)
    refine ⟨N, hN, hxN, ?_, ?_, ?_⟩
    · intro y hy z hz hyz
      have hsub : (fun q : Q ↦ e.symm ((e y).1, q)) '' C ⊆
          {t | (D t).1 = (D y).1} := by
        rintro _ ⟨q, hq, rfl⟩
        change (D (e.symm ((e y).1, q))).1 = (D y).1
        have hpair : ((e y).1, q) ∈ e.target := hBC ⟨hy.2.1, hq⟩
        rw [he, e.right_inv hpair]
      apply (hv y hy).subset_connectedComponentIn ?_ hsub
      · refine ⟨(e z).2, hz.2.2, ?_⟩
        rw [he] at hyz
        dsimp only
        rw [hyz]
        exact e.left_inv hz.1
      · exact ⟨(e y).2, hy.2.2, e.left_inv hy.1⟩
    · intro y hy z hz hyz
      have hsub : (fun p : P ↦ e.symm (p, (e y).2)) '' B ⊆
          {t | (D t).2 = (D y).2} := by
        rintro _ ⟨p, hp, rfl⟩
        change (D (e.symm (p, (e y).2))).2 = (D y).2
        have hpair : (p, (e y).2) ∈ e.target := hBC ⟨hp, hy.2.2⟩
        rw [he, e.right_inv hpair]
      apply (hh y hy).subset_connectedComponentIn ?_ hsub
      · refine ⟨(e z).1, hz.2.1, ?_⟩
        rw [he] at hyz
        dsimp only
        rw [hyz]
        exact e.left_inv hz.1
      · exact ⟨(e y).1, hy.2.1, e.left_inv hy.1⟩
    · intro y hy
      let z := e.symm ((e y).1, (e x).2)
      have hz : ((e y).1, (e x).2) ∈ e.target := hBC ⟨hy.2.1, hxC⟩
      refine ⟨z, ⟨e.map_target hz, ?_⟩, ?_⟩
      · change e (e.symm ((e y).1, (e x).2)) ∈ B ×ˢ C
        rw [e.right_inv hz]
        exact ⟨hy.2.1, hxC⟩
      · dsimp [z]
        rw [he, e.right_inv hz]
        exact ⟨rfl, rfl⟩
  let S : Set X := {z | ∃ y ∈ connectedComponentIn {t | (D t).2 = (D x).2} x,
      z ∈ connectedComponentIn {t | (D t).1 = (D y).1} y}
  have hsat : ∀ y ∈ S, connectedComponentIn {t | (D t).1 = (D y).1} y ⊆ S := by
    rintro y ⟨z, hz, hy⟩ t ht
    refine ⟨z, hz, ?_⟩
    have he : (D y).1 = (D z).1 :=
      connectedComponentIn_subset {t | (D t).1 = (D z).1} z hy
    rw [he] at ht
    rw [connectedComponentIn_eq hy]
    exact ht
  have hbase : connectedComponentIn {t | (D t).2 = (D x).2} x ⊆ interior S := by
    intro y hy
    obtain ⟨N, hN, hyN, hv, hh, hm⟩ := coordinate_component_boxes D hD y
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hN.mem_nhds hyN)
    intro t ht
    obtain ⟨z, hz, hzt, hzy⟩ := hm t ht
    refine ⟨z, ?_, hv z hz t ht hzt⟩
    have hz' := hh y hyN z hz hzy.symm
    have he : (D y).2 = (D x).2 :=
      connectedComponentIn_subset {t | (D t).2 = (D x).2} x hy
    rw [he] at hz'
    rw [connectedComponentIn_eq hy]
    exact hz'
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨z, hz, hy⟩
  apply mem_interior_iff_mem_nhds.mp
  apply interior_saturated_of_openMap (fun t ↦ (D t).1)
    (continuous_fst.comp hD.continuous) (isOpenMap_fst.comp hD.isOpenMap) ?_ S hsat
    (hbase hz) hy
  intro t
  obtain ⟨N, hN, ht, hv, _⟩ := coordinate_component_boxes D hD t
  exact ⟨N, hN, ht, hv⟩


end HolomorphicAnosov.Topology
