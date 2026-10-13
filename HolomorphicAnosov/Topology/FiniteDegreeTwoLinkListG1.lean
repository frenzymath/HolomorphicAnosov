import HolomorphicAnosov.Topology.GallierXuSurfacePresentation
import HolomorphicAnosov.Topology.FiniteSurfacePlanarFrontierG9
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Max

/-!
# Exact interval and circle lists for finite degree-two links

Elementary finite graph adapter for the vertex-link condition in Gallier–Xu,
Chapter 3. Choose a longest simple chain, use the degree bound to make its
vertex set adjacency-closed, and use connectedness to exhaust the graph.
-/

noncomputable section
open Set
namespace HolomorphicAnosov.Topology.GallierXu

lemma exists_longest_simple_chain {N : ℕ} (V : Finset (Fin N))
    (R : Fin N → Fin N → Prop) (hV : V.Nonempty) :
    ∃ l : List (Fin N), l.Nodup ∧ l.IsChain R ∧ (∀ x ∈ l, x ∈ V) ∧
      ∀ m : List (Fin N), m.Nodup → m.IsChain R → (∀ x ∈ m, x ∈ V) → m.length ≤ l.length := by
  classical
  let S : Set (List (Fin N)) := {l | l.Nodup ∧ l.IsChain R ∧ ∀ x ∈ l, x ∈ V}
  have hfin : S.Finite := (List.finite_length_le (Fin N) N).subset
    (fun l hl ↦ by simpa using hl.1.length_le_card)
  obtain ⟨v,hv⟩ := hV
  have hs : ([v] : List (Fin N)) ∈ S := by
    exact ⟨by simp,List.IsChain.singleton v,by simpa using hv⟩
  obtain ⟨l,hl,hmax⟩ := Finset.exists_max_image hfin.toFinset List.length
    ⟨[v],hfin.mem_toFinset.mpr hs⟩
  have hl' := hfin.mem_toFinset.mp hl
  refine ⟨l,hl'.1,hl'.2.1,hl'.2.2,?_⟩
  intro m hm hc hv
  exact hmax m (hfin.mem_toFinset.mpr ⟨hm,hc,hv⟩)

lemma degreeTwo_chain_internal_neighbor {α : Type*} (R : α → α → Prop)
    (hsymm : ∀ ⦃a b⦄, R a b → R b a)
    (hdegree : ∀ a b c d, R a b → R a c → R a d → b = c ∨ b = d ∨ c = d)
    (l : List α) (hnd : l.Nodup) (hc : l.IsChain R)
    (i : ℕ) (hi : 0 < i) (hil : i+1 < l.length)
    (b : α) (hb : R l[i] b) :
    b = l[i-1] ∨ b = l[i+1] := by
  have hip : i-1 < l.length := by omega
  have hprev : R l[i] l[i-1] := by
    have h := hc.getElem (i-1) (by omega)
    have he : i-1+1=i := by omega
    simp only [he] at h
    exact hsymm h
  have hnext := hc.getElem i hil
  rcases hdegree l[i] l[i-1] l[i+1] b hprev hnext hb with he | he | he
  · have hh := hnd.getElem_inj_iff.mp he
    omega
  · exact Or.inl he.symm
  · exact Or.inr he.symm

lemma longest_chain_head_neighbor {N : ℕ} (V : Finset (Fin N))
    (R : Fin N → Fin N → Prop) (hsymm : ∀ ⦃a b⦄, R a b → R b a)
    (hmem : ∀ a b, R a b → a ∈ V ∧ b ∈ V)
    (l : List (Fin N)) (hnd : l.Nodup) (hc : l.IsChain R)
    (hV : ∀ x ∈ l, x ∈ V) (hne : l ≠ [])
    (hmax : ∀ m : List (Fin N), m.Nodup → m.IsChain R →
      (∀ x ∈ m, x ∈ V) → m.length ≤ l.length)
    (b : Fin N) (hb : R (l.head hne) b) : b ∈ l := by
  by_contra hbl
  have hlen := hmax (b :: l) (List.nodup_cons.mpr ⟨hbl,hnd⟩)
    (hc.cons_of_ne_nil hne (hsymm hb)) (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (hmem _ _ hb).2
      · exact hV x hx)
  simp only [List.length_cons] at hlen
  omega

lemma longest_chain_last_neighbor {N : ℕ} (V : Finset (Fin N))
    (R : Fin N → Fin N → Prop) (hsymm : ∀ ⦃a b⦄, R a b → R b a)
    (hmem : ∀ a b, R a b → a ∈ V ∧ b ∈ V)
    (l : List (Fin N)) (hnd : l.Nodup) (hc : l.IsChain R)
    (hV : ∀ x ∈ l, x ∈ V) (hne : l ≠ [])
    (hmax : ∀ m : List (Fin N), m.Nodup → m.IsChain R →
      (∀ x ∈ m, x ∈ V) → m.length ≤ l.length)
    (b : Fin N) (hb : R (l.getLast hne) b) : b ∈ l := by
  have hr : l.reverse.IsChain R := List.isChain_reverse.mpr (hc.imp (fun _ _ h ↦ hsymm h))
  have he : l.reverse ≠ [] := by simpa using hne
  have hh : R (l.reverse.head he) b := by simpa using hb
  have hm : ∀ m : List (Fin N), m.Nodup → m.IsChain R →
      (∀ x ∈ m, x ∈ V) → m.length ≤ l.reverse.length := by
    simpa only [List.length_reverse] using hmax
  have h := longest_chain_head_neighbor V R hsymm hmem l.reverse (List.nodup_reverse.mpr hnd) hr
    (by simpa using hV) he hm b hh
  simpa using h


lemma longest_chain_neighbor_mem {N : ℕ} (V : Finset (Fin N))
    (R : Fin N → Fin N → Prop) (hsymm : ∀ ⦃a b⦄, R a b → R b a)
    (hmem : ∀ a b, R a b → a ∈ V ∧ b ∈ V)
    (hdegree : ∀ a b c d, R a b → R a c → R a d → b = c ∨ b = d ∨ c = d)
    (l : List (Fin N)) (hnd : l.Nodup) (hc : l.IsChain R)
    (hV : ∀ x ∈ l, x ∈ V)
    (hmax : ∀ m : List (Fin N), m.Nodup → m.IsChain R →
      (∀ x ∈ m, x ∈ V) → m.length ≤ l.length)
    (a b : Fin N) (ha : a ∈ l) (hab : R a b) : b ∈ l := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
  have hne : l ≠ [] := by
    intro he
    have hh := i.isLt
    simp [he] at hh
  by_cases hi0 : i.val = 0
  · have he : l.get i = l.head hne := by
      rw [List.head_eq_getElem_zero]
      exact congrArg l.get (Fin.ext hi0)
    exact longest_chain_head_neighbor V R hsymm hmem l hnd hc hV hne hmax b (he ▸ hab)
  by_cases hil : i.val+1 = l.length
  · have he : l.get i = l.getLast hne := by
      rw [List.getLast_eq_getElem]
      exact congrArg l.get (Fin.ext (by change i.val = l.length-1; omega))
    exact longest_chain_last_neighbor V R hsymm hmem l hnd hc hV hne hmax b (he ▸ hab)
  have hin : i.val+1 < l.length := by omega
  rcases degreeTwo_chain_internal_neighbor R hsymm hdegree l hnd hc i.val (by omega) hin b hab with he | he
  · rw [he]
    exact List.getElem_mem _
  · rw [he]
    exact List.getElem_mem _

lemma longest_chain_covers {N : ℕ} (V : Finset (Fin N))
    (R : Fin N → Fin N → Prop) (hVne : V.Nonempty) (hsymm : ∀ ⦃a b⦄, R a b → R b a)
    (hirr : ∀ a, ¬ R a a) (hmem : ∀ a b, R a b → a ∈ V ∧ b ∈ V)
    (hneighbor : ∀ a ∈ V, ∃ b, R a b)
    (hdegree : ∀ a b c d, R a b → R a c → R a d → b = c ∨ b = d ∨ c = d)
    (hconn : ∀ a ∈ V, ∀ b ∈ V, Relation.ReflTransGen R a b)
    (l : List (Fin N)) (hnd : l.Nodup) (hc : l.IsChain R)
    (hV : ∀ x ∈ l, x ∈ V)
    (hmax : ∀ m : List (Fin N), m.Nodup → m.IsChain R →
      (∀ x ∈ m, x ∈ V) → m.length ≤ l.length) :
    2 ≤ l.length ∧ ∀ a, a ∈ l ↔ a ∈ V := by
  obtain ⟨a,ha⟩ := hVne
  obtain ⟨b,hab⟩ := hneighbor a ha
  have hneab : a ≠ b := fun he ↦ hirr b (he ▸ hab)
  have hlen : 2 ≤ l.length := by
    have hh := hmax [a,b] (by simp [hneab]) (by simpa using hab)
      (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl | rfl
          · exact ha
          · exact (hmem _ _ hab).2)
    simpa using hh
  refine ⟨hlen,fun x ↦ ⟨hV x,?_⟩⟩
  intro hx
  have hne : l ≠ [] := by intro he; simp [he] at hlen
  have hh : l.head hne ∈ l := List.head_mem hne
  have hr := hconn (l.head hne) (hV _ hh) x hx
  induction hr with
  | refl => exact hh
  | @tail y z hr hyz ih =>
    exact longest_chain_neighbor_mem V R hsymm hmem hdegree l hnd hc hV hmax y z (ih (hmem y z hyz).1) hyz

lemma degreeTwo_chain_edge_indices {α : Type*} (R : α → α → Prop)
    (hsymm : ∀ ⦃a b⦄, R a b → R b a) (hirr : ∀ a, ¬ R a a)
    (hdegree : ∀ a b c d, R a b → R a c → R a d → b = c ∨ b = d ∨ c = d)
    (l : List α) (hnd : l.Nodup) (hc : l.IsChain R)
    (i j : Fin l.length) (hij : R (l.get i) (l.get j)) :
    (i.val+1=j.val ∨ j.val+1=i.val) ∨
      (i.val=0 ∧ j.val+1=l.length) ∨ (j.val=0 ∧ i.val+1=l.length) := by
  have hne : i.val ≠ j.val := by
    intro he
    have hh : i = j := Fin.ext he
    exact hirr (l.get j) (hh ▸ hij)
  by_cases hii : 0 < i.val ∧ i.val+1 < l.length
  · rcases degreeTwo_chain_internal_neighbor R hsymm hdegree l hnd hc i.val hii.1 hii.2
      (l.get j) hij with he | he
    · have hh := hnd.getElem_inj_iff.mp he
      left; omega
    · have hh := hnd.getElem_inj_iff.mp he
      left; omega
  by_cases hji : 0 < j.val ∧ j.val+1 < l.length
  · rcases degreeTwo_chain_internal_neighbor R hsymm hdegree l hnd hc j.val hji.1 hji.2
      (l.get i) (hsymm hij) with he | he
    · have hh := hnd.getElem_inj_iff.mp he
      left; omega
    · have hh := hnd.getElem_inj_iff.mp he
      left; omega
  omega

lemma pathEdge_get_iff {N : ℕ} (l : List (Fin N)) (hnd : l.Nodup)
    (i j : Fin l.length) :
    pathEdge l (l.get i) (l.get j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  constructor
  · rintro ⟨k,hk,⟨hi,hj⟩ | ⟨hj,hi⟩⟩
    · have hi' := congrArg Fin.val (hnd.get_inj_iff.mp hi)
      have hj' := congrArg Fin.val (hnd.get_inj_iff.mp hj)
      change k = i.val at hi'
      change k+1 = j.val at hj'
      exact Or.inl (by omega)
    · have hi' := congrArg Fin.val (hnd.get_inj_iff.mp hi)
      have hj' := congrArg Fin.val (hnd.get_inj_iff.mp hj)
      change k+1 = i.val at hi'
      change k = j.val at hj'
      exact Or.inr (by omega)
  · rintro (he | he)
    · refine ⟨i.val,by omega,Or.inl ⟨rfl,?_⟩⟩
      exact congrArg l.get (Fin.ext he)
    · refine ⟨j.val,by omega,Or.inr ⟨rfl,?_⟩⟩
      exact congrArg l.get (Fin.ext he)


lemma finRotate_val_cases {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (finRotate n i).val = if i.val+1 < n then i.val+1 else 0 := by
  let : NeZero n := ⟨by omega⟩
  rw [finRotate_apply]
  change (i.val + 1 % n) % n = _
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have he : i.val+1=n := by omega
    simp [he]

lemma cycleEdge_get_iff {N : ℕ} (l : List (Fin N)) (hnd : l.Nodup)
    (hlen : 2 ≤ l.length) (i j : Fin l.length) :
    cycleEdge l (l.get i) (l.get j) ↔
      (i.val+1=j.val ∨ j.val+1=i.val) ∨
        (i.val=0 ∧ j.val+1=l.length) ∨ (j.val=0 ∧ i.val+1=l.length) := by
  constructor
  · rintro ⟨k,⟨hi,hj⟩ | ⟨hj,hi⟩⟩
    · have he := hnd.get_inj_iff.mp hi
      have hh := congrArg Fin.val (hnd.get_inj_iff.mp hj)
      change (finRotate l.length k).val = j.val at hh
      rw [he,finRotate_val_cases hlen] at hh
      split_ifs at hh <;> omega
    · have he := hnd.get_inj_iff.mp hj
      have hh := congrArg Fin.val (hnd.get_inj_iff.mp hi)
      change (finRotate l.length k).val = i.val at hh
      rw [he,finRotate_val_cases hlen] at hh
      split_ifs at hh <;> omega
  · rintro ((hij | hji) | ⟨hi,hj⟩ | ⟨hj,hi⟩)
    · refine ⟨i,Or.inl ⟨rfl,?_⟩⟩
      apply congrArg l.get
      apply Fin.ext
      rw [finRotate_val_cases hlen,ite_eq_left (by omega)]
      exact hij
    · refine ⟨j,Or.inr ⟨rfl,?_⟩⟩
      apply congrArg l.get
      apply Fin.ext
      rw [finRotate_val_cases hlen,ite_eq_left (by omega)]
      exact hji
    · refine ⟨j,Or.inr ⟨rfl,?_⟩⟩
      apply congrArg l.get
      apply Fin.ext
      rw [finRotate_val_cases hlen,ite_eq_right (by omega)]
      exact hi.symm
    · refine ⟨i,Or.inl ⟨rfl,?_⟩⟩
      apply congrArg l.get
      apply Fin.ext
      rw [finRotate_val_cases hlen,ite_eq_right (by omega)]
      exact hj.symm


lemma chain_rel_of_consecutive {α : Type*} (R : α → α → Prop) (hsymm : ∀ ⦃a b⦄, R a b → R b a)
    (l : List α) (hc : l.IsChain R) (i j : Fin l.length)
    (hij : i.val+1=j.val ∨ j.val+1=i.val) : R (l.get i) (l.get j) := by
  rcases hij with hij | hji
  · have hb : i.val+1 < l.length := by omega
    have hh := hc.getElem i.val hb
    change R (l.get i) (l.get ⟨i.val+1,hb⟩) at hh
    rwa [show (⟨i.val+1,hb⟩ : Fin l.length) = j from Fin.ext hij] at hh
  · have hb : j.val+1 < l.length := by omega
    have hh := hc.getElem j.val hb
    change R (l.get j) (l.get ⟨j.val+1,hb⟩) at hh
    rw [show (⟨j.val+1,hb⟩ : Fin l.length) = i from Fin.ext hji] at hh
    exact hsymm hh

lemma list_relation_ext {α : Type*} (l : List α) (R S : α → α → Prop)
    (hR : ∀ a b, R a b → a ∈ l ∧ b ∈ l)
    (hS : ∀ a b, S a b → a ∈ l ∧ b ∈ l)
    (he : ∀ i j : Fin l.length, R (l.get i) (l.get j) ↔ S (l.get i) (l.get j)) :
    ∀ a b, R a b ↔ S a b := by
  intro a b
  constructor
  · intro hab
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (hR a b hab).1
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (hR _ b hab).2
    exact (he i j).mp hab
  · intro hab
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (hS a b hab).1
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (hS _ b hab).2
    exact (he i j).mpr hab

/-- A finite connected nonisolated graph with at most two neighbors per vertex
is an exact simple path or an exact simple cycle, expressed in the lists used
by `SurfaceLinks`. The two-vertex graph is assigned to the interval case. -/
theorem finite_degree_two_link_list {N : ℕ} (V : Finset (Fin N))
    (R : Fin N → Fin N → Prop) (hVne : V.Nonempty) (hsymm : ∀ ⦃a b⦄, R a b → R b a)
    (hirr : ∀ a, ¬ R a a) (hmem : ∀ a b, R a b → a ∈ V ∧ b ∈ V)
    (hneighbor : ∀ a ∈ V, ∃ b, R a b)
    (hdegree : ∀ a b c d, R a b → R a c → R a d → b = c ∨ b = d ∨ c = d)
    (hconn : ∀ a ∈ V, ∀ b ∈ V, Relation.ReflTransGen R a b) :
    ∃ l : List (Fin N), l.Nodup ∧ (∀ a, a ∈ l ↔ a ∈ V) ∧
      ((3 ≤ l.length ∧ ∀ a b, R a b ↔ cycleEdge l a b) ∨
        (2 ≤ l.length ∧ ∀ a b, R a b ↔ pathEdge l a b)) := by
  classical
  obtain ⟨l,hnd,hc,hV,hmax⟩ := exists_longest_simple_chain V R hVne
  obtain ⟨hlen,hcover⟩ := longest_chain_covers V R hVne hsymm hirr hmem hneighbor hdegree hconn
    l hnd hc hV hmax
  have hRmem : ∀ a b, R a b → a ∈ l ∧ b ∈ l := by
    intro a b hab
    exact ⟨(hcover a).mpr (hmem a b hab).1,(hcover b).mpr (hmem a b hab).2⟩
  let first : Fin l.length := ⟨0,by omega⟩
  let last : Fin l.length := ⟨l.length-1,by omega⟩
  have hwrap (i j : Fin l.length) (hi : i.val=0) (hj : j.val+1=l.length) :
      i = first ∧ j = last := by
    exact ⟨Fin.ext hi,Fin.ext (by change j.val=l.length-1; omega)⟩
  refine ⟨l,hnd,hcover,?_⟩
  by_cases hclose : 3 ≤ l.length ∧ R (l.get first) (l.get last)
  · left
    refine ⟨hclose.1,?_⟩
    apply list_relation_ext l R (cycleEdge l) hRmem
    · intro a b hab
      obtain ⟨i,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := hab
      · exact ⟨List.get_mem _ _,List.get_mem _ _⟩
      · exact ⟨List.get_mem _ _,List.get_mem _ _⟩
    · intro i j
      rw [cycleEdge_get_iff l hnd hlen]
      constructor
      · exact degreeTwo_chain_edge_indices R hsymm hirr hdegree l hnd hc i j
      · rintro (hij | ⟨hi,hj⟩ | ⟨hj,hi⟩)
        · exact chain_rel_of_consecutive R hsymm l hc i j hij
        · obtain ⟨rfl,rfl⟩ := hwrap i j hi hj
          exact hclose.2
        · obtain ⟨rfl,rfl⟩ := hwrap j i hj hi
          exact hsymm hclose.2
  · right
    refine ⟨hlen,?_⟩
    apply list_relation_ext l R (pathEdge l) hRmem
    · intro a b hab
      obtain ⟨i,hi,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := hab
      · exact ⟨List.get_mem _ _,List.get_mem _ _⟩
      · exact ⟨List.get_mem _ _,List.get_mem _ _⟩
    · intro i j
      rw [pathEdge_get_iff l hnd]
      constructor
      · intro hij
        rcases degreeTwo_chain_edge_indices R hsymm hirr hdegree l hnd hc i j hij with he | ⟨hi,hj⟩ | ⟨hj,hi⟩
        · exact he
        · by_cases h3 : 3 ≤ l.length
          · obtain ⟨rfl,rfl⟩ := hwrap i j hi hj
            exact False.elim (hclose ⟨h3,hij⟩)
          · omega
        · by_cases h3 : 3 ≤ l.length
          · obtain ⟨rfl,rfl⟩ := hwrap j i hj hi
            exact False.elim (hclose ⟨h3,hsymm hij⟩)
          · omega
      · exact chain_rel_of_consecutive R hsymm l hc i j


lemma linkEdge_symm {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) (v : Fin N) :
    ∀ ⦃a b⦄, linkEdge K v a b → linkEdge K v b a := by
  intro a b h
  exact ⟨h.1.symm,h.2.2.1,h.2.1,by simpa only [Finset.pair_comm a b] using h.2.2.2⟩

lemma linkEdge_vertices {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (v a b : Fin N) (h : linkEdge K v a b) :
    (a ≠ v ∧ ({v,a} : Finset (Fin N)) ∈ K.faces) ∧
      (b ≠ v ∧ ({v,b} : Finset (Fin N)) ∈ K.faces) := by
  constructor
  · refine ⟨h.2.1,?_⟩
    exact (K.isRelLowerSet_faces h.2.2.2).2 (by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢; tauto) (by simp)
  · refine ⟨h.2.2.1,?_⟩
    exact (K.isRelLowerSet_faces h.2.2.2).2 (by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢; tauto) (by simp)

lemma linkEdge_triangle_mem {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (v a b : Fin N) (h : linkEdge K v a b) :
    ({v,a,b} : Finset (Fin N)) ∈ (simplices K 2).filter (fun t ↦ ({v,a} : Finset (Fin N)) ⊆ t) := by
  classical
  have hcard : ({v,a,b} : Finset (Fin N)).card = 3 := by
    simp [h.1,h.2.1.symm,h.2.2.1.symm]
  simp only [Finset.mem_filter,simplices,Finset.mem_univ,true_and]
  exact ⟨⟨h.2.2.2,hcard⟩,by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢; tauto⟩

lemma linkEdge_third_injective {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (v a b c : Fin N) (hb : linkEdge K v a b) (_hc : linkEdge K v a c)
    (he : ({v,a,b} : Finset (Fin N)) = {v,a,c}) : b = c := by
  have hh : b ∈ ({v,a,c} : Finset (Fin N)) := he ▸ (by simp)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  exact (hh.resolve_left hb.2.2.1).resolve_left hb.1.symm

/-- Edge incidence at most two is the degree bound for every vertex link. -/
theorem linkEdge_degree_two {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (hinc : ∀ e ∈ simplices K 1, incidence K e ≤ 2) (v a b c d : Fin N)
    (hb : linkEdge K v a b) (hc : linkEdge K v a c) (hd : linkEdge K v a d) :
    b = c ∨ b = d ∨ c = d := by
  classical
  by_contra h
  push Not at h
  have htri : 2 < ((simplices K 2).filter (fun t ↦ ({v,a} : Finset (Fin N)) ⊆ t)).card := by
    apply Finset.two_lt_card_iff.mpr
    refine ⟨{v,a,b},{v,a,c},{v,a,d},linkEdge_triangle_mem K v a b hb,
      linkEdge_triangle_mem K v a c hc,linkEdge_triangle_mem K v a d hd,?_,?_,?_⟩
    · exact fun he ↦ h.1 (linkEdge_third_injective K v a b c hb hc he)
    · exact fun he ↦ h.2.1 (linkEdge_third_injective K v a b d hb hd he)
    · exact fun he ↦ h.2.2 (linkEdge_third_injective K v a c d hc hd he)
  have he : ({v,a} : Finset (Fin N)) ∈ simplices K 1 := by
    have hf := (linkEdge_vertices K v a b hb).1.2
    simp [simplices,hf,hb.2.1.symm]
  exact (not_lt_of_ge (hinc _ he)) htri

/-- For a pure triangle complex with edge incidence at most two, the sole
additional condition needed for exact surface-link lists is connectivity of
each original simplicial link. -/
theorem surfaceLinks_of_link_chainConnected {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (hpure : PureTwo K)
    (hinc : ∀ e ∈ simplices K 1, incidence K e ≤ 2)
    (hconn : ∀ v a b : Fin N,
      (a ≠ v ∧ ({v,a} : Finset (Fin N)) ∈ K.faces) →
      (b ≠ v ∧ ({v,b} : Finset (Fin N)) ∈ K.faces) →
      Relation.ReflTransGen (linkEdge K v) a b) : SurfaceLinks K := by
  classical
  intro v
  let V := Finset.univ.filter (fun a ↦ a ≠ v ∧ ({v,a} : Finset (Fin N)) ∈ K.faces)
  have hV (a : Fin N) : a ∈ V ↔ a ≠ v ∧ ({v,a} : Finset (Fin N)) ∈ K.faces := by simp [V]
  have hne : V.Nonempty := by
    obtain ⟨t,ht,htc,hsub⟩ := hpure {v} (K.singleton_mem v)
    obtain ⟨a,ha,hav⟩ := Finset.exists_mem_ne (by omega : 1 < t.card) v
    refine ⟨a,(hV a).mpr ⟨hav,?_⟩⟩
    apply (K.isRelLowerSet_faces ht).2 _ (by simp)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hsub (by simp)
    · exact (Finset.mem_singleton.mp hx) ▸ ha
  have hn (a : Fin N) (ha : a ∈ V) : ∃ b, linkEdge K v a b := by
    have ha' := (hV a).mp ha
    obtain ⟨t,ht,htc,hsub⟩ := hpure {v,a} ha'.2
    obtain ⟨b,hbv,hba,he⟩ := triangle_third_vertex_g9 htc ha'.1.symm
      (hsub (by simp)) (hsub (by simp))
    exact ⟨b,hba.symm,ha'.1,hbv,he ▸ ht⟩
  obtain ⟨l,hnd,hcover,hshape⟩ := finite_degree_two_link_list V (linkEdge K v) hne
    (linkEdge_symm K v) (fun a h ↦ h.1 rfl)
    (fun a b h ↦ ⟨(hV a).mpr (linkEdge_vertices K v a b h).1,
      (hV b).mpr (linkEdge_vertices K v a b h).2⟩)
    hn (linkEdge_degree_two K hinc v)
    (fun a ha b hb ↦ hconn v a b ((hV a).mp ha) ((hV b).mp hb))
  exact ⟨l,hnd,fun a ↦ (hcover a).trans (hV a),hshape⟩


lemma boundaryEdge_symm_g1 {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) :
    ∀ ⦃a b⦄, boundaryEdge K a b → boundaryEdge K b a := by
  intro a b h
  exact ⟨h.1.symm,by simpa only [Finset.pair_comm] using h.2.1,
    by simpa only [Finset.pair_comm] using h.2.2⟩

lemma boundaryEdge_link_unique {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (v a : Fin N) (h : boundaryEdge K v a) (b c : Fin N)
    (hb : linkEdge K v a b) (hc : linkEdge K v a c) : b = c := by
  classical
  obtain ⟨t,ht⟩ := Finset.card_eq_one.mp h.2.2
  have hb' := linkEdge_triangle_mem K v a b hb
  have hc' := linkEdge_triangle_mem K v a c hc
  rw [ht,Finset.mem_singleton] at hb' hc'
  exact linkEdge_third_injective K v a b c hb hc (hb'.trans hc'.symm)

lemma circularLink_not_boundaryEdge {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N)
    (l : List (Fin N)) (hnd : l.Nodup) (hlen : 3 ≤ l.length)
    (hvertices : ∀ a, a ∈ l ↔ a ≠ v ∧ ({v,a} : Finset (Fin N)) ∈ K.faces)
    (hlink : ∀ a b, linkEdge K v a b ↔ cycleEdge l a b) :
    ∀ a, ¬ boundaryEdge K v a := by
  intro a ha
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((hvertices a).mpr ⟨ha.1.symm,ha.2.1⟩)
  subst a
  let j := (finRotate l.length).symm i
  have hj : finRotate l.length j = i := (finRotate l.length).apply_symm_apply i
  have h₁ : linkEdge K v (l.get i) (l.get (finRotate l.length i)) :=
    (hlink _ _).mpr ⟨i,Or.inl ⟨rfl,rfl⟩⟩
  have h₂ : linkEdge K v (l.get i) (l.get j) :=
    (hlink _ _).mpr ⟨j,Or.inr ⟨rfl,by rw [hj]⟩⟩
  have he := hnd.injective_get (boundaryEdge_link_unique K v (l.get i) ha _ _ h₁ h₂)
  exact finRotate_twice_ne_g9 hlen j (by rw [hj]; exact he.symm)

lemma intervalLink_boundaryEdge_iff {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (v : Fin N)
    (l : List (Fin N)) (hnd : l.Nodup) (hlen : 2 ≤ l.length)
    (hvertices : ∀ a, a ∈ l ↔ a ≠ v ∧ ({v,a} : Finset (Fin N)) ∈ K.faces)
    (hlink : ∀ a b, linkEdge K v a b ↔ pathEdge l a b) (a : Fin N) :
    boundaryEdge K v a ↔ a = l.get ⟨0,by omega⟩ ∨ a = l.get ⟨l.length-1,by omega⟩ := by
  constructor
  · intro ha
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((hvertices a).mpr ⟨ha.1.symm,ha.2.1⟩)
    subst a
    by_cases hfirst : i.val = 0
    · exact Or.inl (congrArg l.get (Fin.ext hfirst))
    by_cases hlast : i.val = l.length-1
    · exact Or.inr (congrArg l.get (Fin.ext hlast))
    have hleft : i.val-1 < l.length := by omega
    have hright : i.val+1 < l.length := by omega
    have h₁ : linkEdge K v (l.get i) (l.get ⟨i.val-1,hleft⟩) := by
      apply (hlink _ _).mpr
      apply (pathEdge_get_iff l hnd _ _).mpr
      right; dsimp; omega
    have h₂ : linkEdge K v (l.get i) (l.get ⟨i.val+1,hright⟩) := by
      apply (hlink _ _).mpr
      apply (pathEdge_get_iff l hnd _ _).mpr
      left; rfl
    have he := congrArg Fin.val (hnd.injective_get
      (boundaryEdge_link_unique K v (l.get i) ha _ _ h₁ h₂))
    dsimp at he
    omega
  · rintro (rfl | rfl)
    · exact intervalLink_first_boundaryEdge_g9 K v l hnd hlen hlink
    · exact intervalLink_last_boundaryEdge_g9 K v l hnd hlen hlink

/-- Every boundary vertex of a finite surface has exactly two distinct
boundary neighbors: they are the endpoints of its interval link. -/
theorem surface_boundary_neighbors {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (hlinks : SurfaceLinks K) (v a : Fin N) (ha : boundaryEdge K v a) :
    ∃ b c : Fin N, b ≠ c ∧ ∀ w, boundaryEdge K v w ↔ w = b ∨ w = c := by
  obtain ⟨l,hnd,hvertices,hcircle | hpath⟩ := hlinks v
  · exact (circularLink_not_boundaryEdge K v l hnd hcircle.1 hvertices hcircle.2 a ha).elim
  · refine ⟨l.get ⟨0,by omega⟩,l.get ⟨l.length-1,by omega⟩,?_,?_⟩
    · intro he
      have hh := congrArg Fin.val (hnd.injective_get he)
      dsimp at hh
      omega
    · exact intervalLink_boundaryEdge_iff K v l hnd hpath.1 hvertices hpath.2

/-- A finite connected simple graph with degree exactly two is represented by
one simple cyclic list containing exactly its vertices and edges. -/
theorem finite_degree_two_cycle {N : ℕ} (V : Finset (Fin N))
    (R : Fin N → Fin N → Prop) (hVne : V.Nonempty) (hsymm : ∀ ⦃a b⦄, R a b → R b a)
    (hirr : ∀ a, ¬ R a a) (hmem : ∀ a b, R a b → a ∈ V ∧ b ∈ V)
    (hdegree : ∀ a ∈ V, ∃ b c, b ≠ c ∧ ∀ w, R a w ↔ w = b ∨ w = c)
    (hconn : ∀ a ∈ V, ∀ b ∈ V, Relation.ReflTransGen R a b) :
    ∃ l : List (Fin N), l.Nodup ∧ 3 ≤ l.length ∧
      (∀ a, a ∈ l ↔ a ∈ V) ∧ ∀ a b, R a b ↔ cycleEdge l a b := by
  have hn (a : Fin N) (ha : a ∈ V) : ∃ b, R a b := by
    obtain ⟨b,c,_,he⟩ := hdegree a ha
    exact ⟨b,(he b).mpr (Or.inl rfl)⟩
  have hd (a b c d : Fin N) (hb : R a b) (hc : R a c) (hd : R a d) :
      b = c ∨ b = d ∨ c = d := by
    obtain ⟨u,v,_,he⟩ := hdegree a (hmem a b hb).1
    have h₁ := (he b).mp hb
    have h₂ := (he c).mp hc
    have h₃ := (he d).mp hd
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
      rcases h₃ with rfl | rfl <;> tauto
  obtain ⟨l,hnd,hcover,hcircle | hpath⟩ := finite_degree_two_link_list V R hVne hsymm hirr hmem hn hd hconn
  · exact ⟨l,hnd,hcircle.1,hcover,hcircle.2⟩
  · let a := l.get ⟨0,by omega⟩
    have ha : a ∈ V := (hcover a).mp (List.get_mem _ _)
    obtain ⟨b,c,hbc,he⟩ := hdegree a ha
    have hb := (hpath.2 a b).mp ((he b).mpr (Or.inl rfl))
    have hc := (hpath.2 a c).mp ((he c).mpr (Or.inr rfl))
    have hb' := (pathEdge_first_iff_g9 l hnd hpath.1 b).mp hb
    have hc' := (pathEdge_first_iff_g9 l hnd hpath.1 c).mp hc
    exact (hbc (hb'.trans hc'.symm)).elim

end HolomorphicAnosov.Topology.GallierXu
