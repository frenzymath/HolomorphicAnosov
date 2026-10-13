import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.UnitInterval
import HolomorphicAnosov.Topology.WhyburnCircleSplit
import HolomorphicAnosov.Topology.AccumulatingChordArcClassification
import HolomorphicAnosov.Topology.CairnsBoundaryArcPastingCore

open Set Metric

namespace HolomorphicAnosov.Topology

/-- The embedded boundary circle supplies the two complementary arcs cut by the seam endpoints.

Source: Cairns (1951), §4(D), pp.865--866; the exact circle split is the
Whyburn two-arc lemma already formalized in `circle_split_two_arcs`.  This
wrapper transports that lemma through the given boundary homeomorphism and
records the ambient set equalities needed for the half-disk pasting. -/
theorem cairns_halfdisk_complementary_arcs
    (c : Set ℂ) (p q : ℂ)
    (e : c ≃ₜ sphere (0 : ℂ) 1)
    (hp : p ∈ c) (hq : q ∈ c) (hpq : p ≠ q) :
    ∃ e₂ e₃ : unitInterval → ℂ,
      Topology.IsEmbedding e₂ ∧ Topology.IsEmbedding e₃ ∧
      e₂ 0 = p ∧ e₂ 1 = q ∧ e₃ 0 = q ∧ e₃ 1 = p ∧
      range e₂ ∪ range e₃ = c ∧ range e₂ ∩ range e₃ = {p, q} := by
  have hj : Function.Injective (fun z : Circle ↦ (e.symm z : ℂ)) := by
    intro x y hxy
    apply e.symm.injective
    exact Subtype.ext hxy
  have hJ : range (fun z : Circle ↦ (e.symm z : ℂ)) = c := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, rfl⟩
      exact (e.symm w).property
    · intro z hz
      refine ⟨e ⟨z, hz⟩, ?_⟩
      simp
  obtain ⟨u, v, hu, hv, huv, e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃, hun, hint⟩ :=
    circle_split_two_arcs (fun z : Circle ↦ (e.symm z : ℂ))
      (e.symm.continuous.subtype_val.isClosedEmbedding hj).isEmbedding
      p q ⟨e ⟨p, hp⟩, by simp⟩ ⟨e ⟨q, hq⟩, by simp⟩ hpq
  refine ⟨e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃, ?_, ?_⟩
  · rw [← hJ]
    exact hun
  · simpa [hJ] using hint

/-!  The seam's relative interior is exactly the image of the open parameter
interval.  This elementary identity is the interval bookkeeping needed before
transporting the seam to `Circle`; it keeps endpoint exclusion explicit rather
than hidden in a relative-topology assertion. -/
theorem cairns_embedded_seam_relative_interior
    (B : Set ℂ) (p q : ℂ) (b : unitInterval → ℂ)
    (hb : Topology.IsEmbedding b) (hrange : range b = B)
    (h0 : b 0 = p) (h1 : b 1 = q) :
    B \ {p, q} = b '' Ioo 0 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := (hrange ▸ hx.1)
    have ht0 : t ≠ (0 : unitInterval) := by
      intro ht
      apply hx.2
      left
      simpa [ht] using h0
    have ht1 : t ≠ (1 : unitInterval) := by
      intro ht
      apply hx.2
      right
      simpa [ht] using h1
    refine ⟨t, ?_, rfl⟩
    exact ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
      lt_of_le_of_ne t.property.2 ht1⟩
  · rintro ⟨t, ht, rfl⟩
    constructor
    · rw [← hrange]
      exact mem_range_self t
    · intro h
      rcases h with h | h
      · have heq : t = (0 : unitInterval) := hb.injective (h.trans h0.symm)
        exact (ne_of_gt ht.1) heq
      · have heq : t = (1 : unitInterval) := hb.injective (h.trans h1.symm)
        exact (ne_of_lt ht.2) heq

/-!  The image of the open parameter interval remains connected after
transport to the boundary circle. -/
theorem cairns_halfdisk_seam_preimage_connected
    (c B : Set ℂ) (p q : ℂ) (e : c ≃ₜ sphere (0 : ℂ) 1)
    (b : unitInterval → ℂ) (hb : Topology.IsEmbedding b)
    (hrange : range b = B) (h0 : b 0 = p) (h1 : b 1 = q)
    (hproper : B ⊆ c) :
    IsConnected {z : Circle | (e.symm z : ℂ) ∈ B \ {p, q}} := by
  have hB : IsConnected (B \ {p, q}) := by
    rw [cairns_embedded_seam_relative_interior B p q b hb hrange h0 h1]
    exact (isConnected_Ioo (show (0 : unitInterval) < 1 by norm_num)).image
      b hb.continuous.continuousOn
  let f : unitInterval → Circle := fun t =>
    e ⟨b t, hproper (hrange ▸ mem_range_self t)⟩
  have hf : Continuous f := by
    apply e.continuous.comp
    apply hb.continuous.subtype_mk
  have hset : {z : Circle | (e.symm z : ℂ) ∈ B \ {p, q}} =
      f '' Ioo 0 1 := by
    ext z
    constructor
    · intro hz
      have hz' : (e.symm z : ℂ) ∈ B \ {p, q} := hz
      rw [cairns_embedded_seam_relative_interior B p q b hb hrange h0 h1] at hz'
      obtain ⟨t, ht, hbt⟩ := hz'
      refine ⟨t, ht, ?_⟩
      change e ⟨b t, _⟩ = z
      rw [← e.apply_symm_apply z]
      exact congrArg e (Subtype.ext hbt)
    · rintro ⟨t, ht, rfl⟩
      change (e.symm (f t) : ℂ) ∈ B \ {p, q}
      rw [Homeomorph.symm_apply_apply]
      exact (cairns_embedded_seam_relative_interior B p q b hb hrange h0 h1) ▸
        ⟨t, ht, rfl⟩
  rw [hset]
  exact (isConnected_Ioo (show (0 : unitInterval) < 1 by norm_num)).image f hf.continuousOn

/-! A simple interval arc in the circle occupies one of the two directed arcs.
This is the compact-interval component argument used in Cairns §4(D). -/
theorem cairns_circle_arc_range (b : unitInterval → Circle)
    (hb : Topology.IsEmbedding b) :
    range b = range (Circle.path (b 0) (b 1)) ∨
      range b = range (Circle.path (b 1) (b 0)) := by
  have hne : b 0 ≠ b 1 := hb.injective.ne zero_ne_one
  let A := range (Circle.path (b 0) (b 1))
  let D := range (Circle.path (b 1) (b 0))
  let s := b '' Ioo 0 1
  have hs : IsPreconnected s := isPreconnected_Ioo.image b hb.continuous.continuousOn
  have hcover : s ⊆ A ∪ D := by
    rw [show A ∪ D = univ from Circle.range_path_union_range_path hne]
    exact subset_univ _
  have hdis : s ∩ (A ∩ D) = ∅ := by
    rw [show A ∩ D = {b 0, b 1} from Circle.range_path_inter_range_path hne]
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨t, ht, rfl⟩, hx⟩
    rcases (show b t = b 0 ∨ b t = b 1 from by
      simpa only [mem_insert_iff, mem_singleton_iff] using hx) with hx | hx
    · exact ht.1.ne' (hb.injective hx)
    · exact ht.2.ne (hb.injective hx)
  have hsplit : s ⊆ A ∨ s ⊆ D :=
    isPreconnected_iff_subset_of_disjoint_closed.mp hs A D
      (isCompact_range (Circle.path (b 0) (b 1)).continuous).isClosed
      (isCompact_range (Circle.path (b 1) (b 0)).continuous).isClosed hcover hdis
  have hfull {P : Set Circle} (hP : s ⊆ P) (h0 : b 0 ∈ P) (h1 : b 1 ∈ P) :
      range b ⊆ P := by
    rintro x ⟨t, rfl⟩
    by_cases ht0 : t = 0
    · simpa only [ht0] using h0
    by_cases ht1 : t = 1
    · simpa only [ht1] using h1
    exact hP ⟨t, ⟨lt_of_le_of_ne (bot_le : (0 : unitInterval) ≤ t)
      (Ne.symm ht0), lt_of_le_of_ne (le_top : t ≤ (1 : unitInterval)) ht1⟩, rfl⟩
  have hfill (a : unitInterval → Circle) (ha : Topology.IsEmbedding a)
      (hba : range b ⊆ range a)
      (he : (b 0 = a 0 ∧ b 1 = a 1) ∨ (b 0 = a 1 ∧ b 1 = a 0)) :
      range b = range a := by
    let e := ha.toHomeomorph
    let k : unitInterval → unitInterval := fun t ↦
      e.symm ⟨b t, hba ⟨t, rfl⟩⟩
    have hk : Continuous k := e.symm.continuous.comp
      (hb.continuous.subtype_mk (fun t ↦ hba ⟨t, rfl⟩))
    have hak (t : unitInterval) : a (k t) = b t :=
      congrArg Subtype.val (e.apply_symm_apply _)
    have hkends : (k 0 = 0 ∧ k 1 = 1) ∨ (k 0 = 1 ∧ k 1 = 0) := by
      rcases he with he | he
      · exact Or.inl ⟨ha.injective ((hak 0).trans he.1),
          ha.injective ((hak 1).trans he.2)⟩
      · exact Or.inr ⟨ha.injective ((hak 0).trans he.1),
          ha.injective ((hak 1).trans he.2)⟩
    apply Subset.antisymm hba
    rintro x ⟨t, rfl⟩
    have ht : t ∈ Set.uIcc (k 0) (k 1) := by
      rcases hkends with he | he <;> rw [he.1, he.2] <;>
        simp [show t ≤ 1 from t.property.2]
    obtain ⟨r, _, hr⟩ := intermediate_value_uIcc hk.continuousOn ht
    exact ⟨r, (hak r).symm.trans (congrArg a hr)⟩
  rcases hsplit with hA | hD
  · apply Or.inl
    apply hfill _ ((Circle.path (b 0) (b 1)).continuous.isClosedEmbedding
      (Circle.path_injective_of_ne hne)).isEmbedding
    · exact hfull hA (Circle.path (b 0) (b 1)).source_mem_range
        (Circle.path (b 0) (b 1)).target_mem_range
    · exact Or.inl ⟨(Circle.path (b 0) (b 1)).source.symm,
        (Circle.path (b 0) (b 1)).target.symm⟩
  · apply Or.inr
    apply hfill _ ((Circle.path (b 1) (b 0)).continuous.isClosedEmbedding
      (Circle.path_injective_of_ne hne.symm)).isEmbedding
    · exact hfull hD (Circle.path (b 1) (b 0)).target_mem_range
        (Circle.path (b 1) (b 0)).source_mem_range
    · exact Or.inr ⟨(Circle.path (b 1) (b 0)).target.symm,
        (Circle.path (b 1) (b 0)).source.symm⟩

theorem cairns_circle_open_arc_range (b : unitInterval → Circle)
    (hb : Topology.IsEmbedding b) :
    b '' Ioo 0 1 = Circle.path (b 0) (b 1) '' Ioo 0 1 ∨
      b '' Ioo 0 1 = Circle.path (b 1) (b 0) '' Ioo 0 1 := by
  have hne : b 0 ≠ b 1 := hb.injective.ne zero_ne_one
  have hrel (a : unitInterval → Circle) (ha : Topology.IsEmbedding a)
      (x y : Circle) (h0 : a 0 = x) (h1 : a 1 = y) :
      range a \ {x, y} = a '' Ioo 0 1 := by
    ext z
    constructor
    · rintro ⟨⟨t, rfl⟩, ht⟩
      have ht0 : t ≠ (0 : unitInterval) := by
        intro h
        apply ht
        left
        simpa [h] using h0
      have ht1 : t ≠ (1 : unitInterval) := by
        intro h
        apply ht
        right
        simpa [h] using h1
      exact ⟨t, ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
        lt_of_le_of_ne t.property.2 ht1⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      constructor
      · exact mem_range_self t
      · intro h
        rcases h with h | h
        · have heq : t = (0 : unitInterval) := ha.injective (h.trans h0.symm)
          exact (ne_of_gt ht.1) heq
        · have heq : t = (1 : unitInterval) := ha.injective (h.trans h1.symm)
          exact (ne_of_lt ht.2) heq
  rcases cairns_circle_arc_range b hb with h | h
  · left
    rw [← hrel (Circle.path (b 0) (b 1))
      ((Circle.path (b 0) (b 1)).continuous.isClosedEmbedding
        (Circle.path_injective_of_ne hne)).isEmbedding
      (b 0) (b 1) (by simp [Circle.path]) (by simp [Circle.path]), ← h,
      hrel b hb (b 0) (b 1) rfl rfl]
  · right
    calc
      b '' Ioo 0 1 = range b \ {b 0, b 1} :=
        (hrel b hb (b 0) (b 1) rfl rfl).symm
      _ = range (Circle.path (b 1) (b 0)) \ {b 1, b 0} := by
        rw [h, Set.pair_comm]
      _ = Circle.path (b 1) (b 0) '' Ioo 0 1 :=
        hrel (Circle.path (b 1) (b 0))
          ((Circle.path (b 1) (b 0)).continuous.isClosedEmbedding
            (Circle.path_injective_of_ne hne.symm)).isEmbedding
          (b 1) (b 0) (by simp [Circle.path]) (by simp [Circle.path])

/-! If the complement of a transported seam is the closed range of the
opposite directed Circle path, compactness gives the seam's openness. -/
theorem cairns_seam_open_of_complementary_closed_arc
    (s : Set Circle) (u v : Circle) (_huv : u ≠ v)
    (hcomp : sᶜ = range (Circle.path v u)) : IsOpen s := by
  rw [← compl_compl s, hcomp]
  exact (isCompact_range (Circle.path v u).continuous).isClosed.isOpen_compl

/-! Directed circle arcs are open, have the closed path as closure, and have
exactly their two endpoints as frontier.  These are the elementary boundary
facts used by the seam transport. -/
theorem cairns_directed_circle_arc_open_connected
    (u v : Circle) (huv : u ≠ v) :
    IsOpen (Circle.path u v '' Ioo 0 1) ∧
      IsConnected (Circle.path u v '' Ioo 0 1) := by
  constructor
  · apply cairns_seam_open_of_complementary_closed_arc _ u v huv
    rw [← Circle.compl_range_path huv.symm, compl_compl]
  · exact (isConnected_Ioo (show (0 : unitInterval) < 1 by norm_num)).image _
      (Circle.path u v).continuous.continuousOn

theorem cairns_directed_circle_arc_closure
    (u v : Circle) (huv : u ≠ v) :
    closure (Circle.path u v '' Ioo 0 1) = range (Circle.path u v) := by
  let g : unitInterval ≃ₜ range (Circle.path u v) :=
    ((Circle.path u v).continuous.isClosedEmbedding
      (Circle.path_injective_of_ne huv)).toHomeomorph
  have hI : closure (Ioo (0 : unitInterval) 1) = (univ : Set unitInterval) := by
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 by norm_num)]
    ext t
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨t.property.1, t.property.2⟩
  have hsub : closure (g '' Ioo (0 : unitInterval) 1) =
      (univ : Set (range (Circle.path u v))) := by
    rw [← g.image_closure, hI, image_univ]
    exact Set.range_eq_univ.mpr g.surjective
  apply Set.Subset.antisymm
  · apply (closure_mono ?_).trans
        (isCompact_range (Circle.path u v).continuous).isClosed.closure_subset
    rintro z ⟨t, ht, rfl⟩
    exact mem_range_self t
  · intro z hz
    have hz' : (⟨z, hz⟩ : range (Circle.path u v)) ∈
        closure (g '' Ioo (0 : unitInterval) 1) := by
      rw [hsub]
      trivial
    rw [mem_closure_iff_nhds] at hz'
    rw [mem_closure_iff_nhds]
    intro t ht
    have ht' : ((Subtype.val : range (Circle.path u v) → Circle) ⁻¹' t) ∈
        nhds ⟨z, hz⟩ := continuous_subtype_val.continuousAt.preimage_mem_nhds ht
    obtain ⟨w, hw, hwt⟩ := hz' _ ht'
    rcases hwt with ⟨t, ht, heq⟩
    have hmem : (w : Circle) ∈ Circle.path u v '' Ioo 0 1 := by
      refine ⟨t, ht, ?_⟩
      have := congrArg (fun z : range (Circle.path u v) => (z : Circle)) heq
      simpa [g] using this
    refine ⟨(w : Circle), ?_, ?_⟩
    · exact hw
    · exact hmem

theorem cairns_directed_circle_arc_frontier
    (u v : Circle) (huv : u ≠ v) :
    frontier (Circle.path u v '' Ioo 0 1) = {u, v} := by
  rw [(cairns_directed_circle_arc_open_connected u v huv).1.frontier_eq,
      cairns_directed_circle_arc_closure u v huv]
  ext z
  constructor
  · intro hz
    rcases hz.1 with ⟨t, rfl⟩
    by_cases ht0 : t = (0 : unitInterval)
    · left
      simp [ht0, Circle.path]
    by_cases ht1 : t = (1 : unitInterval)
    · right
      simp [ht1, Circle.path]
    exfalso
    apply hz.2
    refine ⟨t, ?_, rfl⟩
    exact ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
      lt_of_le_of_ne t.property.2 ht1⟩
  · intro hz
    constructor
    · rcases hz with hzu | hzv
      · rw [hzu]
        exact ⟨0, by simp [Circle.path]⟩
      · rw [hzv]
        exact ⟨1, by simp [Circle.path]⟩
    · intro hzimg
      rcases hzimg with ⟨t, ht, heq⟩
      rcases hz with hzu | hzv
      · have heq' : Circle.path u v t = Circle.path u v 0 := by
          calc
            Circle.path u v t = z := heq
            _ = u := hzu
            _ = Circle.path u v 0 := by simp [Circle.path]
        have ht0 : t = (0 : unitInterval) :=
          (Circle.path_injective_of_ne huv) heq'
        exact (ne_of_gt ht.1) ht0
      · have heq' : Circle.path u v t = Circle.path u v 1 := by
          calc
            Circle.path u v t = z := heq
            _ = v := hzv
            _ = Circle.path u v 1 := by simp [Circle.path]
        have ht1 : t = (1 : unitInterval) :=
          (Circle.path_injective_of_ne huv) heq'
        exact (ne_of_lt ht.2) ht1

/-! The endpoint and relative-topology obligations follow once the
transported seam interior has been identified with one directed circle arc. -/
theorem cairns_seam_preimage_data_of_directed_arc
    (s : Set Circle) (u v : Circle) (huv : u ≠ v)
    (hsEq : s = Circle.path u v '' Ioo 0 1) :
    IsOpen s ∧ IsConnected s ∧ frontier s = {u, v} := by
  rw [hsEq]
  exact ⟨(cairns_directed_circle_arc_open_connected u v huv).1,
    (cairns_directed_circle_arc_open_connected u v huv).2,
    cairns_directed_circle_arc_frontier u v huv⟩

/-!  The source's phrase “the seam arc” is a relative-open arc statement on
the boundary circle.  Isolating its exact data prevents the later path
classification from silently assuming that an arbitrary proper subset is an
arc. -/
theorem cairns_halfdisk_seam_preimage_data
    (c B : Set ℂ) (p q : ℂ) (e : c ≃ₜ sphere (0 : ℂ) 1)
    (hp : p ∈ c) (hq : q ∈ c) (_hpq : p ≠ q)
    (b : unitInterval → ℂ) (hb : Topology.IsEmbedding b)
    (hrange : range b = B) (h0 : b 0 = p) (h1 : b 1 = q)
    (hproper : B ⊆ c ∧ B ≠ c) :
    let s : Set Circle := {z | (e.symm z : ℂ) ∈ B \ {p, q}}
    IsOpen s ∧ IsConnected s ∧
      frontier s = {e ⟨p, hp⟩, e ⟨q, hq⟩} := by
  /-
  Source: Cairns (1951), §4(D), pp.865--866, and Whyburn II §5, p.28.
  The embedded seam b has compact connected range B, contains p and q, and is
  proper in c.  Transport B by e to the boundary Circle.  Removing the two
  endpoint images leaves the relative interior of a single arc, an open
  connected subset whose frontier is exactly those endpoints.  The omitted
  source step is the elementary interval-image relative-topology argument;
  it is retained as this named prerequisite.
  -/
  dsimp
  have hconn := cairns_halfdisk_seam_preimage_connected c B p q e b hb hrange h0 h1 hproper.1
  let f : unitInterval → Circle := fun t =>
    e ⟨b t, hproper.1 (hrange ▸ mem_range_self t)⟩
  have hf : Continuous f := by
    apply e.continuous.comp
    exact hb.continuous.subtype_mk (fun t ↦ hproper.1 (hrange ▸ mem_range_self t))
  have hset : {z : Circle | (e.symm z : ℂ) ∈ B \ {p, q}} = f '' Ioo 0 1 := by
    ext z
    constructor
    · intro hz
      rw [cairns_embedded_seam_relative_interior B p q b hb hrange h0 h1] at hz
      obtain ⟨t, ht, hbt⟩ := hz
      refine ⟨t, ht, ?_⟩
      change e ⟨b t, _⟩ = z
      rw [← e.apply_symm_apply z]
      exact congrArg e (Subtype.ext hbt)
    · rintro ⟨t, ht, rfl⟩
      change (e.symm (f t) : ℂ) ∈ B \ {p, q}
      rw [Homeomorph.symm_apply_apply]
      rw [cairns_embedded_seam_relative_interior B p q b hb hrange h0 h1]
      exact ⟨t, ht, rfl⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hsub : (⟨b x, hproper.1 (hrange ▸ mem_range_self x)⟩ : c) =
        ⟨b y, hproper.1 (hrange ▸ mem_range_self y)⟩ := e.injective hxy
    exact hb.injective (congrArg Subtype.val hsub)
  have hfemb : Topology.IsEmbedding f := by
    exact (hf.isClosedEmbedding hf_inj).isEmbedding
  have hf01 : f 0 ≠ f 1 := by
    intro h
    have : (0 : unitInterval) = 1 := hf_inj h
    exact (show (0 : unitInterval) ≠ 1 by norm_num) this
  have hf10 : f 1 ≠ f 0 := hf01.symm
  have hf0 : f 0 = e ⟨p, hp⟩ := by
    dsimp [f]
    apply congrArg e
    exact Subtype.ext h0
  have hf1 : f 1 = e ⟨q, hq⟩ := by
    dsimp [f]
    apply congrArg e
    exact Subtype.ext h1
  have harc := cairns_circle_open_arc_range f hfemb
  refine ⟨?_, hconn, ?_⟩
  · rw [hset]
    rcases harc with harc | harc
    · exact (cairns_seam_preimage_data_of_directed_arc _ (f 0) (f 1) hf01 harc).1
    · exact (cairns_seam_preimage_data_of_directed_arc _ (f 1) (f 0) hf10 harc).1
  · rcases harc with harc | harc
    · rw [hset, harc]
      rw [← hf0, ← hf1]
      exact cairns_directed_circle_arc_frontier (f 0) (f 1) hf01
    · rw [hset, harc]
      rw [← hf0, ← hf1]
      calc
        frontier (Circle.path (f 1) (f 0) '' Ioo 0 1) = {f 1, f 0} :=
          cairns_directed_circle_arc_frontier (f 1) (f 0) hf10
        _ = {f 0, f 1} := by
          ext z
          constructor <;> intro hz
          · rcases hz with rfl | rfl <;> simp
          · rcases hz with rfl | rfl <;> simp

theorem cairns_halfdisk_circle_arc_classification
    (s : Set Circle) (u v : Circle)
    (hsOpen : IsOpen s) (hsConnected : IsConnected s)
    (hsFrontier : frontier s = {u, v}) (huv : u ≠ v) :
    s ⊆ Circle.path u v '' Ioo 0 1 ∨
      s ⊆ Circle.path v u '' Ioo 0 1 := by
  exact circle_arc_subset_directed_path s u v hsOpen hsConnected hsFrontier huv

/-! Once the transported relative interior is identified with a directed arc,
the corresponding closed seam range is obtained by adjoining its two endpoint
values.  This isolates the endpoint/range conversion from the circle
classification argument itself. -/
theorem cairns_seam_range_of_open_arc_eq
    (B : Set ℂ) (p q : ℂ) (b : unitInterval → ℂ)
    (hb : Topology.IsEmbedding b) (hrange : range b = B)
    (h0 : b 0 = p) (h1 : b 1 = q)
    (j : Circle → ℂ) (_hj : Topology.IsEmbedding j)
    (hBsub : B ⊆ range j) (ep eq : Circle) (_hep : ep ≠ eq)
    (hjp : j ep = p) (hjq : j eq = q)
    (hinterior : B \ {p, q} = b '' Ioo 0 1)
    (hsEq : {z : Circle | j z ∈ B \ {p, q}} =
      Circle.path ep eq '' Ioo 0 1) :
    range b = range (j ∘ Circle.path ep eq) := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := hx
    by_cases ht0 : t = (0 : unitInterval)
    · refine ⟨0, ?_⟩
      simp [Function.comp, ht0, h0, hjp, Circle.path]
    by_cases ht1 : t = (1 : unitInterval)
    · refine ⟨1, ?_⟩
      simp [Function.comp, ht1, h1, hjq, Circle.path]
    have ht : t ∈ Ioo (0 : unitInterval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
       lt_of_le_of_ne t.property.2 ht1⟩
    have hxt : b t ∈ B \ {p, q} := by
      rw [← hrange]
      exact ⟨mem_range_self t, by
        intro h
        rcases h with h | h
        · apply ht0
          exact hb.injective (h.trans h0.symm)
        · apply ht1
          exact hb.injective (h.trans h1.symm)⟩
    obtain ⟨z, hzj⟩ := hBsub (hrange ▸ mem_range_self t)
    have hzmem : z ∈ {z : Circle | j z ∈ B \ {p, q}} := by
      change j z ∈ B \ {p, q}
      simpa [hzj] using hxt
    rw [hsEq] at hzmem
    obtain ⟨r, hr, hzr⟩ := hzmem
    refine ⟨r, ?_⟩
    calc
      j (Circle.path ep eq r) = j z := congrArg j hzr
      _ = b t := hzj
  · intro hx
    obtain ⟨t, rfl⟩ := hx
    by_cases ht0 : t = (0 : unitInterval)
    · refine ⟨0, ?_⟩
      simp [Function.comp, ht0, h0, hjp, Circle.path]
    by_cases ht1 : t = (1 : unitInterval)
    · refine ⟨1, ?_⟩
      simp [Function.comp, ht1, h1, hjq, Circle.path]
    have ht : t ∈ Ioo (0 : unitInterval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
       lt_of_le_of_ne t.property.2 ht1⟩
    have hzt : j (Circle.path ep eq t) ∈ B \ {p, q} := by
      have : Circle.path ep eq t ∈ {z : Circle |
          j z ∈ B \ {p, q}} := hsEq ▸ ⟨t, ht, rfl⟩
      exact this
    rw [hinterior] at hzt
    obtain ⟨r, hr, hbr⟩ := hzt
    refine ⟨r, ?_⟩
    exact hbr

/-! Reversing a unit-interval parametrization preserves its range.  This is
the orientation bridge used when the seam's classified directed arc runs from
q back to p while the supplied seam runs from p to q. -/
theorem cairns_range_comp_unitInterval_symm
    (b : unitInterval → ℂ) :
    range (b ∘ unitInterval.symm) = range b := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨unitInterval.symm t, by simp [Function.comp]
      ⟩
  · rintro ⟨t, rfl⟩
    exact ⟨unitInterval.symm t, by simp [Function.comp]
      ⟩

/-! Reverse the supplied seam parametrization before applying the endpoint
range lemma.  The reversed parametrization has endpoints q,p and the same
range, while its transported relative interior is unchanged as a set. -/
theorem cairns_seam_range_of_reverse_arc
    (B : Set ℂ) (p q : ℂ) (b : unitInterval → ℂ)
    (hb : Topology.IsEmbedding b) (hrange : range b = B)
    (h0 : b 0 = p) (h1 : b 1 = q)
    (j : Circle → ℂ) (hj : Topology.IsEmbedding j)
    (hBsub : B ⊆ range j) (ep eq : Circle) (hep : ep ≠ eq)
    (hjp : j ep = p) (hjq : j eq = q)
    (hsEq : {z : Circle | j z ∈ B \ {p, q}} =
      Circle.path eq ep '' Ioo 0 1) :
    range b = range (j ∘ Circle.path eq ep) := by
  let br : unitInterval → ℂ := b ∘ unitInterval.symm
  have hbr : Topology.IsEmbedding br := by
    exact hb.comp unitInterval.symmHomeomorph.isEmbedding
  have hbrange : range br = B := by
    rw [cairns_range_comp_unitInterval_symm, hrange]
  have hbr0 : br 0 = q := by simp [br, h1]
  have hbr1 : br 1 = p := by simp [br, h0]
  have hrev := cairns_embedded_seam_relative_interior B q p br hbr hbrange hbr0 hbr1
  have htmp := cairns_seam_range_of_open_arc_eq B q p br hbr hbrange hbr0 hbr1
    j hj hBsub eq ep hep.symm hjq hjp hrev
      (by
        rw [← Set.pair_comm]
        exact hsEq)
  calc
    range b = range br := by rw [hrange, hbrange]
    _ = range (j ∘ Circle.path eq ep) := htmp

/-!  A proper embedded seam with the same endpoint pair occupies exactly one
of the two complementary circle arcs.  This is the elementary arc-classification
step which Cairns uses implicitly when he says “the other arc”. -/
theorem cairns_halfdisk_seam_matches_complementary_arc
    (c B : Set ℂ) (p q : ℂ) (e : c ≃ₜ sphere (0 : ℂ) 1)
    (hpq : p ≠ q) (b : unitInterval → ℂ) (hb : Topology.IsEmbedding b)
    (hrange : range b = B) (h0 : b 0 = p) (h1 : b 1 = q)
    (hproper : B ⊆ c ∧ B ≠ c) :
    ∃ e₂ e₃ : unitInterval → ℂ,
      Topology.IsEmbedding e₂ ∧ Topology.IsEmbedding e₃ ∧
      e₂ 0 = p ∧ e₂ 1 = q ∧ e₃ 0 = q ∧ e₃ 1 = p ∧
      range e₂ ∪ range e₃ = c ∧ range e₂ ∩ range e₃ = {p, q} ∧
      (range b = range e₂ ∨ range b = range e₃) := by
  /-
  Source: Whyburn II §5, p.28 (two arcs meeting at their endpoints), used in
  Cairns §4(D), pp.865--866.  Split the embedded circle at p,q.  The connected
  image B of the embedded interval contains both endpoints and is proper; if
  it met both open complementary arcs, connectedness would force an endpoint
  crossing and injectivity of b would identify a second parameter.  Hence B is
  one whole complementary arc.  The endpoint and range equalities then give
  the displayed disjunction.  The exact connectedness/subtype argument is
  retained as this named prerequisite.
  -/
  have hp : p ∈ c := hproper.1 (by rw [← hrange, ← h0]; exact mem_range_self 0)
  have hq : q ∈ c := hproper.1 (by rw [← hrange, ← h1]; exact mem_range_self 1)
  let s : Set Circle := {z | (e.symm z : ℂ) ∈ B \ {p, q}}
  have hsdata := cairns_halfdisk_seam_preimage_data c B p q e hp hq hpq b hb
    hrange h0 h1 hproper
  have hpq' : e ⟨p, hp⟩ ≠ e ⟨q, hq⟩ := by
    intro h
    apply hpq
    have hh := congrArg (fun z : sphere (0 : ℂ) 1 => (e.symm z : ℂ)) h
    simpa using hh
  have hsclass := cairns_halfdisk_circle_arc_classification s (e ⟨p, hp⟩) (e ⟨q, hq⟩)
    hsdata.1 hsdata.2.1 hsdata.2.2 hpq'
  let ep : Circle := e ⟨p, hp⟩
  let eq : Circle := e ⟨q, hq⟩
  let j : Circle → ℂ := fun z => (e.symm z : ℂ)
  have hj : Topology.IsEmbedding j := by
    apply (e.symm.continuous.subtype_val.isClosedEmbedding ?_).isEmbedding
    intro x y hxy
    apply e.symm.injective
    exact Subtype.ext hxy
  have hjrange : range j = c := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, rfl⟩
      exact (e.symm w).property
    · intro z hz
      refine ⟨e ⟨z, hz⟩, ?_⟩
      simp [j]
  have hjepeq : ep ≠ eq := by
    intro h
    apply hpq
    have hh := congrArg (fun z : sphere (0 : ℂ) 1 => (e.symm z : ℂ)) h
    simpa [ep, eq] using hh
  let e₂ : unitInterval → ℂ := j ∘ Circle.path ep eq
  let e₃ : unitInterval → ℂ := j ∘ Circle.path eq ep
  have he₂ : Topology.IsEmbedding e₂ := by
    exact hj.comp ((Circle.path ep eq).continuous.isClosedEmbedding
      (Circle.path_injective_of_ne hjepeq)).isEmbedding
  have he₃ : Topology.IsEmbedding e₃ := by
    exact hj.comp ((Circle.path eq ep).continuous.isClosedEmbedding
      (Circle.path_injective_of_ne hjepeq.symm)).isEmbedding
  have h0₂ : e₂ 0 = p := by
    change (e.symm (Circle.path ep eq 0) : ℂ) = p
    rw [show Circle.path ep eq 0 = ep by simp [Circle.path], Homeomorph.symm_apply_apply]
  have h1₂ : e₂ 1 = q := by
    change (e.symm (Circle.path ep eq 1) : ℂ) = q
    rw [show Circle.path ep eq 1 = eq by simp [Circle.path], Homeomorph.symm_apply_apply]
  have h0₃ : e₃ 0 = q := by
    change (e.symm (Circle.path eq ep 0) : ℂ) = q
    rw [show Circle.path eq ep 0 = eq by simp [Circle.path], Homeomorph.symm_apply_apply]
  have h1₃ : e₃ 1 = p := by
    change (e.symm (Circle.path eq ep 1) : ℂ) = p
    rw [show Circle.path eq ep 1 = ep by simp [Circle.path], Homeomorph.symm_apply_apply]
  have hcover : range e₂ ∪ range e₃ = c := by
    rw [range_comp, range_comp, ← image_union,
      Circle.range_path_union_range_path hjepeq]
    simpa [j] using hjrange
  have hintersect : range e₂ ∩ range e₃ = {p, q} := by
    rw [range_comp, range_comp, ← image_inter hj.injective,
      Circle.range_path_inter_range_path hjepeq]
    simpa [j, ep, eq] using Set.image_pair j ep eq
  rcases hsclass with hsforward | hsreverse
  · have hsEq : s = Circle.path ep eq '' Ioo 0 1 := by
      exact circle_arc_eq_directed_path s ep eq hsdata.1 hsdata.2.1 hsdata.2.2
        hjepeq hsforward
    have hseam : range b = range e₂ := by
      apply cairns_seam_range_of_open_arc_eq B p q b hb hrange h0 h1 j hj
        (by rw [hjrange]; exact hproper.1) ep eq hjepeq (by simp [j, ep]) (by simp [j, eq])
        (cairns_embedded_seam_relative_interior B p q b hb hrange h0 h1) hsEq
    exact ⟨e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃, hcover, hintersect,
      Or.inl hseam⟩
  · have hsEq : s = Circle.path eq ep '' Ioo 0 1 := by
      exact circle_arc_eq_directed_path s eq ep hsdata.1 hsdata.2.1
        (by
          rw [hsdata.2.2]
          ext z
          change z ∈ {ep, eq} ↔ z ∈ {eq, ep}
          rw [Set.pair_comm])
        hjepeq.symm hsreverse
    have hseam : range b = range e₃ := by
      apply cairns_seam_range_of_reverse_arc B p q b hb hrange h0 h1 j hj
        (by rw [hjrange]; exact hproper.1) ep eq hjepeq (by simp [j, ep]) (by simp [j, eq]) hsEq
    exact ⟨e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃, hcover, hintersect,
      Or.inr hseam⟩

/-!  The remaining source-level step is separated so that the endpoint and
arc-pasting argument can be proved independently of the circle transport. -/
theorem cairns_halfdisk_boundary_arc_pasting
    (upper : Bool) (c B : Set ℂ) (p q : ℂ)
    (e₂ e₃ b : unitInterval → ℂ)
    (he₂ : Topology.IsEmbedding e₂) (he₃ : Topology.IsEmbedding e₃)
    (hb : Topology.IsEmbedding b)
    (h0 : b 0 = p) (h1 : b 1 = q)
    (h0₂ : e₂ 0 = p) (h1₂ : e₂ 1 = q)
    (h0₃ : e₃ 0 = q) (h1₃ : e₃ 1 = p)
    (hcover : range e₂ ∪ range e₃ = c)
    (hintersect : range e₂ ∩ range e₃ = {p, q})
    (hseam : range b = range e₂ ∨ range b = range e₃)
    (hproper : B ⊆ c ∧ B ≠ c) (hrange : range b = B) (hpq : p ≠ q) :
    ∃ H : c ≃ₜ frontier (cairnsClosedHalfDisk upper),
      ∀ t : unitInterval,
        ((H ⟨b t, hproper.1 (hrange ▸ mem_range_self t)⟩ :
          frontier (cairnsClosedHalfDisk upper)) : ℂ) =
          ((2 * (t : ℝ) - 1 : ℝ) : ℂ) := by
  /-
  Source: Cairns (1951), §4(D), pp.865--866.  Map b monotonically onto the
  diameter and map the complementary embedded arc e₂ (or e₃, according to
  `upper`) onto the selected semicircle, with the endpoint equations fixing
  both overlaps.  The two closed arc ranges cover c and meet only at p,q;
  finite closed-set pasting gives a continuous bijection.  The source c is
  compact through its homeomorphism with the circle and the target frontier
  is Hausdorff, so the continuous bijection is a homeomorphism.  Lean's
  remaining obligation is exactly this subtype pasting and its endpoint
  bookkeeping; no separation or extension theorem is hidden here.
  -/
  have hB : range b ⊆ c := by
    intro z hz
    exact hproper.1 (hrange ▸ hz)
  simpa only using cairns_closed_arc_pair_boundary_homeomorph upper c p q e₂ e₃ b
    he₂ he₃ hb h0 h1 h0₂ h1₂ h0₃ h1₃ hcover hintersect hseam hB hpq

/-!
This is the boundary part of Cairns' half-disk construction.  Cairns,
*An Elementary Proof of the Jordan--Schoenflies Theorem* (1951), §4(D),
pp.865--866, cuts the boundary circle at the two seam endpoints and maps the
seam to the diameter and the complementary arc to the selected semicircle.
The printed argument suppresses the subtype and closed-pair bookkeeping.  The
named theorem below isolates exactly that missing boundary correspondence;
its hypotheses retain the literal embedded seam and the properness condition.
-/
theorem cairns_halfdisk_boundary_transport
    (upper : Bool) (c B : Set ℂ) (p q : ℂ)
    (e : c ≃ₜ sphere (0 : ℂ) 1)
    (hpq : p ≠ q)
    (b : unitInterval → ℂ) (hb : Topology.IsEmbedding b)
    (hrange : range b = B) (h0 : b 0 = p) (h1 : b 1 = q)
    (hproper : B ⊆ c ∧ B ≠ c) :
    ∃ H : c ≃ₜ frontier (cairnsClosedHalfDisk upper),
      ∀ t : unitInterval,
        ((H ⟨b t, hproper.1 (hrange ▸ mem_range_self t)⟩ :
          frontier (cairnsClosedHalfDisk upper)) : ℂ) =
          ((2 * (t : ℝ) - 1 : ℝ) : ℂ) := by
  have hp : p ∈ c := hproper.1 (by rw [← hrange, ← h0]; exact mem_range_self 0)
  have hq : q ∈ c := hproper.1 (by rw [← hrange, ← h1]; exact mem_range_self 1)
  obtain ⟨e₂, e₃, he₂, he₃, h0₂, h1₂, h0₃, h1₃, hcover, hintersect, hseam⟩ :=
    cairns_halfdisk_seam_matches_complementary_arc c B p q e hpq b hb hrange h0 h1 hproper
  exact cairns_halfdisk_boundary_arc_pasting upper c B p q e₂ e₃ b he₂ he₃ hb
    h0 h1 h0₂ h1₂ h0₃ h1₃ hcover hintersect hseam hproper hrange hpq

end HolomorphicAnosov.Topology
