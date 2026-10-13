import Mathlib.Topology.LocallyConstant.Basic
import HolomorphicAnosov.Topology.Holonomy.UnitDiskEmbedding
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Geometry.Holonomy.SameBoxCompositionGerm
import HolomorphicAnosov.Topology.OpenCoverPathSubdivision
import HolomorphicAnosov.Geometry.UnstablePlaqueOpenG10
import HolomorphicAnosov.Geometry.StablePlaqueOpenG10
import Mathlib.Topology.Algebra.Module.Basic

/-! Finite plaque chains represent local holonomy along intrinsic leaf paths, and their germs are
independent of the boxes and subdivisions. The file also establishes concatenation and
constant-path laws. (Nisoli, §1.3, Remarks 1.3.2 and 1.3.5, pp.21–23; Hirsch–Pugh–Shub, §7,
p.116; Zhang, Lemma 2.10, p.10) -/

noncomputable section
open scoped ContDiff Manifold _root_.Topology
open Set Filter _root_.Topology
universe u v
namespace HolomorphicAnosov
/-- A product box defines stable transport between its two unstable plaques by preserving the second
coordinate, with the full source plaque as domain. (Ghys, p.594; Nisoli, Remark 1.3.2, pp.21–22) -/
theorem local_plaque_transport_of_box {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (a a' : FoliationCoordinateDisk s)
    (w : FoliationCoordinateDisk t) (x y : M)
    (hx : ((F.box b).chart (a,w)).val = x)
    (hy : ((F.box b).chart (a',w)).val = y) :
    ∃ e : LocalPlaqueTransport F x y,
      e.box = b ∧ e.first = a ∧ e.second = a' ∧ e.transverse = w ∧
      e.map.source = {z | ∃ v : FoliationCoordinateDisk t,
        ((F.box b).chart (a, v)).val = z.val} := by
  classical
  have hqx : F.unstableLabel b a = Quotient.mk F.unstablePartition x :=
    (F.unstable_label b a w).symm.trans (congrArg (Quotient.mk F.unstablePartition) hx)
  have hqy : F.unstableLabel b a' = Quotient.mk F.unstablePartition y :=
    (F.unstable_label b a' w).symm.trans (congrArg (Quotient.mk F.unstablePartition) hy)
  let jx : FoliationCoordinateDisk t → F.ULeaf x := fun v ↦
    ⟨((F.box b).chart (a,v)).val, (F.unstable_label b a v).trans hqx⟩
  let jy : FoliationCoordinateDisk t → F.ULeaf y := fun v ↦
    ⟨((F.box b).chart (a',v)).val, (F.unstable_label b a' v).trans hqy⟩
  have hox : IsOpenEmbedding jx := unstable_plaque_open_at_class_g10 F b a _ hqx
  have hoy : IsOpenEmbedding jy := unstable_plaque_open_at_class_g10 F b a' _ hqy
  have : Nonempty (FoliationCoordinateDisk t) := ⟨w⟩
  let ex := hox.toOpenPartialHomeomorph jx
  let ey := hoy.toOpenPartialHomeomorph jy
  have hxw : jx w = F.uPoint x := Subtype.ext hx
  have hyw : jy w = F.uPoint y := Subtype.ext hy
  have hinvx : ex.symm (F.uPoint x) = w := by
    rw [← hxw]
    exact hox.toOpenPartialHomeomorph_left_inv jx
  have hsrc : F.uPoint x ∈ (ex.symm.trans ey).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · change F.uPoint x ∈ ex.target
      simp only [ex, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
      exact ⟨w, hxw⟩
    · simp [ey]
  have hpt : (ex.symm.trans ey) (F.uPoint x) = F.uPoint y := by
    simp only [OpenPartialHomeomorph.trans_apply, hinvx]
    simpa only [ey, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply] using hyw
  refine ⟨{
    map := ex.symm.trans ey
    source_point := hsrc
    map_point := hpt
    box := b
    first := a
    second := a'
    transverse := w
    first_point := hx
    second_point := hy
    source_in_plaque := ?_
    coordinate_map := ?_ }, rfl, rfl, rfl, rfl, ?_⟩
  · intro z hz
    have hzrange : z ∈ Set.range jx := by
      have hh := (show z ∈ ex.symm.source ∩ ex.symm ⁻¹' ey.source from
        (OpenPartialHomeomorph.trans_source ex.symm ey) ▸ hz).1
      simpa only [OpenPartialHomeomorph.symm_source, ex,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hh
    obtain ⟨v,hv⟩ := hzrange
    exact ⟨v, congrArg Subtype.val hv⟩
  · intro z v hz hv
    have hval : jx v = z := Subtype.ext hv
    have hinv : ex.symm z = v := by
      rw [← hval]
      exact hox.toOpenPartialHomeomorph_left_inv jx
    simp only [OpenPartialHomeomorph.trans_apply, hinv, ey,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    rfl

  · change (ex.symm.trans ey).source = _
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      ey, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ,
      ex, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    ext z
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v, congrArg Subtype.val hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, Subtype.ext hv⟩


/-- Two finite path representatives compose on their open overlap to represent the concatenated
subinterval. (Nisoli, Remark 1.3.5, p.23; Zhang, p.10) -/
theorem compose_path_representatives {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c)
    (e : PathHolonomyRepresentative F γ a b)
    (e' : PathHolonomyRepresentative F γ b c) :
    ∃ r : PathHolonomyRepresentative F γ a c, r.map = e.map.trans e'.map := by
  refine ⟨{
    map := e.map.trans e'.map
    source_point := ?_
    map_point := ?_
    chain := PlaqueChainAlong.compose hab hbc e.chain e'.chain}, rfl⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨e.source_point, by simpa only [Set.mem_preimage, e.map_point] using e'.source_point⟩
  · rw [OpenPartialHomeomorph.trans_apply, e.map_point, e'.map_point]


/-- A path segment contained in a single stable plaque has a one-step holonomy representative.
(Nisoli, Remark 1.3.2, pp.21–22; Zhang, Lemma 2.10, p.10) -/
theorem single_path_representative {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (hab : a ≤ b)
    (i : F.boxIndex) (w : FoliationCoordinateDisk t)
    (hseg : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box i).chart (z,w)).val = (γ r).val) :
    Nonempty (PathHolonomyRepresentative F γ a b) := by
  obtain ⟨za,hza⟩ := hseg a le_rfl hab
  obtain ⟨zb,hzb⟩ := hseg b hab le_rfl
  obtain ⟨e,hbox,hfirst,hsecond,htrans,_⟩ :=
    local_plaque_transport_of_box F i za zb w (γ a).val (γ b).val hza hzb
  refine ⟨{
    toPointedLeafHomeomorph := e.toPointedLeafHomeomorph
    chain := PlaqueChainAlong.single a b hab e ?_}⟩
  intro r har hrb
  obtain ⟨z,hz⟩ := hseg r har hrb
  refine ⟨z, ?_⟩
  have heq := congrArg (fun j ↦ ((F.box j).chart (z,w)).val) hbox
  simpa only [htrans] using heq.trans hz


/-- A finite normalized sequence of single-plaque path segments has a finite holonomy
representative. (Nisoli, p.23; Hatcher, Lemma 1.15, p.35) -/
theorem path_representative_of_finite_segments {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a : ℕ → unitInterval) (ha : Monotone a) (n : ℕ) (hn : 0 < n)
    (hseg : ∀ j < n, Nonempty (PathHolonomyRepresentative F γ (a j) (a (j+1)))) :
    Nonempty (PathHolonomyRepresentative F γ (a 0) (a n)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hzero : n = 0
    · subst n
      exact hseg 0 (by omega)
    · have hn' : 0 < n := Nat.pos_of_ne_zero hzero
      obtain ⟨left⟩ := ih hn' (fun j hj ↦ hseg j (by omega))
      obtain ⟨right⟩ := hseg n (Nat.lt_succ_self n)
      obtain ⟨e,he⟩ := compose_path_representatives F γ (a 0) (a n) (a (n+1))
        (ha (Nat.zero_le n)) (ha (Nat.le_succ n)) left right
      exact ⟨e⟩


/-- Every intrinsic stable-leaf path has a finite plaque-chain holonomy representative. (Nisoli,
Remark 1.3.5, p.23; Hatcher, Lemma 1.15, p.35) -/
theorem path_holonomy_representative_exists {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) :
    Nonempty (PathHolonomyRepresentative F γ 0 1) := by
  classical
  let J := {bw : F.boxIndex × FoliationCoordinateDisk t // F.stableLabel bw.1 bw.2 = q}
  let j : J → FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition q :=
    fun bw z ↦ ⟨((F.box bw.val.1).chart (z,bw.val.2)).val,
      (F.stable_label bw.val.1 z bw.val.2).trans bw.prop⟩
  have hj : ∀ bw : J, IsOpenEmbedding (j bw) := fun bw ↦
    stable_plaque_open_at_class_g10 F bw.val.1 bw.val.2 q bw.prop
  have hcover : ∀ r : unitInterval, ∃ bw : J, γ r ∈ Set.range (j bw) := by
    intro r
    obtain ⟨b,hb⟩ := F.cover (γ r).val
    let zw := (F.box b).chart.symm ⟨(γ r).val,hb⟩
    have hv : ((F.box b).chart zw).val = (γ r).val :=
      congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨(γ r).val,hb⟩)
    have hq : F.stableLabel b zw.2 = q :=
      (F.stable_label b zw.1 zw.2).symm.trans
        ((congrArg (Quotient.mk F.stablePartition) hv).trans (γ r).prop)
    exact ⟨⟨(b,zw.2),hq⟩,zw.1,Subtype.ext hv⟩
  obtain ⟨n,hn,ts,ht0,htn,htmono,assigned,hsub⟩ :=
    exists_openCover_pathSubdivision γ (fun bw : J ↦ Set.range (j bw))
      (fun bw ↦ (hj bw).isOpen_range) hcover
  let a : ℕ → unitInterval := fun k ↦ ts ⟨min k n,by omega⟩
  have ha : Monotone a := by
    intro k l hkl
    apply htmono
    change min k n ≤ min l n
    omega
  have hsegments : ∀ k < n,
      Nonempty (PathHolonomyRepresentative F γ (a k) (a (k+1))) := by
    intro k hk
    let kk : Fin n := ⟨k,hk⟩
    have hleft : a k = ts kk.castSucc := by
      apply congrArg ts
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt hk)
    have hright : a (k+1) = ts kk.succ := by
      apply congrArg ts
      apply Fin.ext
      exact min_eq_left (Nat.succ_le_of_lt hk)
    rw [hleft,hright]
    apply single_path_representative F γ _ _ (htmono (Fin.castSucc_le_succ kk))
      (assigned kk).val.1 (assigned kk).val.2
    intro r hl hr
    have hh : γ r ∈ Set.range (γ.subpath (ts kk.castSucc) (ts kk.succ)) := by
      rw [γ.range_subpath_of_le _ _ (htmono (Fin.castSucc_le_succ kk))]
      exact ⟨r,⟨hl,hr⟩,rfl⟩
    obtain ⟨z,hz⟩ := hsub kk hh
    exact ⟨z,congrArg Subtype.val hz⟩
  obtain ⟨e⟩ := path_representative_of_finite_segments F γ a ha n hn hsegments
  have ha0 : a 0 = 0 := by
    have hh : (⟨min 0 n,by omega⟩ : Fin (n+1)) = 0 := Fin.ext (Nat.zero_min n)
    exact (congrArg ts hh).trans ht0
  have han : a n = 1 := by
    have hh : (⟨min n n,by omega⟩ : Fin (n+1)) = Fin.last n := Fin.ext (min_self n)
    exact (congrArg ts hh).trans htn
  simpa only [ha0,han] using (show Nonempty (PathHolonomyRepresentative F γ (a 0) (a n)) from ⟨e⟩)


/-- Every ordered closed subinterval of an intrinsic stable-leaf path has a finite holonomy
representative, including degenerate subintervals. (Hatcher, Lemma 1.15, p.35; Nisoli, Remark
1.3.5, p.23) -/
theorem path_holonomy_subinterval_representative_exists {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (hab : a ≤ b) :
    Nonempty (PathHolonomyRepresentative F γ a b) := by
  classical
  let J := {bw : F.boxIndex × FoliationCoordinateDisk t // F.stableLabel bw.1 bw.2 = q}
  let j : J → FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition q :=
    fun bw z ↦ ⟨((F.box bw.val.1).chart (z,bw.val.2)).val,
      (F.stable_label bw.val.1 z bw.val.2).trans bw.prop⟩
  have hj : ∀ bw : J, IsOpenEmbedding (j bw) := fun bw ↦
    stable_plaque_open_at_class_g10 F bw.val.1 bw.val.2 q bw.prop
  have hcover : ∀ r : unitInterval, ∃ bw : J, γ r ∈ Set.range (j bw) := by
    intro r
    obtain ⟨b,hb⟩ := F.cover (γ r).val
    let zw := (F.box b).chart.symm ⟨(γ r).val,hb⟩
    have hv : ((F.box b).chart zw).val = (γ r).val :=
      congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨(γ r).val,hb⟩)
    have hq : F.stableLabel b zw.2 = q :=
      (F.stable_label b zw.1 zw.2).symm.trans
        ((congrArg (Quotient.mk F.stablePartition) hv).trans (γ r).prop)
    exact ⟨⟨(b,zw.2),hq⟩,zw.1,Subtype.ext hv⟩
  let D := Set.Icc (a : ℝ) (b : ℝ)
  let r : D → unitInterval := fun z ↦ ⟨z.val,
    ⟨a.prop.1.trans z.prop.1,z.prop.2.trans b.prop.2⟩⟩
  have hr : Continuous r := continuous_subtype_val.subtype_mk _
  let c : J → Set D := fun bw ↦ (γ ∘ r) ⁻¹' Set.range (j bw)
  have hc : ∀ bw, IsOpen (c bw) := fun bw ↦
    (hj bw).isOpen_range.preimage (γ.continuous.comp hr)
  have hcov : Set.univ ⊆ ⋃ bw, c bw := by
    intro z hz
    obtain ⟨bw,hbw⟩ := hcover (r z)
    exact Set.mem_iUnion.mpr ⟨bw,hbw⟩
  obtain ⟨seq,hseq0,hseqmono,⟨n,hseqend⟩,hseqsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc (show (a : ℝ) ≤ b from hab) hc hcov
  let times : ℕ → unitInterval := r ∘ seq
  have htmono : Monotone times := by
    intro k l hkl
    exact hseqmono hkl
  have hsegments : ∀ k < n+1,
      Nonempty (PathHolonomyRepresentative F γ (times k) (times (k+1))) := by
    intro k hk
    obtain ⟨bw,hbw⟩ := hseqsub k
    apply single_path_representative F γ _ _ (htmono (Nat.le_succ k)) bw.val.1 bw.val.2
    intro v hl hv
    let z : D := ⟨v.val,⟨(seq k).prop.1.trans hl, hv.trans (seq (k+1)).prop.2⟩⟩
    have hz : z ∈ Set.Icc (seq k) (seq (k+1)) := ⟨hl,hv⟩
    obtain ⟨w,hw⟩ := hbw hz
    exact ⟨w,congrArg Subtype.val hw⟩
  obtain ⟨e⟩ := path_representative_of_finite_segments F γ times htmono (n+1)
    (Nat.succ_pos n) hsegments
  have ht0 : times 0 = a := Subtype.ext hseq0
  have htend : times (n+1) = b := Subtype.ext (hseqend (n+1) (Nat.le_succ n))
  simpa only [ht0,htend] using
    (show Nonempty (PathHolonomyRepresentative F γ (times 0) (times (n+1))) from ⟨e⟩)


/-- The second box coordinate is locally constant on a continuous map into an intrinsic stable leaf
whose image lies in the box. (Hirsch–Pugh–Shub, §7, p.116; Nisoli, Remark 1.3.2, pp.21–22) -/
theorem stable_box_transverse_locally_constant {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (q : Quotient F.stablePartition)
    {X : Type*} [TopologicalSpace X]
    (h : X → IntrinsicFoliationLeaf F.stablePartition q) (hc : @Continuous X (IntrinsicFoliationLeaf F.stablePartition q)
      _ (F.stableTopology q) h)
    (hin : ∀ x, (h x).val ∈ (F.box b).image) :
    IsLocallyConstant (fun x ↦ ((F.box b).chart.symm ⟨(h x).val,hin x⟩).2) := by
  classical
  let := F.stableTopology q
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let zw := (F.box b).chart.symm ⟨(h x).val,hin x⟩
  have hpoint : ((F.box b).chart zw).val = (h x).val :=
    congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨(h x).val,hin x⟩)
  have hlabel : F.stableLabel b zw.2 = q :=
    (F.stable_label b zw.1 zw.2).symm.trans
      ((congrArg (Quotient.mk F.stablePartition) hpoint).trans (h x).prop)
  let j : FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition q :=
    fun z ↦ ⟨((F.box b).chart (z,zw.2)).val,(F.stable_label b z zw.2).trans hlabel⟩
  have hj : IsOpenEmbedding j := stable_plaque_open_at_class_g10 F b zw.2 q hlabel
  have hx : h x ∈ Set.range j := ⟨zw.1,Subtype.ext hpoint⟩
  have hn : h ⁻¹' Set.range j ∈ 𝓝 x :=
    (hj.isOpen_range.preimage hc).mem_nhds hx
  filter_upwards [hn] with y hy
  obtain ⟨z,hz⟩ := hy
  have heq : (F.box b).chart (z,zw.2) = ⟨(h y).val,hin y⟩ :=
    Subtype.ext (congrArg (fun u : IntrinsicFoliationLeaf F.stablePartition q ↦ u.val) hz)
  have hv : (F.box b).chart.symm ⟨(h y).val,hin y⟩ = (z,zw.2) := by
    rw [← heq,(F.box b).chart.symm_apply_apply]
  simpa only [zw] using congrArg (fun p : FoliationCoordinateDisk s × FoliationCoordinateDisk t ↦ p.2) hv


/-- The first box coordinate is locally constant on a continuous map into an intrinsic unstable leaf
whose image lies in the box. (Hirsch–Pugh–Shub, p.116; Nisoli, pp.21–22) -/
theorem unstable_box_first_locally_constant {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (b : F.boxIndex) (q : Quotient F.unstablePartition)
    {X : Type*} [TopologicalSpace X]
    (h : X → IntrinsicFoliationLeaf F.unstablePartition q) (hc : @Continuous X (IntrinsicFoliationLeaf F.unstablePartition q)
      _ (F.unstableTopology q) h)
    (hin : ∀ x, (h x).val ∈ (F.box b).image) :
    IsLocallyConstant (fun x ↦ ((F.box b).chart.symm ⟨(h x).val,hin x⟩).1) := by
  classical
  let := F.unstableTopology q
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let zw := (F.box b).chart.symm ⟨(h x).val,hin x⟩
  have hpoint : ((F.box b).chart zw).val = (h x).val :=
    congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨(h x).val,hin x⟩)
  have hlabel : F.unstableLabel b zw.1 = q :=
    (F.unstable_label b zw.1 zw.2).symm.trans
      ((congrArg (Quotient.mk F.unstablePartition) hpoint).trans (h x).prop)
  let j : FoliationCoordinateDisk t → IntrinsicFoliationLeaf F.unstablePartition q :=
    fun z ↦ ⟨((F.box b).chart (zw.1,z)).val,(F.unstable_label b zw.1 z).trans hlabel⟩
  have hj : IsOpenEmbedding j := unstable_plaque_open_at_class_g10 F b zw.1 q hlabel
  have hx : h x ∈ Set.range j := ⟨zw.2,Subtype.ext hpoint⟩
  have hn : h ⁻¹' Set.range j ∈ 𝓝 x :=
    (hj.isOpen_range.preimage hc).mem_nhds hx
  filter_upwards [hn] with y hy
  obtain ⟨z,hz⟩ := hy
  have heq : (F.box b).chart (zw.1,z) = ⟨(h y).val,hin y⟩ :=
    Subtype.ext (congrArg (fun u : IntrinsicFoliationLeaf F.unstablePartition q ↦ u.val) hz)
  have hv : (F.box b).chart.symm ⟨(h y).val,hin y⟩ = (zw.1,z) := by
    rw [← heq,(F.box b).chart.symm_apply_apply]
  simpa only [zw] using congrArg (fun p : FoliationCoordinateDisk s × FoliationCoordinateDisk t ↦ p.1) hv


/-- A preconnected stable strip contained in a receiving box has a constant receiving transverse
coordinate. (Nisoli, Remark 1.3.2, pp.21–22) -/
theorem connected_box_strip_transverse_eq {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (i b : F.boxIndex) (w : FoliationCoordinateDisk t)
    (K : Set (FoliationCoordinateDisk s)) (hK : IsPreconnected K)
    (hin : ∀ z ∈ K, ((F.box i).chart (z,w)).val ∈ (F.box b).image)
    (a a' : FoliationCoordinateDisk s) (ha : a ∈ K) (ha' : a' ∈ K) :
    ((F.box b).chart.symm ⟨((F.box i).chart (a,w)).val,hin a ha⟩).2 =
      ((F.box b).chart.symm ⟨((F.box i).chart (a',w)).val,hin a' ha'⟩).2 := by
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  let q := F.stableLabel i w
  let := F.stableTopology q
  let h : K → IntrinsicFoliationLeaf F.stablePartition q := fun z ↦
    ⟨((F.box i).chart (z.val,w)).val,F.stable_label i z.val w⟩
  have hc : Continuous h := (F.stable_plaque i w).continuous.comp continuous_subtype_val
  have hlc := stable_box_transverse_locally_constant F b q h hc (fun z ↦ hin z.val z.prop)
  exact hlc.apply_eq_of_preconnectedSpace ⟨a,ha⟩ ⟨a',ha'⟩


/-- A compact source strip contained in a receiving box remains in that box for all transverse
coordinates in some neighborhood of its given coordinate. (Nisoli, Remark 1.3.5, p.23) -/
theorem compact_box_strip_tube {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M) (i b : F.boxIndex)
    (w : FoliationCoordinateDisk t) (K : Set (FoliationCoordinateDisk s))
    (hK : IsCompact K)
    (hin : ∀ z ∈ K, ((F.box i).chart (z,w)).val ∈ (F.box b).image) :
    ∀ᶠ v in 𝓝 w, ∀ z ∈ K, ((F.box i).chart (z,v)).val ∈ (F.box b).image := by
  apply hK.eventually_forall_of_forall_eventually
  intro z hz
  have hc : Continuous (fun p : FoliationCoordinateDisk t × FoliationCoordinateDisk s ↦
      ((F.box i).chart (p.2,p.1)).val) :=
    continuous_subtype_val.comp ((F.box i).chart.continuous.comp
      (continuous_snd.prodMk continuous_fst))
  exact hc.continuousAt.eventually ((F.box b).isOpen_image.mem_nhds (hin z hz))


/-- Plaque transports in two boxes have the same germ when a compact connected source strip joining
their endpoints lies in the receiving box. (Nisoli, Remark 1.3.5, p.23) -/
theorem changed_box_plaque_germ_of_strip {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M) {x y : M}
    (e e' : LocalPlaqueTransport F x y)
    (K : Set (FoliationCoordinateDisk s)) (hK : IsCompact K) (hcK : IsPreconnected K)
    (ha : e.first ∈ K) (hb : e.second ∈ K)
    (hin : ∀ z ∈ K, ((F.box e.box).chart (z,e.transverse)).val ∈ (F.box e'.box).image) :
    (Filter.Germ.ofFun e.map : Filter.Germ (𝓝 (F.uPoint x)) (F.ULeaf y)) =
      Filter.Germ.ofFun e'.map := by
  classical
  have : Nonempty (FoliationCoordinateDisk t) := ⟨e.transverse⟩
  have hqx : F.unstableLabel e.box e.first = Quotient.mk F.unstablePartition x :=
    (F.unstable_label e.box e.first e.transverse).symm.trans
      (congrArg (Quotient.mk F.unstablePartition) e.first_point)
  have hqy : F.unstableLabel e'.box e'.second = Quotient.mk F.unstablePartition y :=
    (F.unstable_label e'.box e'.second e'.transverse).symm.trans
      (congrArg (Quotient.mk F.unstablePartition) e'.second_point)
  let jx : FoliationCoordinateDisk t → F.ULeaf x := fun v ↦
    ⟨((F.box e.box).chart (e.first,v)).val,(F.unstable_label e.box e.first v).trans hqx⟩
  let jy : FoliationCoordinateDisk t → F.ULeaf y := fun v ↦
    ⟨((F.box e'.box).chart (e'.second,v)).val,(F.unstable_label e'.box e'.second v).trans hqy⟩
  have hox : IsOpenEmbedding jx := unstable_plaque_open_at_class_g10 F _ _ _ hqx
  have hoy : IsOpenEmbedding jy := unstable_plaque_open_at_class_g10 F _ _ _ hqy
  let ex := hox.toOpenPartialHomeomorph jx
  have hxw : jx e.transverse = F.uPoint x := Subtype.ext e.first_point
  have hyw : jy e'.transverse = F.uPoint y := Subtype.ext e'.second_point
  have hxsrc : F.uPoint x ∈ ex.target := by
    simp only [ex, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨e.transverse,hxw⟩
  have hxinv : ex.symm (F.uPoint x) = e.transverse := by
    rw [← hxw]
    exact hox.toOpenPartialHomeomorph_left_inv jx
  have htube := compact_box_strip_tube F e.box e'.box e.transverse K hK hin
  have hvnear : ∀ᶠ z in 𝓝 (F.uPoint x), ∀ a ∈ K,
      ((F.box e.box).chart (a,ex.symm z)).val ∈ (F.box e'.box).image := by
    have htend := (ex.symm.continuousAt hxsrc).tendsto
    rw [hxinv] at htend
    exact htend.eventually htube
  have hyrange : Set.range jy ∈ 𝓝 (F.uPoint y) := hoy.isOpen_range.mem_nhds ⟨e'.transverse,hyw⟩
  have htarget : ∀ᶠ z in 𝓝 (F.uPoint x), e.map z ∈ Set.range jy := by
    have htend := (e.map.continuousAt e.source_point).tendsto
    rw [e.map_point] at htend
    exact htend.eventually hyrange
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hvnear,htarget,e.map.open_source.mem_nhds e.source_point,
    e'.map.open_source.mem_nhds e'.source_point] with z hz ht hze hze'
  obtain ⟨v,hv⟩ := e.source_in_plaque z hze
  have hjv : jx v = z := Subtype.ext hv
  have hinv : ex.symm z = v := by
    rw [← hjv]
    exact hox.toOpenPartialHomeomorph_left_inv jx
  have hstrip : ∀ a ∈ K, ((F.box e.box).chart (a,v)).val ∈ (F.box e'.box).image := by
    simpa only [hinv] using hz
  have hcoords := connected_box_strip_transverse_eq F e.box e'.box v K hcK
    hstrip e.first e.second ha hb
  obtain ⟨v',hv'⟩ := e'.source_in_plaque z hze'
  obtain ⟨vout,hout⟩ := ht
  have hev : (e.map z).val = ((F.box e.box).chart (e.second,v)).val :=
    e.coordinate_map z v hze hv
  have hyout : ((F.box e'.box).chart (e'.second,vout)).val = (e.map z).val :=
    congrArg Subtype.val hout
  have hinput : (F.box e'.box).chart.symm
      ⟨((F.box e.box).chart (e.first,v)).val,hstrip e.first ha⟩ = (e'.first,v') := by
    apply (F.box e'.box).chart.injective
    rw [(F.box e'.box).chart.apply_symm_apply]
    exact Subtype.ext (hv.trans hv'.symm)
  have houtput : (F.box e'.box).chart.symm
      ⟨((F.box e.box).chart (e.second,v)).val,hstrip e.second hb⟩ = (e'.second,vout) := by
    apply (F.box e'.box).chart.injective
    rw [(F.box e'.box).chart.apply_symm_apply]
    exact Subtype.ext (hev.symm.trans hyout.symm)
  have hvout : vout = v' := by
    rw [hinput,houtput] at hcoords
    exact hcoords.symm
  apply Subtype.ext
  rw [e'.coordinate_map z v' hze' hv',← hyout,hvout]


/-- Single-step representatives of the same subpath have the same germ, even when they use different
boxes. (Nisoli, Remark 1.3.5, p.23) -/
theorem same_subpath_single_plaque_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b : unitInterval) (hab : a ≤ b)
    (e e' : LocalPlaqueTransport F (γ a).val (γ b).val)
    (hs : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box e.box).chart (z,e.transverse)).val = (γ r).val)
    (hs' : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box e'.box).chart (z,e'.transverse)).val = (γ r).val) :
    (Filter.Germ.ofFun e.map : Filter.Germ (𝓝 (F.uPoint (γ a).val)) (F.ULeaf (γ b).val)) =
      Filter.Germ.ofFun e'.map := by
  classical
  let D := Set.Icc a b
  let : CompactSpace D := isCompact_iff_compactSpace.mp isCompact_Icc
  let : PreconnectedSpace D := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hin (r : D) : (γ r.val).val ∈ (F.box e.box).image := by
    obtain ⟨z,hz⟩ := hs r.val r.prop.1 r.prop.2
    rw [← hz]
    exact ((F.box e.box).chart (z,e.transverse)).prop
  let p : D → FoliationCoordinateDisk s := fun r ↦
    ((F.box e.box).chart.symm ⟨(γ r.val).val,hin r⟩).1
  have hc : Continuous p := continuous_fst.comp ((F.box e.box).chart.symm.continuous.comp
    (((F.stable_inclusion q).comp (γ.continuous.comp continuous_subtype_val)).subtype_mk hin))
  have hp (r : D) : ((F.box e.box).chart (p r,e.transverse)).val = (γ r.val).val := by
    obtain ⟨z,hz⟩ := hs r.val r.prop.1 r.prop.2
    have hpair : (F.box e.box).chart.symm ⟨(γ r.val).val,hin r⟩ = (z,e.transverse) := by
      apply (F.box e.box).chart.injective
      rw [(F.box e.box).chart.apply_symm_apply]
      exact Subtype.ext hz.symm
    have hz' : p r = z := congrArg Prod.fst hpair
    rw [hz']
    exact hz
  have ha : e.first ∈ Set.range p := by
    refine ⟨⟨a,le_rfl,hab⟩,?_⟩
    have h := hp ⟨a,le_rfl,hab⟩
    have he : (F.box e.box).chart (p ⟨a,le_rfl,hab⟩,e.transverse) =
        (F.box e.box).chart (e.first,e.transverse) := Subtype.ext (h.trans e.first_point.symm)
    exact congrArg Prod.fst ((F.box e.box).chart.injective he)
  have hb : e.second ∈ Set.range p := by
    refine ⟨⟨b,hab,le_rfl⟩,?_⟩
    have h := hp ⟨b,hab,le_rfl⟩
    have he : (F.box e.box).chart (p ⟨b,hab,le_rfl⟩,e.transverse) =
        (F.box e.box).chart (e.second,e.transverse) := Subtype.ext (h.trans e.second_point.symm)
    exact congrArg Prod.fst ((F.box e.box).chart.injective he)
  apply changed_box_plaque_germ_of_strip F e e' (Set.range p)
    (isCompact_range hc) (isPreconnected_range hc) ha hb
  rintro z ⟨r,rfl⟩
  obtain ⟨z',hz'⟩ := hs' r.val r.prop.1 r.prop.2
  rw [hp r,← hz']
  exact ((F.box e'.box).chart (z',e'.transverse)).prop




/-- A finite plaque-chain map sends its initial marked point to its terminal marked point on its
open domain. (Nisoli, p.23) -/
theorem plaque_chain_pointed {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {a b : unitInterval}
    {e : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)}
    (h : PlaqueChainAlong F γ a b e) :
    F.uPoint (γ a).val ∈ e.source ∧ e (F.uPoint (γ a).val) = F.uPoint (γ b).val := by
  induction h with
  | single a b hab e hs => exact ⟨e.source_point,e.map_point⟩
  | compose hab hbc left right ihl ihr =>
    constructor
    · rw [OpenPartialHomeomorph.trans_source]
      exact ⟨ihl.1,by simpa only [Set.mem_preimage,ihl.2] using ihr.1⟩
    · rw [OpenPartialHomeomorph.trans_apply,ihl.2,ihr.2]


/-- Germ equalities of pointed continuous maps compose through their common intermediate intrinsic
leaf. (Nisoli, Eq. (1.11), pp.22–23) -/
theorem pointed_composition_germ_congr {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f f' : X → Y) (g g' : Y → Z) (ht : Tendsto f (𝓝 x) (𝓝 y))
    (hf : (Filter.Germ.ofFun f : Filter.Germ (𝓝 x) Y) = Filter.Germ.ofFun f')
    (hg : (Filter.Germ.ofFun g : Filter.Germ (𝓝 y) Z) = Filter.Germ.ofFun g') :
    (Filter.Germ.ofFun (g ∘ f) : Filter.Germ (𝓝 x) Z) = Filter.Germ.ofFun (g' ∘ f') := by
  apply Filter.Germ.coe_eq.mpr
  have he := (Filter.Germ.coe_eq.mp hg).comp_tendsto ht
  filter_upwards [he,Filter.Germ.coe_eq.mp hf] with u hgu hfu
  exact hgu.trans (congrArg g' hfu)


/-- A finite plaque chain along a subpath contained in one plaque has the germ of that plaque
correspondence. (Nisoli, Remark 1.3.5 and Eq. (1.11), p.23) -/
theorem plaque_chain_germ_in_one_plaque {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {a b : unitInterval}
    {e : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)}
    (h : PlaqueChainAlong F γ a b e) :
    ∀ r : LocalPlaqueTransport F (γ a).val (γ b).val,
      (∀ v : unitInterval, a ≤ v → v ≤ b →
        ∃ z : FoliationCoordinateDisk s, ((F.box r.box).chart (z,r.transverse)).val = (γ v).val) →
      (Filter.Germ.ofFun e : Filter.Germ (𝓝 (F.uPoint (γ a).val)) (F.ULeaf (γ b).val)) =
        Filter.Germ.ofFun r.map := by
  induction h with
  | single a b hab l hseg =>
    intro r hr
    exact same_subpath_single_plaque_germ F γ a b hab l r hseg hr
  | @compose a b c el er hab hbc left right ihl ihr =>
    intro r hr
    obtain ⟨zm,hzm⟩ := hr b hab hbc
    obtain ⟨rl,hlb,hlf,hls,hlt,_⟩ := local_plaque_transport_of_box F r.box r.first zm
      r.transverse (γ a).val (γ b).val r.first_point hzm
    obtain ⟨rr,hrb,hrf,hrs,hrt,_⟩ := local_plaque_transport_of_box F r.box zm r.second
      r.transverse (γ b).val (γ c).val hzm r.second_point
    have hleft : ∀ v : unitInterval, a ≤ v → v ≤ b →
        ∃ z : FoliationCoordinateDisk s, ((F.box rl.box).chart (z,rl.transverse)).val = (γ v).val := by
      intro v hav hvb
      obtain ⟨z,hz⟩ := hr v hav (hvb.trans hbc)
      refine ⟨z,?_⟩
      have heq := congrArg (fun i ↦ ((F.box i).chart (z,r.transverse)).val) hlb
      simpa only [hlt] using heq.trans hz
    have hright : ∀ v : unitInterval, b ≤ v → v ≤ c →
        ∃ z : FoliationCoordinateDisk s, ((F.box rr.box).chart (z,rr.transverse)).val = (γ v).val := by
      intro v hbv hvc
      obtain ⟨z,hz⟩ := hr v (hab.trans hbv) hvc
      refine ⟨z,?_⟩
      have heq := congrArg (fun i ↦ ((F.box i).chart (z,r.transverse)).val) hrb
      simpa only [hrt] using heq.trans hz
    have hl := ihl rl hleft
    have hh := ihr rr hright
    have hpoint := plaque_chain_pointed F γ left
    have ht : Tendsto el (𝓝 (F.uPoint (γ a).val)) (𝓝 (F.uPoint (γ b).val)) := by
      simpa only [hpoint.2] using (el.continuousAt hpoint.1).tendsto
    have hcomp := pointed_composition_germ_congr el rl.map er rr.map ht hl hh
    have hcancel := same_box_composition_germ F r rl rr hlb hrb hlf (hls.trans hrf.symm) hrs
    exact hcomp.trans hcancel


/-- The initial time of a chronological finite plaque chain is at most its terminal time. -/
theorem plaque_chain_ordered {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {a b : unitInterval}
    {e : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)}
    (h : PlaqueChainAlong F γ a b e) : a ≤ b := by
  induction h with
  | single a b hab e hs => exact hab
  | compose hab hbc left right ihl ihr => exact hab.trans hbc


/-- A finite plaque chain can be split at any intermediate time into two representatives whose
composite has the original germ. (Nisoli, pp.22–23) -/
theorem plaque_chain_split_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {a b : unitInterval}
    {e : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)}
    (h : PlaqueChainAlong F γ a b e) :
    ∀ m : unitInterval, a ≤ m → m ≤ b →
      ∃ l : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ m).val),
      ∃ r : OpenPartialHomeomorph (F.ULeaf (γ m).val) (F.ULeaf (γ b).val),
        PlaqueChainAlong F γ a m l ∧ PlaqueChainAlong F γ m b r ∧
        (Filter.Germ.ofFun e : Filter.Germ (𝓝 (F.uPoint (γ a).val)) (F.ULeaf (γ b).val)) =
          Filter.Germ.ofFun (r ∘ l) := by
  induction h with
  | single a b hab e hs =>
    intro m ham hmb
    obtain ⟨zm,hzm⟩ := hs m ham hmb
    obtain ⟨l,hlb,hlf,hls,hlt,_⟩ := local_plaque_transport_of_box F e.box e.first zm
      e.transverse (γ a).val (γ m).val e.first_point hzm
    obtain ⟨r,hrb,hrf,hrs,hrt,_⟩ := local_plaque_transport_of_box F e.box zm e.second
      e.transverse (γ m).val (γ b).val hzm e.second_point
    refine ⟨l.map,r.map,PlaqueChainAlong.single a m ham l ?_,
      PlaqueChainAlong.single m b hmb r ?_,?_⟩
    · intro v hav hvm
      obtain ⟨z,hz⟩ := hs v hav (hvm.trans hmb)
      refine ⟨z,?_⟩
      have heq := congrArg (fun i ↦ ((F.box i).chart (z,e.transverse)).val) hlb
      simpa only [hlt] using heq.trans hz
    · intro v hmv hvb
      obtain ⟨z,hz⟩ := hs v (ham.trans hmv) hvb
      refine ⟨z,?_⟩
      have heq := congrArg (fun i ↦ ((F.box i).chart (z,e.transverse)).val) hrb
      simpa only [hrt] using heq.trans hz
    · exact (same_box_composition_germ F e l r hlb hrb hlf (hls.trans hrf.symm) hrs).symm
  | @compose a b c el er hab hbc left right ihl ihr =>
    intro m ham hmc
    have hpoint := plaque_chain_pointed F γ left
    have ht : Tendsto el (𝓝 (F.uPoint (γ a).val)) (𝓝 (F.uPoint (γ b).val)) := by
      simpa only [hpoint.2] using (el.continuousAt hpoint.1).tendsto
    by_cases hmb : m ≤ b
    · obtain ⟨l,r,hl,hr,heq⟩ := ihl m ham hmb
      refine ⟨l,r.trans er,hl,PlaqueChainAlong.compose hmb hbc hr right,?_⟩
      have hh := pointed_composition_germ_congr el (r ∘ l) er er ht heq rfl
      simpa only [OpenPartialHomeomorph.coe_trans,Function.comp_def] using hh
    · have hbm : b ≤ m := le_of_not_ge hmb
      obtain ⟨l,r,hl,hr,heq⟩ := ihr m hbm hmc
      refine ⟨el.trans l,r,PlaqueChainAlong.compose hab hbm left hl,hr,?_⟩
      have hh := pointed_composition_germ_congr el el er (r ∘ l) ht rfl heq
      simpa only [OpenPartialHomeomorph.coe_trans,Function.comp_def] using hh


/-- All finite plaque chains along the same subpath have the same germ, independently of boxes and
subdivisions. (Nisoli, Remark 1.3.5, pp.22–23) -/
theorem same_subpath_plaque_chain_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {a b : unitInterval}
    {e : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val)}
    (h : PlaqueChainAlong F γ a b e) :
    ∀ e' : OpenPartialHomeomorph (F.ULeaf (γ a).val) (F.ULeaf (γ b).val),
      PlaqueChainAlong F γ a b e' →
      (Filter.Germ.ofFun e : Filter.Germ (𝓝 (F.uPoint (γ a).val)) (F.ULeaf (γ b).val)) =
        Filter.Germ.ofFun e' := by
  induction h with
  | single a b hab l hs =>
    intro e' he'
    exact (plaque_chain_germ_in_one_plaque F γ he' l hs).symm
  | @compose a b c el er hab hbc left right ihl ihr =>
    intro e' he'
    obtain ⟨l,r,hl,hr,hg⟩ := plaque_chain_split_germ F γ he' b hab hbc
    have hpoint := plaque_chain_pointed F γ left
    have ht : Tendsto el (𝓝 (F.uPoint (γ a).val)) (𝓝 (F.uPoint (γ b).val)) := by
      simpa only [hpoint.2] using (el.continuousAt hpoint.1).tendsto
    have hh := pointed_composition_germ_congr el l er r ht (ihl l hl) (ihr r hr)
    have heq : (Filter.Germ.ofFun (el.trans er) :
        Filter.Germ (𝓝 (F.uPoint (γ a).val)) (F.ULeaf (γ c).val)) =
        Filter.Germ.ofFun (r ∘ l) := by
      simpa only [OpenPartialHomeomorph.coe_trans] using hh
    exact heq.trans hg.symm


/-- Every intrinsic stable-leaf path admits a local holonomy continuation coherent under
subdivision. (Nisoli, Remark 1.3.5, p.23; Ghys, Lemma 5.1, pp.597–598) -/
theorem local_holonomy_continuation_exists_g9 {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) :
    Nonempty (LocalHolonomyContinuation F γ) := by
  classical
  let reps (a b : unitInterval) (hab : a ≤ b) : PathHolonomyRepresentative F γ a b :=
    (path_holonomy_subinterval_representative_exists F γ a b hab).some
  refine ⟨{representative := reps, refinement := ?_}⟩
  intro a b c hab hbc
  have h := same_subpath_plaque_chain_germ F γ
    (PlaqueChainAlong.compose hab hbc (reps a b hab).chain (reps b c hbc).chain)
    (reps a c (hab.trans hbc)).map (reps a c (hab.trans hbc)).chain
  simpa only [OpenPartialHomeomorph.coe_trans] using h


/-- Every finite representative of an ordered subinterval has the germ of the chosen local holonomy
continuation on that subinterval. (Nisoli, pp.22–23) -/
theorem local_continuation_representative_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (L : LocalHolonomyContinuation F γ) (a b : unitInterval) (hab : a ≤ b)
    (e : PathHolonomyRepresentative F γ a b) :
    (Filter.Germ.ofFun (L.representative a b hab).map :
      Filter.Germ (𝓝 (F.uPoint (γ a).val)) (F.ULeaf (γ b).val)) =
        Filter.Germ.ofFun e.map := by
  exact same_subpath_plaque_chain_germ F γ (L.representative a b hab).chain e.map e.chain


/-- The composite of any two adjacent subinterval representatives has the germ of any representative
of their union. (Nisoli, Eq. (1.11), pp.22–23) -/
theorem local_representative_concatenation_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c)
    (l : PathHolonomyRepresentative F γ a b) (r : PathHolonomyRepresentative F γ b c)
    (e : PathHolonomyRepresentative F γ a c) :
    (Filter.Germ.ofFun (r.map ∘ l.map) :
      Filter.Germ (𝓝 (F.uPoint (γ a).val)) (F.ULeaf (γ c).val)) =
        Filter.Germ.ofFun e.map := by
  have h := same_subpath_plaque_chain_germ F γ
    (PlaqueChainAlong.compose hab hbc l.chain r.chain) e.map e.chain
  simpa only [OpenPartialHomeomorph.coe_trans] using h


/-- A one-box plaque correspondence whose centers coincide has the identity germ. (Nisoli, Eq.
(1.9), pp.21–22) -/
theorem same_center_plaque_identity_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M) {x : M}
    (e : LocalPlaqueTransport F x x) :
    (Filter.Germ.ofFun e.map : Filter.Germ (𝓝 (F.uPoint x)) (F.ULeaf x)) =
      Filter.Germ.ofFun id := by
  have hcoords : e.first = e.second := by
    have he : (F.box e.box).chart (e.first,e.transverse) =
        (F.box e.box).chart (e.second,e.transverse) :=
      Subtype.ext (e.first_point.trans e.second_point.symm)
    exact congrArg Prod.fst ((F.box e.box).chart.injective he)
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [e.map.open_source.mem_nhds e.source_point] with z hz
  obtain ⟨v,hv⟩ := e.source_in_plaque z hz
  apply Subtype.ext
  change (e.map z).val = z.val
  rw [e.coordinate_map z v hz hv,← hcoords]
  exact hv


/-- Every finite holonomy representative of a constant intrinsic path has the identity germ.
(Nisoli, Remarks 1.3.2 and 1.3.5, pp.21–23) -/
theorem constant_path_representative_identity_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    {q : Quotient F.stablePartition} (x : IntrinsicFoliationLeaf F.stablePartition q)
    (a b : unitInterval) (e : PathHolonomyRepresentative F (Path.refl x) a b) :
    (Filter.Germ.ofFun e.map : Filter.Germ (𝓝 (F.uPoint x.val)) (F.ULeaf x.val)) =
      Filter.Germ.ofFun id := by
  obtain ⟨i,hi⟩ := F.cover x.val
  let zw := (F.box i).chart.symm ⟨x.val,hi⟩
  have hv : ((F.box i).chart zw).val = x.val :=
    congrArg Subtype.val ((F.box i).chart.apply_symm_apply ⟨x.val,hi⟩)
  obtain ⟨r,hrb,hrf,hrs,hrt,_⟩ := local_plaque_transport_of_box F i zw.1 zw.1 zw.2 x.val x.val hv hv
  have hs : ∀ v : unitInterval, a ≤ v → v ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box r.box).chart (z,r.transverse)).val = x.val := by
    intro v hav hvb
    refine ⟨zw.1,?_⟩
    have hh := congrArg (fun j ↦ ((F.box j).chart (zw.1,zw.2)).val) hrb
    simpa only [hrt] using hh.trans hv
  have hh := plaque_chain_germ_in_one_plaque F (Path.refl x) e.chain r hs
  exact hh.trans (same_center_plaque_identity_germ F r)


end HolomorphicAnosov
end
