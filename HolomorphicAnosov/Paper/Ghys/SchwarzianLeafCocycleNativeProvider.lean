import HolomorphicAnosov.Geometry.Holonomy.CompleteLinearCoordinatesGlobalHolonomyG8
import HolomorphicAnosov.Paper.Ghys.SchwarzianLeafCocycleHolomorphicBridgeG12
import HolomorphicAnosov.Paper.Ghys.IntrinsicUnstableTransportBiholomorphG5
import HolomorphicAnosov.Geometry.StableLeafHomeomorphG9
import HolomorphicAnosov.Geometry.StableLeafTransportG9
import HolomorphicAnosov.Paper.Ghys.SchwarzianAffineCurveCalculus
import HolomorphicAnosov.Ghys.SchwarzianCoordinateIndependence
import HolomorphicAnosov.Paper.Ghys.Proposition31
import HolomorphicAnosov.Ghys.AffineDevelopingConnectedChart
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry

/-! This file constructs stable holonomy and its Schwarzian cocycle on simply connected intrinsic
stable leaves, together with equivariance and affine iterate laws (Ghys, §4, pp. 594–595;
Nisoli, Thm 1.3.8, pp. 24–25). -/

noncomputable section
set_option linter.style.haveILetI false
open scoped ContDiff Manifold _root_.Topology
open Set Filter _root_.Topology
namespace HolomorphicAnosov
universe u

private def squareRow {X : Type*} [TopologicalSpace X]
    (H : unitInterval × unitInterval → X) (hH : Continuous H) (a : unitInterval) :
    Path (H (a,0)) (H (a,1)) :=
  ⟨⟨fun v ↦ H (a,v), hH.comp (continuous_const.prodMk continuous_id)⟩, rfl, rfl⟩

private def squareColumn {X : Type*} [TopologicalSpace X]
    (H : unitInterval × unitInterval → X) (hH : Continuous H) (a : unitInterval) :
    Path (H (0,a)) (H (1,a)) :=
  ⟨⟨fun v ↦ H (v,a), hH.comp (continuous_id.prodMk continuous_const)⟩, rfl, rfl⟩


/-- Commuting squares of germs give a commuting square for prefix maps that agree locally with the
successive edge compositions. -/
private theorem germ_prefix_strip_g12 {n : ℕ}
    (X : Fin (n + 1) → Type u) (Y : Fin (n + 1) → Type v)
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (x : ∀ i, X i) (y : ∀ i, Y i)
    (B : ∀ i, X 0 → X i) (T : ∀ i, Y 0 → Y i)
    (b : ∀ i : Fin n, X i.castSucc → X i.succ)
    (t : ∀ i : Fin n, Y i.castSucc → Y i.succ)
    (V : ∀ i, X i → Y i)
    (hB : ∀ i, Tendsto (B i) (𝓝 (x 0)) (𝓝 (x i)))
    (hV : Tendsto (V 0) (𝓝 (x 0)) (𝓝 (y 0)))
    (hB0 : B 0 =ᶠ[𝓝 (x 0)] id) (hT0 : T 0 =ᶠ[𝓝 (y 0)] id)
    (hBs : ∀ i : Fin n, B i.succ =ᶠ[𝓝 (x 0)] b i ∘ B i.castSucc)
    (hTs : ∀ i : Fin n, T i.succ =ᶠ[𝓝 (y 0)] t i ∘ T i.castSucc)
    (hsquare : ∀ i : Fin n, V i.succ ∘ b i =ᶠ[𝓝 (x i.castSucc)] t i ∘ V i.castSucc) :
    ∀ i, V i ∘ B i =ᶠ[𝓝 (x 0)] T i ∘ V 0 := by
  intro i
  induction i using Fin.induction with
  | zero =>
    filter_upwards [hB0, hV.eventually hT0] with z hzb hzt
    exact (congrArg (V 0) hzb).trans hzt.symm
  | succ i ih =>
    filter_upwards [hBs i, (hB i.castSucc).eventually (hsquare i), ih,
      hV.eventually (hTs i)] with z hzb hzs hzi hzt
    change V i.succ (B i.succ z) = T i.succ (V 0 z)
    rw [hzb]
    exact hzs.trans ((congrArg (t i) hzi).trans hzt.symm)


section NormalizedPathGerms
variable {s t : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (Fin (s+t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,u} s t M)
  (φ : ∀ x : M, F.ULeaf x ≃ₜ ℂ)
  (hzero : ∀ x, φ x (F.uPoint x) = 0)
  {q : Quotient F.stablePartition}
  {x y : IntrinsicFoliationLeaf F.stablePartition q}


/-- The point-preserving homeomorphism between intrinsic unstable leaves with equal quotient labels. -/
def unstableLeafLabelHomeomorph_g17
    (q q' : Quotient F.unstablePartition) (h : q = q') :
    @Homeomorph (IntrinsicFoliationLeaf F.unstablePartition q)
      (IntrinsicFoliationLeaf F.unstablePartition q')
      (F.unstableTopology q) (F.unstableTopology q') := by
  subst q'
  letI := F.unstableTopology q
  exact Homeomorph.refl _

@[simp] theorem unstableLeafLabelHomeomorph_g17_val
    (q q' : Quotient F.unstablePartition) (h : q = q')
    (z : IntrinsicFoliationLeaf F.unstablePartition q) :
    (unstableLeafLabelHomeomorph_g17 F q q' h z).val = z.val := by
  subst q'
  rfl

/-- A local plaque transport can be marked at any point of its open source after identifying the
corresponding unstable leaf labels. -/
theorem repoint_local_plaque_transport_g17 {a b : M}
    (e : LocalPlaqueTransport F a b) (p : F.ULeaf a) (hp : p ∈ e.map.source) :
    let E := unstableLeafLabelHomeomorph_g17 F
      (Quotient.mk F.unstablePartition p.val) (Quotient.mk F.unstablePartition a) p.property
    ∃ r : LocalPlaqueTransport F p.val (e.map p).val,
      r.box = e.box ∧ r.first = e.first ∧ r.second = e.second ∧
      (∀ z, z ∈ r.map.source ↔ E z ∈ e.map.source) ∧
      ∀ z, (r.map z).val = (e.map (E z)).val := by
  intro E
  let E' := unstableLeafLabelHomeomorph_g17 F
    (Quotient.mk F.unstablePartition (e.map p).val)
    (Quotient.mk F.unstablePartition b) (e.map p).property
  let m := (E.toOpenPartialHomeomorph.trans e.map).trans E'.symm.toOpenPartialHomeomorph
  have hEpoint : E (F.uPoint p.val) = p := Subtype.ext (unstableLeafLabelHomeomorph_g17_val _ _ _ _ _)
  have hm (z) : (m z).val = (e.map (E z)).val := by
    have hh := unstableLeafLabelHomeomorph_g17_val F _ _ (e.map p).property
      (E'.symm (e.map (E z)))
    change (E' (E'.symm (e.map (E z)))).val = (E'.symm (e.map (E z))).val at hh
    rw [E'.apply_symm_apply] at hh
    exact hh.symm
  have hsource (z) : z ∈ m.source ↔ E z ∈ e.map.source := by
    simp [m]
  obtain ⟨w,hw⟩ := e.source_in_plaque p hp
  have hwp : (e.map p).val = ((F.box e.box).chart (e.second,w)).val :=
    e.coordinate_map p w hp hw
  refine ⟨{
    map := m
    source_point := by rw [hsource,hEpoint]; exact hp
    map_point := ?_
    box := e.box
    first := e.first
    second := e.second
    transverse := w
    first_point := hw
    second_point := hwp.symm
    source_in_plaque := ?_
    coordinate_map := ?_ },rfl,rfl,rfl,hsource,hm⟩
  · apply Subtype.ext
    change (m (F.uPoint p.val)).val = (e.map p).val
    rw [hm,hEpoint]
  · intro z hz
    obtain ⟨v,hv⟩ := e.source_in_plaque (E z) ((hsource z).mp hz)
    exact ⟨v,hv.trans (unstableLeafLabelHomeomorph_g17_val _ _ _ _ _)⟩
  · intro z v hz hv
    rw [hm]
    apply e.coordinate_map (E z) v ((hsource z).mp hz)
    exact hv.trans (unstableLeafLabelHomeomorph_g17_val _ _ _ _ _).symm

/-- A plaque transport whose source is the entire source plaque has the entire receiving plaque as
its target. -/
theorem local_plaque_transport_full_target_g17 {a b : M}
    (e : LocalPlaqueTransport F a b)
    (hsource : e.map.source = {z | ∃ w : FoliationCoordinateDisk t,
      ((F.box e.box).chart (e.first,w)).val = z.val}) :
    e.map.target = {z | ∃ w : FoliationCoordinateDisk t,
      ((F.box e.box).chart (e.second,w)).val = z.val} := by
  ext z
  constructor
  · intro hz
    obtain ⟨w,hw⟩ := e.source_in_plaque (e.map.symm z) (e.map.map_target hz)
    refine ⟨w,?_⟩
    have hh := e.coordinate_map (e.map.symm z) w (e.map.map_target hz) hw
    rw [e.map.right_inv hz] at hh
    exact hh.symm
  · rintro ⟨w,hw⟩
    let y : F.ULeaf a := ⟨((F.box e.box).chart (e.first,w)).val,
      (F.unstable_label e.box e.first w).trans
        ((F.unstable_label e.box e.first e.transverse).symm.trans
          (congrArg (Quotient.mk F.unstablePartition) e.first_point))⟩
    have hy : y ∈ e.map.source := hsource.symm ▸ ⟨w,rfl⟩
    have he : e.map y = z := Subtype.ext ((e.coordinate_map y w hy rfl).trans hw)
    rw [← he]
    exact e.map.map_source hy

/-- On the transport target, the receiving plaque projection equals the inverse plaque transport
followed by the chosen source coordinate. -/
theorem plaque_projection_eq_inverse_transport_g17 {a b : M} {Z : Type*}
    (e : LocalPlaqueTransport F a b) (d : F.ULeaf a → Z) (proj : M → Z)
    (hproj : ∀ (v : F.ULeaf a) (w : FoliationCoordinateDisk t),
      ((F.box e.box).chart (e.first,w)).val = v.val →
      proj ((F.box e.box).chart (e.second,w)).val = d v)
    (z : F.ULeaf b) (hz : z ∈ e.map.target) :
    proj z.val = d (e.map.symm z) := by
  obtain ⟨w,hw⟩ := e.source_in_plaque (e.map.symm z) (e.map.map_target hz)
  have hmap := e.coordinate_map (e.map.symm z) w (e.map.map_target hz) hw
  rw [e.map.right_inv hz] at hmap
  rw [hmap]
  exact hproj _ w hw

/-- The partial homeomorphism of `ℂ` obtained by expressing a pointed leaf homeomorphism in the
chosen leaf coordinates. -/
private def normLeafMap_g12 {a b : M} (e : PointedLeafHomeomorph F a b) :
    OpenPartialHomeomorph ℂ ℂ :=
  ((φ a).symm.toOpenPartialHomeomorph.trans e.map).trans (φ b).toOpenPartialHomeomorph

include hzero in
private theorem normLeafMap_point_g12 {a b : M} (e : PointedLeafHomeomorph F a b) :
    0 ∈ (normLeafMap_g12 F φ e).source ∧ normLeafMap_g12 F φ e 0 = 0 := by
  have hz : (φ a).symm 0 = F.uPoint a := (φ a).symm_apply_eq.mpr (hzero a).symm
  constructor
  · simp only [normLeafMap_g12, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_univ,
      Set.mem_preimage, Homeomorph.toOpenPartialHomeomorph_apply, hz]
    exact ⟨⟨trivial,e.source_point⟩,trivial⟩
  · change φ b (e.map ((φ a).symm 0)) = 0
    rw [hz,e.map_point,hzero]

include hzero in
private theorem normLeafMap_tendsto_g12 {a b : M} (e : PointedLeafHomeomorph F a b) :
    Tendsto (normLeafMap_g12 F φ e) (𝓝 0) (𝓝 0) := by
  obtain ⟨hs,hp⟩ := normLeafMap_point_g12 F φ hzero e
  simpa only [hp] using ((normLeafMap_g12 F φ e).continuousAt hs).tendsto

private def normPathMap_g12 (γ : Path x y) (a b : unitInterval) (hab : a ≤ b) :
    OpenPartialHomeomorph ℂ ℂ :=
  normLeafMap_g12 F φ
    (Classical.choice (path_holonomy_subinterval_representative_exists F γ a b hab)).toPointedLeafHomeomorph

include hzero in
private theorem normPathMap_spec_g12 (γ : Path x y) (a b : unitInterval) (hab : a ≤ b)
    (e : PathHolonomyRepresentative F γ a b) :
    normPathMap_g12 F φ γ a b hab =ᶠ[𝓝 0] normLeafMap_g12 F φ e.toPointedLeafHomeomorph := by
  let r := Classical.choice (path_holonomy_subinterval_representative_exists F γ a b hab)
  have hg := Germ.coe_eq.mp (same_subpath_plaque_chain_germ F γ r.chain e.map e.chain)
  have ht : Tendsto (φ (γ a).val).symm (𝓝 0) (𝓝 (F.uPoint (γ a).val)) := by
    have hp : (φ (γ a).val).symm 0 = F.uPoint (γ a).val :=
      (φ (γ a).val).symm_apply_eq.mpr (hzero _).symm
    simpa only [hp] using (φ (γ a).val).symm.continuous.continuousAt.tendsto (x := (0 : ℂ))
  filter_upwards [ht.eventually hg] with z hz
  exact congrArg (φ (γ b).val) hz

include hzero in
private theorem normPathMap_tendsto_g12 (γ : Path x y) (a b : unitInterval) (hab : a ≤ b) :
    Tendsto (normPathMap_g12 F φ γ a b hab) (𝓝 0) (𝓝 0) :=
  normLeafMap_tendsto_g12 F φ hzero _

include hzero in
private theorem normPathMap_subdivide_g12 (γ : Path x y)
    (a b c : unitInterval) (hab : a ≤ b) (hbc : b ≤ c) :
    normPathMap_g12 F φ γ a c (hab.trans hbc) =ᶠ[𝓝 0]
      (normPathMap_g12 F φ γ b c hbc ∘ normPathMap_g12 F φ γ a b hab) := by
  let l := Classical.choice (path_holonomy_subinterval_representative_exists F γ a b hab)
  let r := Classical.choice (path_holonomy_subinterval_representative_exists F γ b c hbc)
  let e := Classical.choice (path_holonomy_subinterval_representative_exists F γ a c (hab.trans hbc))
  have hg := Germ.coe_eq.mp (same_subpath_plaque_chain_germ F γ
    (PlaqueChainAlong.compose hab hbc l.chain r.chain) e.map e.chain)
  have hp : (φ (γ a).val).symm 0 = F.uPoint (γ a).val :=
    (φ (γ a).val).symm_apply_eq.mpr (hzero _).symm
  have ht : Tendsto (φ (γ a).val).symm (𝓝 0) (𝓝 (F.uPoint (γ a).val)) := by
    simpa only [hp] using (φ (γ a).val).symm.continuous.continuousAt.tendsto (x := (0 : ℂ))
  filter_upwards [ht.eventually hg] with z hz
  change φ (γ c).val (e.map ((φ (γ a).val).symm z)) =
    φ (γ c).val (r.map ((φ (γ b).val).symm (φ (γ b).val (l.map ((φ (γ a).val).symm z)))))
  rw [Homeomorph.symm_apply_apply]
  exact congrArg (φ (γ c).val) hz.symm

private theorem local_idempotent_germ_g12 (e : OpenPartialHomeomorph ℂ ℂ)
    (hs : 0 ∈ e.source) (hp : e 0 = 0) (hi : e ∘ e =ᶠ[𝓝 0] e) :
    e =ᶠ[𝓝 0] id := by
  have ht : Tendsto e (𝓝 0) (𝓝 0) := by simpa only [hp] using (e.continuousAt hs).tendsto
  filter_upwards [e.open_source.mem_nhds hs, ht.eventually (e.open_source.mem_nhds hs), hi]
    with z hz hez hi
  exact e.injOn hez hz hi

include hzero in
private theorem normPathMap_self_g12 (γ : Path x y) (a : unitInterval) :
    normPathMap_g12 F φ γ a a le_rfl =ᶠ[𝓝 0] id := by
  obtain ⟨hs,hp⟩ := normLeafMap_point_g12 F φ hzero
    (Classical.choice (path_holonomy_subinterval_representative_exists F γ a a le_rfl)).toPointedLeafHomeomorph
  exact local_idempotent_germ_g12 _ hs hp (normPathMap_subdivide_g12 F φ hzero γ a a a le_rfl le_rfl).symm


include hzero in
private theorem normPathMap_constant_g12 (γ : Path x y) (hc : ∀ v, γ v = x)
    (a b : unitInterval) (hab : a ≤ b) :
    normPathMap_g12 F φ γ a b hab =ᶠ[𝓝 0] id := by
  have hy : y = x := γ.target.symm.trans (hc 1)
  subst y
  have hγ : γ = Path.refl x := Path.ext (funext hc)
  subst γ
  let e := Classical.choice (path_holonomy_subinterval_representative_exists F (Path.refl x) a b hab)
  have hg := Germ.coe_eq.mp (constant_path_representative_identity_germ F x a b e)
  have hp : (φ x.val).symm 0 = F.uPoint x.val := (φ x.val).symm_apply_eq.mpr (hzero _).symm
  have ht : Tendsto (φ x.val).symm (𝓝 0) (𝓝 (F.uPoint x.val)) := by
    simpa only [hp] using (φ x.val).symm.continuous.continuousAt.tendsto (x := (0 : ℂ))
  filter_upwards [ht.eventually hg] with z hz
  change φ x.val (e.map ((φ x.val).symm z)) = z
  rw [hz]
  exact (φ x.val).apply_symm_apply z

set_option backward.isDefEq.respectTransparency false in
include hzero in
private theorem normPathMap_rectangle_g12
    (H : unitInterval × unitInterval → IntrinsicFoliationLeaf F.stablePartition q)
    (hH : Continuous H) (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (box : F.boxIndex) (w : FoliationCoordinateDisk t)
    (hcell : ∀ z ∈ Icc a b ×ˢ Icc c d, ∃ r : FoliationCoordinateDisk s,
      ((F.box box).chart (r,w)).val = (H z).val) :
    (normPathMap_g12 F φ (squareColumn H hH d) a b hab ∘
      normPathMap_g12 F φ (squareRow H hH a) c d hcd) =ᶠ[𝓝 0]
    (normPathMap_g12 F φ (squareRow H hH b) c d hcd ∘
      normPathMap_g12 F φ (squareColumn H hH c) a b hab) := by
  let B := Classical.choice (path_holonomy_subinterval_representative_exists F (squareRow H hH a) c d hcd)
  let T := Classical.choice (path_holonomy_subinterval_representative_exists F (squareRow H hH b) c d hcd)
  let L := Classical.choice (path_holonomy_subinterval_representative_exists F (squareColumn H hH c) a b hab)
  let R := Classical.choice (path_holonomy_subinterval_representative_exists F (squareColumn H hH d) a b hab)
  have hg := plaque_rectangle_representatives_commute F H hH a b c d hab hcd box w hcell B T L R
  have hp : (φ (H (a,c)).val).symm 0 = F.uPoint (H (a,c)).val :=
    (φ (H (a,c)).val).symm_apply_eq.mpr (hzero _).symm
  have ht : Tendsto (φ (H (a,c)).val).symm (𝓝 0) (𝓝 (F.uPoint (H (a,c)).val)) := by
    simpa only [hp] using (φ (H (a,c)).val).symm.continuous.continuousAt.tendsto (x := (0 : ℂ))
  filter_upwards [ht.eventually hg] with z hz
  change φ (H (b,d)).val (R.map ((φ (H (a,d)).val).symm
      (φ (H (a,d)).val (B.map ((φ (H (a,c)).val).symm z))))) =
    φ (H (b,d)).val (T.map ((φ (H (b,c)).val).symm
      (φ (H (b,c)).val (L.map ((φ (H (a,c)).val).symm z)))))
  simp only [Homeomorph.symm_apply_apply]
  exact congrArg (φ (H (b,d)).val) hz

include hzero in
private theorem normPathMap_strip_g12
    (H : unitInterval × unitInterval → IntrinsicFoliationLeaf F.stablePartition q)
    (hH : Continuous H) {n : ℕ} (a : Fin (n+2) → unitInterval) (ha : StrictMono a)
    (j : Fin (n+1))
    (hcells : ∀ k : Fin (n+1), ∃ box : F.boxIndex, ∃ w : FoliationCoordinateDisk t,
      ∀ z ∈ Icc (a j.castSucc) (a j.succ) ×ˢ Icc (a k.castSucc) (a k.succ),
        ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (H z).val) :
    (normPathMap_g12 F φ (squareColumn H hH (a (Fin.last (n+1))))
      (a j.castSucc) (a j.succ) (ha.monotone (Fin.castSucc_le_succ j)) ∘
    normPathMap_g12 F φ (squareRow H hH (a j.castSucc)) (a 0) (a (Fin.last (n+1)))
      (ha.monotone (Fin.zero_le _))) =ᶠ[𝓝 0]
    (normPathMap_g12 F φ (squareRow H hH (a j.succ)) (a 0) (a (Fin.last (n+1)))
      (ha.monotone (Fin.zero_le _)) ∘
    normPathMap_g12 F φ (squareColumn H hH (a 0))
      (a j.castSucc) (a j.succ) (ha.monotone (Fin.castSucc_le_succ j))) := by
  let bot (k : Fin (n+2)) := normPathMap_g12 F φ (squareRow H hH (a j.castSucc))
    (a 0) (a k) (ha.monotone (Fin.zero_le k))
  let top (k : Fin (n+2)) := normPathMap_g12 F φ (squareRow H hH (a j.succ))
    (a 0) (a k) (ha.monotone (Fin.zero_le k))
  let vert (k : Fin (n+2)) := normPathMap_g12 F φ (squareColumn H hH (a k))
    (a j.castSucc) (a j.succ) (ha.monotone (Fin.castSucc_le_succ j))
  let bedge (k : Fin (n+1)) := normPathMap_g12 F φ (squareRow H hH (a j.castSucc))
    (a k.castSucc) (a k.succ) (ha.monotone (Fin.castSucc_le_succ k))
  let tedge (k : Fin (n+1)) := normPathMap_g12 F φ (squareRow H hH (a j.succ))
    (a k.castSucc) (a k.succ) (ha.monotone (Fin.castSucc_le_succ k))
  apply germ_prefix_strip_g12 (fun _ : Fin (n+2) ↦ ℂ) (fun _ : Fin (n+2) ↦ ℂ)
    (fun _ ↦ 0) (fun _ ↦ 0) (fun k ↦ bot k) (fun k ↦ top k)
    (fun k ↦ bedge k) (fun k ↦ tedge k) (fun k ↦ vert k)
    (fun k ↦ normPathMap_tendsto_g12 F φ hzero _ _ _ _)
    (normPathMap_tendsto_g12 F φ hzero _ _ _ _)
    (normPathMap_self_g12 F φ hzero _ _) (normPathMap_self_g12 F φ hzero _ _)
    (fun k ↦ normPathMap_subdivide_g12 F φ hzero _ _ _ _ _ _)
    (fun k ↦ normPathMap_subdivide_g12 F φ hzero _ _ _ _ _ _) ?_ (Fin.last (n+1))
  intro k
  obtain ⟨box,w,hw⟩ := hcells k
  exact normPathMap_rectangle_g12 F φ hzero H hH _ _ _ _ _ _ box w hw


private theorem normPathMap_interval_congr_g12 (γ : Path x y)
    (a b a' b' : unitInterval) (hab : a ≤ b) (hab' : a' ≤ b')
    (ha : a = a') (hb : b = b') :
    normPathMap_g12 F φ γ a b hab = normPathMap_g12 F φ γ a' b' hab' := by
  subst a'; subst b'; rfl

private theorem normPathMap_path_congr_g12
    {x' y' : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (η : Path x' y') (he : ∀ v, γ v = η v)
    (a b : unitInterval) (hab : a ≤ b) :
    normPathMap_g12 F φ γ a b hab = normPathMap_g12 F φ η a b hab := by
  have hx : x = x' := γ.source.symm.trans ((he 0).trans η.source)
  have hy : y = y' := γ.target.symm.trans ((he 1).trans η.target)
  subst x'; subst y'
  have hγη : γ = η := Path.ext (funext he)
  subst η
  rfl

include hzero in
/-- Endpoint-fixed homotopic stable paths have the same normalized holonomy germ. -/
private theorem normPathMap_homotopy_square_g12
    (H : unitInterval × unitInterval → IntrinsicFoliationLeaf F.stablePartition q)
    (hH : Continuous H)
    (hleft : ∀ r, H (r,0) = H (0,0)) (hright : ∀ r, H (r,1) = H (0,1)) :
    normPathMap_g12 F φ (squareRow H hH 0) 0 1 zero_le_one =ᶠ[𝓝 0]
      normPathMap_g12 F φ (squareRow H hH 1) 0 1 zero_le_one := by
  obtain ⟨n,a,ha,h0,h1,hcells⟩ := intrinsic_plaque_square_subdivision F q H hH
  have hadj (j : Fin (n+1)) :
      normPathMap_g12 F φ (squareRow H hH (a j.castSucc)) 0 1 zero_le_one =ᶠ[𝓝 0]
        normPathMap_g12 F φ (squareRow H hH (a j.succ)) 0 1 zero_le_one := by
    have hs := normPathMap_strip_g12 F φ hzero H hH a ha j (fun k ↦ by
      obtain ⟨box,w,_,hw⟩ := hcells j k
      exact ⟨box,w,hw⟩)
    have hn (r : unitInterval) := normPathMap_interval_congr_g12 F φ
      (squareRow H hH r) (a 0) (a (Fin.last (n+1))) 0 1
      (ha.monotone (Fin.zero_le _)) zero_le_one h0 h1
    rw [hn,hn] at hs
    have hl := normPathMap_constant_g12 F φ hzero (squareColumn H hH (a 0))
      (fun v ↦ by change H (v,a 0) = H (0,a 0); rw [h0]; exact hleft v)
      (a j.castSucc) (a j.succ) (ha.monotone (Fin.castSucc_le_succ j))
    have hr := normPathMap_constant_g12 F φ hzero (squareColumn H hH (a (Fin.last (n+1))))
      (fun v ↦ by change H (v,a (Fin.last (n+1))) = H (0,a (Fin.last (n+1))); rw [h1]; exact hright v)
      (a j.castSucc) (a j.succ) (ha.monotone (Fin.castSucc_le_succ j))
    have hbot := normPathMap_tendsto_g12 F φ hzero (squareRow H hH (a j.castSucc)) 0 1 zero_le_one
    filter_upwards [hs, hbot.eventually hr, hl] with z hz hrz hlz
    change _ = _ at hz
    simpa only [Function.comp_apply, hrz, hlz, id_eq] using hz
  have hall : ∀ k : Fin (n+2),
      normPathMap_g12 F φ (squareRow H hH (a 0)) 0 1 zero_le_one =ᶠ[𝓝 0]
        normPathMap_g12 F φ (squareRow H hH (a k)) 0 1 zero_le_one := by
    apply Fin.induction
    · exact EventuallyEq.rfl
    · intro k ih; exact ih.trans (hadj k)
  have hh := hall (Fin.last (n+1))
  have hb := congrArg (fun r : unitInterval ↦
    normPathMap_g12 F φ (squareRow H hH r) 0 1 zero_le_one) h0
  have ht := congrArg (fun r : unitInterval ↦
    normPathMap_g12 F φ (squareRow H hH r) 0 1 zero_le_one) h1
  rwa [hb,ht] at hh

include hzero in
private theorem normPathMap_homotopy_g12 (γ η : Path x y) (h : γ.Homotopy η) :
    normPathMap_g12 F φ γ 0 1 zero_le_one =ᶠ[𝓝 0] normPathMap_g12 F φ η 0 1 zero_le_one := by
  have hh := normPathMap_homotopy_square_g12 F φ hzero h h.continuous
    (fun r ↦ (h.source r).trans (h.source 0).symm)
    (fun r ↦ (h.target r).trans (h.target 0).symm)
  have hγ := normPathMap_path_congr_g12 F φ (squareRow h h.continuous 0) γ
    (fun v ↦ h.apply_zero v) 0 1 zero_le_one
  have hη := normPathMap_path_congr_g12 F φ (squareRow h h.continuous 1) η
    (fun v ↦ h.apply_one v) 0 1 zero_le_one
  rwa [hγ,hη] at hh


include hzero in
private theorem normLeafMap_congr_g12 {a b : M} (e e' : PointedLeafHomeomorph F a b)
    (hh : e.map =ᶠ[𝓝 (F.uPoint a)] e'.map) :
    normLeafMap_g12 F φ e =ᶠ[𝓝 0] normLeafMap_g12 F φ e' := by
  have hp : (φ a).symm 0 = F.uPoint a := (φ a).symm_apply_eq.mpr (hzero a).symm
  have ht : Tendsto (φ a).symm (𝓝 0) (𝓝 (F.uPoint a)) := by
    simpa only [hp] using (φ a).symm.continuous.continuousAt.tendsto (x := (0 : ℂ))
  filter_upwards [ht.eventually hh] with z hz
  exact congrArg (φ b) hz

include hzero in
private theorem normLeafMap_same_box_g12 {a b a' b' : M} (hx : a = a') (hy : b = b')
    (e : LocalPlaqueTransport F a b) (e' : LocalPlaqueTransport F a' b')
    (hbox : e.box = e'.box) :
    normLeafMap_g12 F φ e.toPointedLeafHomeomorph =ᶠ[𝓝 0]
      normLeafMap_g12 F φ e'.toPointedLeafHomeomorph := by
  subst a'; subst b'
  have hf := e.first_point
  have hs := e.second_point
  rw [hbox] at hf hs
  have hfirst : e.first = e'.first := congrArg Prod.fst
    ((F.box e'.box).chart.injective (Subtype.ext (hf.trans e'.first_point.symm)))
  have hsecond : e.second = e'.second := congrArg Prod.fst
    ((F.box e'.box).chart.injective (Subtype.ext (hs.trans e'.second_point.symm)))
  exact normLeafMap_congr_g12 F φ hzero _ _
    (Germ.coe_eq.mp (same_box_plaque_germ_g10 F e e' hbox hfirst hsecond))

include hzero in
private theorem normPathMap_eq_local_g12 (γ : Path x y) (a b : unitInterval) (hab : a ≤ b)
    (e : LocalPlaqueTransport F (γ a).val (γ b).val)
    (hseg : ∀ v : unitInterval, a ≤ v → v ≤ b →
      ∃ r : FoliationCoordinateDisk s, ((F.box e.box).chart (r,e.transverse)).val = (γ v).val) :
    normPathMap_g12 F φ γ a b hab =ᶠ[𝓝 0] normLeafMap_g12 F φ e.toPointedLeafHomeomorph := by
  let r := Classical.choice (path_holonomy_subinterval_representative_exists F γ a b hab)
  exact normLeafMap_congr_g12 F φ hzero r.toPointedLeafHomeomorph e.toPointedLeafHomeomorph
    (Germ.coe_eq.mp (plaque_chain_germ_in_one_plaque F γ r.chain e hseg))

include hzero in
private theorem normPathMap_same_plaque_g12
    {x' y' : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (η : Path x' y') (a b c d : unitInterval) (hab : a ≤ b) (hcd : c ≤ d)
    (hx : γ a = η c) (hy : γ b = η d)
    (box : F.boxIndex) (w : FoliationCoordinateDisk t)
    (hγ : ∀ v : unitInterval, a ≤ v → v ≤ b →
      ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (γ v).val)
    (hη : ∀ v : unitInterval, c ≤ v → v ≤ d →
      ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (η v).val) :
    normPathMap_g12 F φ γ a b hab =ᶠ[𝓝 0] normPathMap_g12 F φ η c d hcd := by
  obtain ⟨ga,hga⟩ := hγ a le_rfl hab
  obtain ⟨gb,hgb⟩ := hγ b hab le_rfl
  obtain ⟨ec,hec⟩ := hη c le_rfl hcd
  obtain ⟨ed,hed⟩ := hη d hcd le_rfl
  obtain ⟨e,heb,_,_,hew,_⟩ := local_plaque_transport_of_box F box ga gb w _ _ hga hgb
  obtain ⟨e',he'b,_,_,he'w,_⟩ := local_plaque_transport_of_box F box ec ed w _ _ hec hed
  have heγ := normPathMap_eq_local_g12 F φ hzero γ a b hab e (by
    intro v hv hv'
    obtain ⟨r,hr⟩ := hγ v hv hv'
    refine ⟨r,?_⟩
    rw [hew]
    exact (congrArg (fun j ↦ ((F.box j).chart (r,w)).val) heb).trans hr)
  have heη := normPathMap_eq_local_g12 F φ hzero η c d hcd e' (by
    intro v hv hv'
    obtain ⟨r,hr⟩ := hη v hv hv'
    refine ⟨r,?_⟩
    rw [he'w]
    exact (congrArg (fun j ↦ ((F.box j).chart (r,w)).val) he'b).trans hr)
  exact heγ.trans ((normLeafMap_same_box_g12 F φ hzero
    (congrArg Subtype.val hx) (congrArg Subtype.val hy) e e' (heb.trans he'b.symm)).trans heη.symm)

private theorem scalar_germ_comp_congr_g12 {f f' g g' : ℂ → ℂ}
    (hf : f =ᶠ[𝓝 0] f') (hg : g =ᶠ[𝓝 0] g') (ht : Tendsto f (𝓝 0) (𝓝 0)) :
    g ∘ f =ᶠ[𝓝 0] g' ∘ f' := by
  filter_upwards [ht.eventually hg, hf] with z hz hzf
  exact hz.trans (congrArg g' hzf)

include hzero in
private theorem normPathMap_reparam_g12
    {x' y' : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (η : Path x' y') (ρ : unitInterval → unitInterval)
    (hc : Continuous ρ) (hm : Monotone ρ) (he : ∀ v, η v = γ (ρ v)) :
    normPathMap_g12 F φ γ (ρ 0) (ρ 1) (hm zero_le_one) =ᶠ[𝓝 0]
      normPathMap_g12 F φ η 0 1 zero_le_one := by
  let H : unitInterval × unitInterval → IntrinsicFoliationLeaf F.stablePartition q := fun z ↦ η z.2
  have hH : Continuous H := η.continuous.comp continuous_snd
  obtain ⟨n,a,ha,h0,h1,hcells⟩ := intrinsic_plaque_square_subdivision F q H hH
  have hp : ∀ k : Fin (n+2),
      normPathMap_g12 F φ γ (ρ (a 0)) (ρ (a k)) (hm (ha.monotone (Fin.zero_le _))) =ᶠ[𝓝 0]
        normPathMap_g12 F φ η (a 0) (a k) (ha.monotone (Fin.zero_le _)) := by
    apply Fin.induction
    · exact (normPathMap_self_g12 F φ hzero _ _).trans (normPathMap_self_g12 F φ hzero _ _).symm
    · intro k ih
      obtain ⟨box,w,_,hw⟩ := hcells 0 k
      have hη : ∀ v : unitInterval, a k.castSucc ≤ v → v ≤ a k.succ →
          ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (η v).val := by
        intro v hv hv'
        exact hw (a 0,v) ⟨⟨le_rfl,ha.monotone (Fin.zero_le _)⟩,⟨hv,hv'⟩⟩
      have hγ : ∀ v : unitInterval, ρ (a k.castSucc) ≤ v → v ≤ ρ (a k.succ) →
          ∃ r : FoliationCoordinateDisk s, ((F.box box).chart (r,w)).val = (γ v).val := by
        intro v hv hv'
        have hsv := (hc.continuousOn.surjOn_Icc
          (show a k.castSucc ∈ Icc (a k.castSucc) (a k.succ) from
            ⟨le_rfl,ha.monotone (Fin.castSucc_le_succ k)⟩)
          (show a k.succ ∈ Icc (a k.castSucc) (a k.succ) from
            ⟨ha.monotone (Fin.castSucc_le_succ k),le_rfl⟩)) ⟨hv,hv'⟩
        obtain ⟨u,hu,hρu⟩ := hsv
        obtain ⟨r,hr⟩ := hη u hu.1 hu.2
        exact ⟨r,hr.trans (congrArg Subtype.val ((he u).trans (congrArg γ hρu)))⟩
      have hseg := normPathMap_same_plaque_g12 F φ hzero γ η
        (ρ (a k.castSucc)) (ρ (a k.succ)) (a k.castSucc) (a k.succ)
        (hm (ha.monotone (Fin.castSucc_le_succ k)))
        (ha.monotone (Fin.castSucc_le_succ k)) (he _).symm (he _).symm box w hγ hη
      have hγsplit := normPathMap_subdivide_g12 F φ hzero γ
        (ρ (a 0)) (ρ (a k.castSucc)) (ρ (a k.succ))
        (hm (ha.monotone (Fin.zero_le _))) (hm (ha.monotone (Fin.castSucc_le_succ k)))
      have hηsplit := normPathMap_subdivide_g12 F φ hzero η
        (a 0) (a k.castSucc) (a k.succ)
        (ha.monotone (Fin.zero_le _)) (ha.monotone (Fin.castSucc_le_succ k))
      exact hγsplit.trans ((scalar_germ_comp_congr_g12 ih hseg
        (normPathMap_tendsto_g12 F φ hzero _ _ _ _)).trans hηsplit.symm)
  have hγ := normPathMap_interval_congr_g12 F φ γ
    (ρ (a 0)) (ρ (a (Fin.last (n+1)))) (ρ 0) (ρ 1)
    (hm (ha.monotone (Fin.zero_le _))) (hm zero_le_one) (congrArg ρ h0) (congrArg ρ h1)
  have hη := normPathMap_interval_congr_g12 F φ η
    (a 0) (a (Fin.last (n+1))) 0 1 (ha.monotone (Fin.zero_le _)) zero_le_one h0 h1
  have hh := hp (Fin.last (n+1))
  rwa [hγ,hη] at hh

include hzero in
private theorem normPathMap_trans_g12
    {x y z : IntrinsicFoliationLeaf F.stablePartition q}
    (γ : Path x y) (η : Path y z) :
    normPathMap_g12 F φ (γ.trans η) 0 1 zero_le_one =ᶠ[𝓝 0]
      (normPathMap_g12 F φ η 0 1 zero_le_one ∘ normPathMap_g12 F φ γ 0 1 zero_le_one) := by
  let m : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
  let l : unitInterval → unitInterval := Icc.convexComb 0 m
  let r : unitInterval → unitInterval := Icc.convexComb m 1
  have hl : Monotone l := by
    intro u v huv
    change (1 - (u : ℝ)) * 0 + u * (1/2) ≤ (1 - (v : ℝ)) * 0 + v * (1/2)
    have huv' : (u : ℝ) ≤ v := huv
    linarith
  have hr : Monotone r := by
    intro u v huv
    change (1 - (u : ℝ)) * (1/2) + u * 1 ≤ (1 - (v : ℝ)) * (1/2) + v * 1
    have huv' : (u : ℝ) ≤ v := huv
    linarith
  have hle : ∀ v, γ v = (γ.trans η) (l v) := by
    intro v
    rw [Path.trans_apply, dite_eq_left (show ((l v : unitInterval) : ℝ) ≤ 1/2 by
      change (1-(v:ℝ))*0+(v:ℝ)*(1/2) ≤ 1/2
      linarith [v.property.2])]
    congr 1
    apply Subtype.ext
    change (v : ℝ) = 2*((1-(v:ℝ))*0+(v:ℝ)*(1/2))
    ring
  have hre : ∀ v, η v = (γ.trans η) (r v) := by
    intro v
    have hv : (1/2 : ℝ) ≤ r v := by
      change (1/2 : ℝ) ≤ (1-(v:ℝ))*(1/2)+(v:ℝ)*1
      linarith [v.property.1]
    calc
      η v = η.extend (2 * (r v : ℝ) - 1) := by
        have ht : 2 * (r v : ℝ) - 1 = (v : ℝ) := by
          change 2*((1-(v:ℝ))*(1/2)+(v:ℝ)*1)-1 = (v:ℝ)
          ring
        rw [ht, η.extend_extends']
      _ = (γ.trans η).extend (r v : ℝ) := (Path.extend_trans_of_half_le γ η hv).symm
      _ = (γ.trans η) (r v) := (γ.trans η).extend_extends' _
  have hL := normPathMap_reparam_g12 F φ hzero (γ.trans η) γ l (by dsimp [l]; fun_prop) hl hle
  have hR := normPathMap_reparam_g12 F φ hzero (γ.trans η) η r (by dsimp [r]; fun_prop) hr hre
  have hLi := normPathMap_interval_congr_g12 F φ (γ.trans η)
    (l 0) (l 1) 0 m (hl zero_le_one) (by exact m.property.1)
    (Icc.convexComb_zero 0 m) (Icc.convexComb_one 0 m)
  have hRi := normPathMap_interval_congr_g12 F φ (γ.trans η)
    (r 0) (r 1) m 1 (hr zero_le_one) (by exact m.property.2)
    (Icc.convexComb_zero m 1) (Icc.convexComb_one m 1)
  rw [hLi] at hL
  rw [hRi] at hR
  exact (normPathMap_subdivide_g12 F φ hzero (γ.trans η) 0 m 1 m.property.1 m.property.2).trans
    (scalar_germ_comp_congr_g12 hL hR (normPathMap_tendsto_g12 F φ hzero _ _ _ _))


private def pointedLeafCast_g12 {a b a' b' : M} (ha : a = a') (hb : b = b')
    (e : PointedLeafHomeomorph F a b) : PointedLeafHomeomorph F a' b' := ha ▸ hb ▸ e

private theorem normLeafMap_cast_g12 {a b a' b' : M} (ha : a = a') (hb : b = b')
    (e : PointedLeafHomeomorph F a b) :
    normLeafMap_g12 F φ (pointedLeafCast_g12 F ha hb e) = normLeafMap_g12 F φ e := by
  subst a'; subst b'; rfl

section SimplyConnectedLeaf
variable [SimplyConnectedSpace (IntrinsicFoliationLeaf F.stablePartition q)]

private def endpointHolonomy_g12 (x y : IntrinsicFoliationLeaf F.stablePartition q) :
    PointedLeafHomeomorph F x.val y.val :=
  let γ := PathConnectedSpace.somePath x y
  let e := Classical.choice (path_holonomy_subinterval_representative_exists F γ 0 1 zero_le_one)
  pointedLeafCast_g12 F (congrArg Subtype.val γ.source) (congrArg Subtype.val γ.target)
    e.toPointedLeafHomeomorph

private theorem endpointHolonomy_norm_spec_g12 (x y : IntrinsicFoliationLeaf F.stablePartition q) :
    normLeafMap_g12 F φ (endpointHolonomy_g12 F x y) =
      normPathMap_g12 F φ (PathConnectedSpace.somePath x y) 0 1 zero_le_one :=
  normLeafMap_cast_g12 F φ _ _ _

include hzero in
private theorem endpointHolonomy_representative_norm_g12 (γ : Path x y)
    (e : PathHolonomyRepresentative F γ 0 1) :
    normLeafMap_g12 F φ (endpointHolonomy_g12 F (γ 0) (γ 1)) =ᶠ[𝓝 0]
      normLeafMap_g12 F φ e.toPointedLeafHomeomorph := by
  rw [endpointHolonomy_norm_spec_g12]
  let δ := γ.cast γ.source γ.target
  have hh := normPathMap_homotopy_g12 F φ hzero (PathConnectedSpace.somePath (γ 0) (γ 1)) δ
    (SimplyConnectedSpace.paths_homotopic _ _).some
  have hδ := normPathMap_path_congr_g12 F φ δ γ (fun _ ↦ rfl) 0 1 zero_le_one
  rw [hδ] at hh
  exact hh.trans (normPathMap_spec_g12 F φ hzero γ 0 1 zero_le_one e)

include hzero in
private theorem endpointHolonomy_identity_norm_g12 (x : IntrinsicFoliationLeaf F.stablePartition q) :
    normLeafMap_g12 F φ (endpointHolonomy_g12 F x x) =ᶠ[𝓝 0] id := by
  rw [endpointHolonomy_norm_spec_g12]
  exact (normPathMap_homotopy_g12 F φ hzero (PathConnectedSpace.somePath x x) (Path.refl x)
    (SimplyConnectedSpace.paths_homotopic _ _).some).trans
      (normPathMap_constant_g12 F φ hzero (Path.refl x) (fun _ ↦ rfl) 0 1 zero_le_one)

include hzero in
private theorem endpointHolonomy_composition_norm_g12
    (x y z : IntrinsicFoliationLeaf F.stablePartition q) :
    normLeafMap_g12 F φ (endpointHolonomy_g12 F x z) =ᶠ[𝓝 0]
      (normLeafMap_g12 F φ (endpointHolonomy_g12 F y z) ∘
        normLeafMap_g12 F φ (endpointHolonomy_g12 F x y)) := by
  rw [endpointHolonomy_norm_spec_g12, endpointHolonomy_norm_spec_g12, endpointHolonomy_norm_spec_g12]
  exact (normPathMap_homotopy_g12 F φ hzero (PathConnectedSpace.somePath x z)
    ((PathConnectedSpace.somePath x y).trans (PathConnectedSpace.somePath y z))
    (SimplyConnectedSpace.paths_homotopic _ _).some).trans
      (normPathMap_trans_g12 F φ hzero _ _)

end SimplyConnectedLeaf

include hzero in
private theorem normLeafMap_reflect_g12 {a b : M} (e e' : PointedLeafHomeomorph F a b)
    (hh : normLeafMap_g12 F φ e =ᶠ[𝓝 0] normLeafMap_g12 F φ e') :
    e.map =ᶠ[𝓝 (F.uPoint a)] e'.map := by
  have ht : Tendsto (φ a) (𝓝 (F.uPoint a)) (𝓝 0) := by
    simpa only [hzero] using (φ a).continuous.continuousAt.tendsto (x := F.uPoint a)
  filter_upwards [ht.eventually hh] with z hz
  apply (φ b).injective
  change φ b (e.map ((φ a).symm (φ a z))) = φ b (e'.map ((φ a).symm (φ a z))) at hz
  simpa only [Homeomorph.symm_apply_apply, Function.comp_apply, id_eq] using hz

include hzero in
private theorem normLeafMap_reflect_comp_g12 {a b c : M}
    (e : PointedLeafHomeomorph F a b) (e' : PointedLeafHomeomorph F b c)
    (k : PointedLeafHomeomorph F a c)
    (hh : normLeafMap_g12 F φ k =ᶠ[𝓝 0]
      (normLeafMap_g12 F φ e' ∘ normLeafMap_g12 F φ e)) :
    k.map =ᶠ[𝓝 (F.uPoint a)] (e'.map ∘ e.map) := by
  have ht : Tendsto (φ a) (𝓝 (F.uPoint a)) (𝓝 0) := by
    simpa only [hzero] using (φ a).continuous.continuousAt.tendsto (x := F.uPoint a)
  filter_upwards [ht.eventually hh] with z hz
  apply (φ c).injective
  change φ c (k.map ((φ a).symm (φ a z))) =
    φ c (e'.map ((φ b).symm (φ b (e.map ((φ a).symm (φ a z)))))) at hz
  simpa only [Homeomorph.symm_apply_apply, Function.comp_apply, id_eq] using hz

include hzero in
private theorem normLeafMap_reflect_identity_g12 {a : M} (e : PointedLeafHomeomorph F a a)
    (hh : normLeafMap_g12 F φ e =ᶠ[𝓝 0] id) : e.map =ᶠ[𝓝 (F.uPoint a)] id := by
  have ht : Tendsto (φ a) (𝓝 (F.uPoint a)) (𝓝 0) := by
    simpa only [hzero] using (φ a).continuous.continuousAt.tendsto (x := F.uPoint a)
  filter_upwards [ht.eventually hh] with z hz
  apply (φ a).injective
  change φ a (e.map ((φ a).symm (φ a z))) = φ a z at hz
  simpa only [Homeomorph.symm_apply_apply, Function.comp_apply, id_eq] using hz


private theorem pointedLeafCast_holomorphic_g12
    [∀ a : M, ChartedSpace (ComplexModel 1) (F.ULeaf a)]
    {a b a' b' : M} (ha : a = a') (hb : b = b')
    (e : PointedLeafHomeomorph F a b) (he : Ghys.IsHolomorphicCurveLocalMap e.map) :
    Ghys.IsHolomorphicCurveLocalMap (pointedLeafCast_g12 F ha hb e).map := by
  subst a'; subst b'; exact he

private theorem endpointHolonomy_holomorphic_g12
    [∀ a : M, ChartedSpace (ComplexModel 1) (F.ULeaf a)]
    [SimplyConnectedSpace (IntrinsicFoliationLeaf F.stablePartition q)]
    (hH : ∀ {a b : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path a b)
      (e : PathHolonomyRepresentative F γ 0 1), Ghys.IsHolomorphicCurveLocalMap e.map)
    (x y : IntrinsicFoliationLeaf F.stablePartition q) :
    Ghys.IsHolomorphicCurveLocalMap (endpointHolonomy_g12 F x y).map := by
  apply pointedLeafCast_holomorphic_g12
  exact hH _ _

private theorem paired_intrinsic_path_subdivision_g12
    {q' : Quotient F.stablePartition}
    {x' y' : IntrinsicFoliationLeaf F.stablePartition q'} (γ : Path x y) (η : Path x' y') :
    ∃ n : ℕ, 0 < n ∧ ∃ a : Fin (n+1) → unitInterval,
      a 0 = 0 ∧ a (Fin.last n) = 1 ∧ Monotone a ∧
      ∀ j : Fin n, ∃ b : F.boxIndex, ∃ w : FoliationCoordinateDisk t,
        ∃ b' : F.boxIndex, ∃ w' : FoliationCoordinateDisk t,
          (∀ r : unitInterval, a j.castSucc ≤ r → r ≤ a j.succ →
            ∃ z : FoliationCoordinateDisk s, ((F.box b).chart (z,w)).val = (γ r).val) ∧
          (∀ r : unitInterval, a j.castSucc ≤ r → r ≤ a j.succ →
            ∃ z : FoliationCoordinateDisk s, ((F.box b').chart (z,w')).val = (η r).val) := by
  let J (q : Quotient F.stablePartition) :=
    {bw : (Σ _ : F.boxIndex, FoliationCoordinateDisk t) // F.stableLabel bw.1 bw.2 = q}
  let plaque {q : Quotient F.stablePartition} (i : J q) :
      FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition q := fun r ↦
    ⟨((F.box i.val.1).chart (r,i.val.2)).val,(F.stable_label i.val.1 r i.val.2).trans i.property⟩
  have hopen {q : Quotient F.stablePartition} (i : J q) : IsOpen (range (plaque i)) := by
    rcases i with ⟨⟨b,w⟩,h⟩
    subst q
    exact (F.stable_plaque b w).isOpen_range
  have hcover {q : Quotient F.stablePartition} (z : IntrinsicFoliationLeaf F.stablePartition q) :
      ∃ i : J q, z ∈ range (plaque i) := by
    obtain ⟨b,hb⟩ := F.cover z.val
    let rw := (F.box b).chart.symm ⟨z.val,hb⟩
    have he : ((F.box b).chart rw).val = z.val :=
      congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨z.val,hb⟩)
    have hl : F.stableLabel b rw.2 = q :=
      (F.stable_label b rw.1 rw.2).symm.trans
        ((congrArg (Quotient.mk F.stablePartition) he).trans z.property)
    exact ⟨⟨⟨b,rw.2⟩,hl⟩,rw.1,Subtype.ext he⟩
  let δ := γ.prod η
  obtain ⟨n,hn,a,h0,h1,ha,assigned,hs⟩ := exists_openCover_pathSubdivision δ
    (fun ij : J q × J q' ↦ range (plaque ij.1) ×ˢ range (plaque ij.2))
    (fun ij ↦ (hopen ij.1).prod (hopen ij.2)) (by
      intro r
      obtain ⟨i,hi⟩ := hcover (γ r)
      obtain ⟨j,hj⟩ := hcover (η r)
      exact ⟨(i,j),hi,hj⟩)
  refine ⟨n,hn,a,h0,h1,ha,?_⟩
  intro j
  let i := assigned j
  refine ⟨i.1.val.1,i.1.val.2,i.2.val.1,i.2.val.2,?_,?_⟩
  · intro r hr hr'
    have hmem : (γ r,η r) ∈ range (δ.subpath (a j.castSucc) (a j.succ)) := by
      rw [δ.range_subpath_of_le _ _ (ha (Fin.castSucc_le_succ j))]
      exact ⟨r,⟨hr,hr'⟩,rfl⟩
    obtain ⟨z,hz⟩ := (hs j hmem).1
    exact ⟨z,congrArg Subtype.val hz⟩
  · intro r hr hr'
    have hmem : (γ r,η r) ∈ range (δ.subpath (a j.castSucc) (a j.succ)) := by
      rw [δ.range_subpath_of_le _ _ (ha (Fin.castSucc_le_succ j))]
      exact ⟨r,⟨hr,hr'⟩,rfl⟩
    obtain ⟨z,hz⟩ := (hs j hmem).2
    exact ⟨z,congrArg Subtype.val hz⟩

section DynamicsNaturality
variable (f : M → M) (hf : Continuous f)
  (hstable : ∀ q : Quotient F.stablePartition,
    ∃ q' : Quotient F.stablePartition,
    ∃ E : @Homeomorph (IntrinsicFoliationLeaf F.stablePartition q)
      (IntrinsicFoliationLeaf F.stablePartition q') (F.stableTopology q) (F.stableTopology q'),
      ∀ z, (E z).val = f z.val)

include hstable in
private theorem image_connected_box_strip_g12
    (i b : F.boxIndex) (w : FoliationCoordinateDisk t)
    (K : Set (FoliationCoordinateDisk s)) (hK : IsPreconnected K)
    (hin : ∀ z ∈ K, f ((F.box i).chart (z,w)).val ∈ (F.box b).image)
    (a a' : FoliationCoordinateDisk s) (ha : a ∈ K) (ha' : a' ∈ K) :
    ((F.box b).chart.symm ⟨f ((F.box i).chart (a,w)).val,hin a ha⟩).2 =
      ((F.box b).chart.symm ⟨f ((F.box i).chart (a',w)).val,hin a' ha'⟩).2 := by
  letI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  let q := F.stableLabel i w
  letI := F.stableTopology q
  obtain ⟨q', E, hE⟩ := hstable q
  letI := F.stableTopology q'
  let h : K → IntrinsicFoliationLeaf F.stablePartition q := fun z ↦
    ⟨((F.box i).chart (z.val,w)).val,F.stable_label i z.val w⟩
  have hc : Continuous h := (F.stable_plaque i w).continuous.comp continuous_subtype_val
  have hlc := stable_box_transverse_locally_constant F b q' (E ∘ h) (E.continuous.comp hc)
    (fun z ↦ by simpa only [Function.comp_apply,hE] using hin z.val z.prop)
  have hh := hlc.apply_eq_of_preconnectedSpace ⟨a,ha⟩ ⟨a',ha'⟩
  simpa only [Function.comp_apply,hE] using hh

include hf in
private theorem image_compact_box_strip_tube_g12
    (i b : F.boxIndex) (w : FoliationCoordinateDisk t)
    (K : Set (FoliationCoordinateDisk s)) (hK : IsCompact K)
    (hin : ∀ z ∈ K, f ((F.box i).chart (z,w)).val ∈ (F.box b).image) :
    ∀ᶠ v in 𝓝 w, ∀ z ∈ K, f ((F.box i).chart (z,v)).val ∈ (F.box b).image := by
  apply hK.eventually_forall_of_forall_eventually
  intro z hz
  have hc : Continuous (fun p : FoliationCoordinateDisk t × FoliationCoordinateDisk s ↦
      f ((F.box i).chart (p.2,p.1)).val) :=
    hf.comp (continuous_subtype_val.comp ((F.box i).chart.continuous.comp
      (continuous_snd.prodMk continuous_fst)))
  exact hc.continuousAt.eventually ((F.box b).isOpen_image.mem_nhds (hin z hz))

include hf hstable in
/-- A receiving stable-plaque projection composed with `f` has the same germ before and after source
plaque transport along a compact connected strip. -/
theorem image_strip_projection_germ_g17 {x y : M} {Z : Type*}
    (b : F.boxIndex) (proj : M → Z) (label : FoliationCoordinateDisk t → Z)
    (hproj : ∀ z (hz : z ∈ (F.box b).image),
      proj z = label ((F.box b).chart.symm ⟨z,hz⟩).2)
    (e : LocalPlaqueTransport F x y) (p : F.ULeaf x) (hp : p ∈ e.map.source)
    (w : FoliationCoordinateDisk t) (hw : ((F.box e.box).chart (e.first,w)).val = p.val)
    (K : Set (FoliationCoordinateDisk s)) (hK : IsCompact K) (hcK : IsPreconnected K)
    (ha : e.first ∈ K) (hb : e.second ∈ K)
    (hin : ∀ a ∈ K, f ((F.box e.box).chart (a,w)).val ∈ (F.box b).image) :
    (fun z : F.ULeaf x ↦ proj (f (e.map z).val)) =ᶠ[𝓝 p]
      (fun z ↦ proj (f z.val)) := by
  have hqx : F.unstableLabel e.box e.first = Quotient.mk F.unstablePartition x :=
    (F.unstable_label e.box e.first w).symm.trans
      ((congrArg (Quotient.mk F.unstablePartition) hw).trans p.property)
  let j : FoliationCoordinateDisk t → F.ULeaf x := fun v ↦
    ⟨((F.box e.box).chart (e.first,v)).val,(F.unstable_label e.box e.first v).trans hqx⟩
  have hj : IsOpenEmbedding j := unstable_plaque_open_at_class_g10 F _ _ _ hqx
  let chart := hj.toOpenPartialHomeomorph j
  have hjw : j w = p := Subtype.ext hw
  have hpt : p ∈ chart.target := by
    simp only [chart,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨w,hjw⟩
  have hinv : chart.symm p = w := by
    rw [← hjw]
    exact hj.toOpenPartialHomeomorph_left_inv j
  have htube := image_compact_box_strip_tube_g12 F f hf e.box b w K hK hin
  have hnear : ∀ᶠ z in 𝓝 p, ∀ a ∈ K,
      f ((F.box e.box).chart (a,chart.symm z)).val ∈ (F.box b).image := by
    have ht := (chart.symm.continuousAt hpt).tendsto
    rw [hinv] at ht
    exact ht.eventually htube
  filter_upwards [hnear,e.map.open_source.mem_nhds hp] with z hz hze
  obtain ⟨v,hv⟩ := e.source_in_plaque z hze
  have hjv : j v = z := Subtype.ext hv
  have hinvz : chart.symm z = v := by
    rw [← hjv]
    exact hj.toOpenPartialHomeomorph_left_inv j
  have hstrip : ∀ a ∈ K, f ((F.box e.box).chart (a,v)).val ∈ (F.box b).image := by
    simpa only [hinvz] using hz
  have heq := image_connected_box_strip_g12 F f hstable e.box b v K hcK hstrip
    e.first e.second ha hb
  have hpj := congrArg label heq
  rw [← hproj _ (hstrip e.first ha),← hproj _ (hstrip e.second hb)] at hpj
  rw [e.coordinate_map z v hze hv]
  exact hpj.symm.trans (congrArg (proj ∘ f) hv)

include hf hstable in
/-- Plaque transport commutes locally with the leaf maps induced by `f` when the image of a compact
connected source strip lies in a receiving box. -/
theorem image_plaque_germ_of_strip_g12 {x y : M}
    (Ex : F.ULeaf x ≃ₜ F.ULeaf (f x)) (Ey : F.ULeaf y ≃ₜ F.ULeaf (f y))
    (hEx : ∀ z, (Ex z).val = f z.val) (hEy : ∀ z, (Ey z).val = f z.val)
    (e : LocalPlaqueTransport F x y) (e' : LocalPlaqueTransport F (f x) (f y))
    (K : Set (FoliationCoordinateDisk s)) (hK : IsCompact K) (hcK : IsPreconnected K)
    (ha : e.first ∈ K) (hb : e.second ∈ K)
    (hin : ∀ z ∈ K, f ((F.box e.box).chart (z,e.transverse)).val ∈ (F.box e'.box).image) :
    (Ey ∘ e.map) =ᶠ[𝓝 (F.uPoint x)] (e'.map ∘ Ex) := by
  classical
  have hEx0 : Ex (F.uPoint x) = F.uPoint (f x) := Subtype.ext (hEx _)
  have hEy0 : Ey (F.uPoint y) = F.uPoint (f y) := Subtype.ext (hEy _)
  have hqx : F.unstableLabel e.box e.first = Quotient.mk F.unstablePartition x :=
    (F.unstable_label e.box e.first e.transverse).symm.trans
      (congrArg (Quotient.mk F.unstablePartition) e.first_point)
  have hqy : F.unstableLabel e'.box e'.second = Quotient.mk F.unstablePartition (f y) :=
    (F.unstable_label e'.box e'.second e'.transverse).symm.trans
      (congrArg (Quotient.mk F.unstablePartition) e'.second_point)
  let jx : FoliationCoordinateDisk t → F.ULeaf x := fun v ↦
    ⟨((F.box e.box).chart (e.first,v)).val,(F.unstable_label e.box e.first v).trans hqx⟩
  let jy : FoliationCoordinateDisk t → F.ULeaf (f y) := fun v ↦
    ⟨((F.box e'.box).chart (e'.second,v)).val,(F.unstable_label e'.box e'.second v).trans hqy⟩
  have hox : IsOpenEmbedding jx := unstable_plaque_open_at_class_g10 F _ _ _ hqx
  have hoy : IsOpenEmbedding jy := unstable_plaque_open_at_class_g10 F _ _ _ hqy
  let ex := hox.toOpenPartialHomeomorph jx
  have hxw : jx e.transverse = F.uPoint x := Subtype.ext e.first_point
  have hyw : jy e'.transverse = F.uPoint (f y) := Subtype.ext e'.second_point
  have hxsrc : F.uPoint x ∈ ex.target := by
    simp only [ex, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨e.transverse,hxw⟩
  have hxinv : ex.symm (F.uPoint x) = e.transverse := by
    rw [← hxw]
    exact hox.toOpenPartialHomeomorph_left_inv jx
  have htube := image_compact_box_strip_tube_g12 F f hf e.box e'.box e.transverse K hK hin
  have hvnear : ∀ᶠ z in 𝓝 (F.uPoint x), ∀ a ∈ K,
      f ((F.box e.box).chart (a,ex.symm z)).val ∈ (F.box e'.box).image := by
    have htend := (ex.symm.continuousAt hxsrc).tendsto
    rw [hxinv] at htend
    exact htend.eventually htube
  have hyrange : Set.range jy ∈ 𝓝 (F.uPoint (f y)) := hoy.isOpen_range.mem_nhds ⟨e'.transverse,hyw⟩
  have htarget : ∀ᶠ z in 𝓝 (F.uPoint x), Ey (e.map z) ∈ Set.range jy := by
    have htend := Ey.continuous.continuousAt.tendsto.comp (e.map.continuousAt e.source_point).tendsto
    rw [e.map_point,hEy0] at htend
    exact htend.eventually hyrange
  have hsource : ∀ᶠ z in 𝓝 (F.uPoint x), Ex z ∈ e'.map.source := by
    have htend := Ex.continuous.continuousAt.tendsto (x := F.uPoint x)
    rw [hEx0] at htend
    exact htend.eventually (e'.map.open_source.mem_nhds e'.source_point)
  filter_upwards [hvnear,htarget,e.map.open_source.mem_nhds e.source_point,hsource] with z hz ht hze hze'
  obtain ⟨v,hv⟩ := e.source_in_plaque z hze
  have hjv : jx v = z := Subtype.ext hv
  have hinv : ex.symm z = v := by
    rw [← hjv]
    exact hox.toOpenPartialHomeomorph_left_inv jx
  have hstrip : ∀ a ∈ K, f ((F.box e.box).chart (a,v)).val ∈ (F.box e'.box).image := by
    simpa only [hinv] using hz
  have hcoords := image_connected_box_strip_g12 F f hstable e.box e'.box v K hcK
    hstrip e.first e.second ha hb
  obtain ⟨v',hv'⟩ := e'.source_in_plaque (Ex z) hze'
  obtain ⟨vout,hout⟩ := ht
  have hev : (Ey (e.map z)).val = f ((F.box e.box).chart (e.second,v)).val := by
    rw [hEy,e.coordinate_map z v hze hv]
  have hyout : ((F.box e'.box).chart (e'.second,vout)).val = (Ey (e.map z)).val :=
    congrArg Subtype.val hout
  have hinput : (F.box e'.box).chart.symm
      ⟨f ((F.box e.box).chart (e.first,v)).val,hstrip e.first ha⟩ = (e'.first,v') := by
    apply (F.box e'.box).chart.injective
    rw [(F.box e'.box).chart.apply_symm_apply]
    exact Subtype.ext ((congrArg f hv).trans ((hEx z).symm.trans hv'.symm))
  have houtput : (F.box e'.box).chart.symm
      ⟨f ((F.box e.box).chart (e.second,v)).val,hstrip e.second hb⟩ = (e'.second,vout) := by
    apply (F.box e'.box).chart.injective
    rw [(F.box e'.box).chart.apply_symm_apply]
    exact Subtype.ext (hev.symm.trans hyout.symm)
  have hvout : vout = v' := by
    rw [hinput,houtput] at hcoords
    exact hcoords.symm
  apply Subtype.ext
  change (Ey (e.map z)).val = (e'.map (Ex z)).val
  rw [e'.coordinate_map (Ex z) v' hze' hv',← hyout,hvout]


include hf hstable in
theorem image_single_plaque_subpath_g12
    (γ : Path x y) (a b : unitInterval) (hab : a ≤ b)
    {xa ya : M} (hxa : xa = f (γ a).val) (hya : ya = f (γ b).val)
    (Ex : F.ULeaf (γ a).val ≃ₜ F.ULeaf xa) (Ey : F.ULeaf (γ b).val ≃ₜ F.ULeaf ya)
    (hEx : ∀ z, (Ex z).val = f z.val) (hEy : ∀ z, (Ey z).val = f z.val)
    (e : LocalPlaqueTransport F (γ a).val (γ b).val) (e' : LocalPlaqueTransport F xa ya)
    (hs : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box e.box).chart (z,e.transverse)).val = (γ r).val)
    (hs' : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box e'.box).chart (z,e'.transverse)).val = f (γ r).val) :
    (Ey ∘ e.map) =ᶠ[𝓝 (F.uPoint (γ a).val)] (e'.map ∘ Ex) := by
  subst xa
  subst ya
  classical
  let D := Set.Icc a b
  letI : CompactSpace D := isCompact_iff_compactSpace.mp isCompact_Icc
  letI : PreconnectedSpace D := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
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
  apply image_plaque_germ_of_strip_g12 F f hf hstable Ex Ey hEx hEy e e' (Set.range p)
    (isCompact_range hc) (isPreconnected_range hc) ha hb
  rintro z ⟨r,rfl⟩
  obtain ⟨z',hz'⟩ := hs' r.val r.prop.1 r.prop.2
  rw [hp r,← hz']
  exact ((F.box e'.box).chart (z',e'.transverse)).prop


private def normTransport_g12 {a b : M} (E : F.ULeaf a ≃ₜ F.ULeaf b) : ℂ ≃ₜ ℂ :=
  ((φ a).symm.trans E).trans (φ b)

include hzero in
private theorem normTransport_tendsto_g12 {a b : M} (E : F.ULeaf a ≃ₜ F.ULeaf b)
    (hp : E (F.uPoint a) = F.uPoint b) : Tendsto (normTransport_g12 F φ E) (𝓝 0) (𝓝 0) := by
  have hzero' : normTransport_g12 F φ E 0 = 0 := by
    have hs : (φ a).symm 0 = F.uPoint a := (φ a).symm_apply_eq.mpr (hzero a).symm
    change φ b (E ((φ a).symm 0)) = 0
    rw [hs,hp,hzero]
  simpa only [hzero'] using (normTransport_g12 F φ E).continuous.continuousAt.tendsto (x := (0 : ℂ))

include hzero in
private theorem normTransport_square_g12 {a b a' b' : M}
    (Ex : F.ULeaf a ≃ₜ F.ULeaf a') (Ey : F.ULeaf b ≃ₜ F.ULeaf b')
    (e : PointedLeafHomeomorph F a b) (e' : PointedLeafHomeomorph F a' b')
    (hsquare : (Ey ∘ e.map) =ᶠ[𝓝 (F.uPoint a)] (e'.map ∘ Ex)) :
    (normTransport_g12 F φ Ey ∘ normLeafMap_g12 F φ e) =ᶠ[𝓝 0]
      (normLeafMap_g12 F φ e' ∘ normTransport_g12 F φ Ex) := by
  have hp : (φ a).symm 0 = F.uPoint a := (φ a).symm_apply_eq.mpr (hzero a).symm
  have ht : Tendsto (φ a).symm (𝓝 0) (𝓝 (F.uPoint a)) := by
    simpa only [hp] using (φ a).symm.continuous.continuousAt.tendsto (x := (0 : ℂ))
  filter_upwards [ht.eventually hsquare] with z hz
  change φ b' (Ey ((φ b).symm (φ b (e.map ((φ a).symm z))))) =
    φ b' (e'.map ((φ a').symm (φ a' (Ex ((φ a).symm z)))))
  simp only [Homeomorph.symm_apply_apply]
  exact congrArg (φ b') hz

include hf hstable hzero in
private theorem normPathMap_image_segment_g12
    {q' : Quotient F.stablePartition}
    {x' y' : IntrinsicFoliationLeaf F.stablePartition q'}
    (γ : Path x y) (η : Path x' y') (hpath : ∀ r, (η r).val = f (γ r).val)
    (E : ∀ r, F.ULeaf (γ r).val ≃ₜ F.ULeaf (η r).val)
    (hE : ∀ r z, (E r z).val = f z.val)
    (a b : unitInterval) (hab : a ≤ b)
    (box : F.boxIndex) (w : FoliationCoordinateDisk t)
    (box' : F.boxIndex) (w' : FoliationCoordinateDisk t)
    (hγ : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box box).chart (z,w)).val = (γ r).val)
    (hη : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box box').chart (z,w')).val = (η r).val) :
    (normTransport_g12 F φ (E b) ∘ normPathMap_g12 F φ γ a b hab) =ᶠ[𝓝 0]
      (normPathMap_g12 F φ η a b hab ∘ normTransport_g12 F φ (E a)) := by
  obtain ⟨ga,hga⟩ := hγ a le_rfl hab
  obtain ⟨gb,hgb⟩ := hγ b hab le_rfl
  obtain ⟨ea,hea⟩ := hη a le_rfl hab
  obtain ⟨eb,heb⟩ := hη b hab le_rfl
  obtain ⟨e,hebox,_,_,hew,_⟩ := local_plaque_transport_of_box F box ga gb w _ _ hga hgb
  obtain ⟨e',he'box,_,_,he'w,_⟩ := local_plaque_transport_of_box F box' ea eb w' _ _ hea heb
  have hs : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box e.box).chart (z,e.transverse)).val = (γ r).val := by
    intro r hr hr'
    obtain ⟨z,hz⟩ := hγ r hr hr'
    refine ⟨z,?_⟩
    rw [hew]
    exact (congrArg (fun j ↦ ((F.box j).chart (z,w)).val) hebox).trans hz
  have hs' : ∀ r : unitInterval, a ≤ r → r ≤ b →
      ∃ z : FoliationCoordinateDisk s, ((F.box e'.box).chart (z,e'.transverse)).val = (η r).val := by
    intro r hr hr'
    obtain ⟨z,hz⟩ := hη r hr hr'
    refine ⟨z,?_⟩
    rw [he'w]
    exact (congrArg (fun j ↦ ((F.box j).chart (z,w')).val) he'box).trans hz
  have himg := image_single_plaque_subpath_g12 F f hf hstable γ a b hab
    (hpath a) (hpath b) (E a) (E b) (hE a) (hE b) e e' hs (by
      intro r hr hr'
      obtain ⟨z,hz⟩ := hs' r hr hr'
      exact ⟨z,hz.trans (hpath r)⟩)
  have hB := normPathMap_eq_local_g12 F φ hzero γ a b hab e hs
  have hT := normPathMap_eq_local_g12 F φ hzero η a b hab e' hs'
  have hEa : E a (F.uPoint (γ a).val) = F.uPoint (η a).val :=
    Subtype.ext ((hE a _).trans (hpath a).symm)
  exact (hB.fun_comp (normTransport_g12 F φ (E b))).trans
    ((normTransport_square_g12 F φ hzero (E a) (E b) e.toPointedLeafHomeomorph e'.toPointedLeafHomeomorph himg).trans
      (hT.symm.comp_tendsto (normTransport_tendsto_g12 F φ hzero (E a) hEa)))

include hf hstable hzero in
private theorem normPathMap_image_path_g12
    {q' : Quotient F.stablePartition}
    {x' y' : IntrinsicFoliationLeaf F.stablePartition q'}
    (γ : Path x y) (η : Path x' y') (hpath : ∀ r, (η r).val = f (γ r).val)
    (E : ∀ r, F.ULeaf (γ r).val ≃ₜ F.ULeaf (η r).val)
    (hE : ∀ r z, (E r z).val = f z.val) :
    (normTransport_g12 F φ (E 1) ∘ normPathMap_g12 F φ γ 0 1 zero_le_one) =ᶠ[𝓝 0]
      (normPathMap_g12 F φ η 0 1 zero_le_one ∘ normTransport_g12 F φ (E 0)) := by
  obtain ⟨n,hn,a,h0,h1,ha,hcells⟩ := paired_intrinsic_path_subdivision_g12 F γ η
  let B (k : Fin (n+1)) := normPathMap_g12 F φ γ (a 0) (a k) (ha (Fin.zero_le k))
  let T (k : Fin (n+1)) := normPathMap_g12 F φ η (a 0) (a k) (ha (Fin.zero_le k))
  let be (k : Fin n) := normPathMap_g12 F φ γ (a k.castSucc) (a k.succ) (ha (Fin.castSucc_le_succ k))
  let te (k : Fin n) := normPathMap_g12 F φ η (a k.castSucc) (a k.succ) (ha (Fin.castSucc_le_succ k))
  let V (k : Fin (n+1)) := normTransport_g12 F φ (E (a k))
  have hs := germ_prefix_strip_g12 (fun _ : Fin (n+1) ↦ ℂ) (fun _ : Fin (n+1) ↦ ℂ)
    (fun _ ↦ 0) (fun _ ↦ 0) (fun k ↦ B k) (fun k ↦ T k)
    (fun k ↦ be k) (fun k ↦ te k) (fun k ↦ V k)
    (fun k ↦ normPathMap_tendsto_g12 F φ hzero _ _ _ _)
    (normTransport_tendsto_g12 F φ hzero (E (a 0)) (Subtype.ext ((hE (a 0) _).trans (hpath (a 0)).symm)))
    (normPathMap_self_g12 F φ hzero _ _) (normPathMap_self_g12 F φ hzero _ _)
    (fun k ↦ normPathMap_subdivide_g12 F φ hzero _ _ _ _ _ _)
    (fun k ↦ normPathMap_subdivide_g12 F φ hzero _ _ _ _ _ _)
    (fun k ↦ by
      obtain ⟨b,w,b',w',hγ,hη⟩ := hcells k
      exact normPathMap_image_segment_g12 F φ hzero f hf hstable γ η hpath E hE
        _ _ _ b w b' w' hγ hη) (Fin.last n)
  have hγ := normPathMap_interval_congr_g12 F φ γ (a 0) (a (Fin.last n)) 0 1
    (ha (Fin.zero_le _)) zero_le_one h0 h1
  have hη := normPathMap_interval_congr_g12 F φ η (a 0) (a (Fin.last n)) 0 1
    (ha (Fin.zero_le _)) zero_le_one h0 h1
  change (normTransport_g12 F φ (E (a (Fin.last n))) ∘ _) =ᶠ[𝓝 0]
    (_ ∘ normTransport_g12 F φ (E (a 0))) at hs
  dsimp only [B,T] at hs
  rw [hγ,hη] at hs
  have hE0 := congrArg (fun r ↦ normTransport_g12 F φ (E r)) h0
  have hE1 := congrArg (fun r ↦ normTransport_g12 F φ (E r)) h1
  rwa [hE0,hE1] at hs


include hzero in
private theorem normTransport_reflect_square_g12 {a b a' b' : M}
    (Ex : F.ULeaf a ≃ₜ F.ULeaf a') (Ey : F.ULeaf b ≃ₜ F.ULeaf b')
    (e : PointedLeafHomeomorph F a b) (e' : PointedLeafHomeomorph F a' b')
    (hsquare : (normTransport_g12 F φ Ey ∘ normLeafMap_g12 F φ e) =ᶠ[𝓝 0]
      (normLeafMap_g12 F φ e' ∘ normTransport_g12 F φ Ex)) :
    (Ey ∘ e.map) =ᶠ[𝓝 (F.uPoint a)] (e'.map ∘ Ex) := by
  have ht : Tendsto (φ a) (𝓝 (F.uPoint a)) (𝓝 0) := by
    simpa only [hzero] using (φ a).continuous.continuousAt.tendsto (x := F.uPoint a)
  filter_upwards [ht.eventually hsquare] with z hz
  apply (φ b').injective
  change φ b' (Ey ((φ b).symm (φ b (e.map ((φ a).symm (φ a z)))))) =
    φ b' (e'.map ((φ a').symm (φ a' (Ex ((φ a).symm (φ a z)))))) at hz
  simpa only [Homeomorph.symm_apply_apply,Function.comp_apply] using hz

set_option backward.isDefEq.respectTransparency false in
include hf hstable hzero in
/-- Endpoint holonomy germs commute with the leaf maps induced by `f`. -/
private theorem endpointHolonomy_equivariant_g12
    {q' : Quotient F.stablePartition}
    [SimplyConnectedSpace (IntrinsicFoliationLeaf F.stablePartition q)]
    [SimplyConnectedSpace (IntrinsicFoliationLeaf F.stablePartition q')]
    (es : IntrinsicFoliationLeaf F.stablePartition q →
      IntrinsicFoliationLeaf F.stablePartition q') (hes : Continuous es)
    (hesval : ∀ z, (es z).val = f z.val)
    (E : ∀ z : IntrinsicFoliationLeaf F.stablePartition q,
      F.ULeaf z.val ≃ₜ F.ULeaf (es z).val)
    (hE : ∀ z w, (E z w).val = f w.val)
    (x y : IntrinsicFoliationLeaf F.stablePartition q) :
    (E y ∘ (endpointHolonomy_g12 F x y).map) =ᶠ[𝓝 (F.uPoint x.val)]
      ((endpointHolonomy_g12 F (es x) (es y)).map ∘ E x) := by
  let γ := PathConnectedSpace.somePath x y
  let η := γ.map hes
  have hs := normPathMap_image_path_g12 F φ hzero f hf hstable γ η
    (fun r ↦ hesval (γ r)) (fun r ↦ E (γ r)) (fun r ↦ hE (γ r))
  have hsrc := endpointHolonomy_norm_spec_g12 F φ x y
  have htgt : normLeafMap_g12 F φ (endpointHolonomy_g12 F (es x) (es y)) =ᶠ[𝓝 0]
      normPathMap_g12 F φ η 0 1 zero_le_one := by
    rw [endpointHolonomy_norm_spec_g12]
    exact normPathMap_homotopy_g12 F φ hzero _ η (SimplyConnectedSpace.paths_homotopic _ _).some
  have hEx : E x (F.uPoint x.val) = F.uPoint (es x).val :=
    Subtype.ext ((hE x _).trans (hesval x).symm)
  have h0 := congrArg (fun z ↦ normTransport_g12 F φ (E z)) γ.source
  have h1 := congrArg (fun z ↦ normTransport_g12 F φ (E z)) γ.target
  rw [h0,h1] at hs
  apply normTransport_reflect_square_g12 F φ hzero (E x) (E y)
    (endpointHolonomy_g12 F x y) (endpointHolonomy_g12 F (es x) (es y))
  rw [hsrc]
  exact hs.trans (htgt.symm.comp_tendsto (normTransport_tendsto_g12 F φ hzero (E x) hEx))

end DynamicsNaturality

end NormalizedPathGerms
end HolomorphicAnosov


noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u v w
attribute [local instance] complex_isManifold_real


section CurveCalculus
variable {L₀ : Type u} {L₁ : Type v}
  [TopologicalSpace L₀] [TopologicalSpace L₁]
  [ChartedSpace (ComplexModel 1) L₀] [ChartedSpace (ComplexModel 1) L₁]
theorem affine_chart_at_g12 (A : ComplexAffineStructure L₀) (x : L₀) :
    ∃ c ∈ A.maximalAtlas L₀, x ∈ c.source := by
  obtain ⟨c, hc, hxc⟩ := A.out.cover x
  exact ⟨c, ⟨A.out.holomorphic c hc, fun d hd ↦ A.out.compatible d hd c hc⟩, hxc⟩

private theorem schwarzian_quadratic_exists_g12
    (A₀ : ComplexAffineStructure L₀) (A₁ : ComplexAffineStructure L₁)
    (h : OpenPartialHomeomorph L₀ L₁) (hh : IsHolomorphicCurveLocalMap h)
    (x : L₀) (hxh : x ∈ h.source) :
    ∃ Q : QuadraticForm ℂ (TangentSpace (complexModel 1) x),
      ∀ (c : OpenPartialHomeomorph L₀ ℂ) (d : OpenPartialHomeomorph L₁ ℂ),
        c ∈ A₀.maximalAtlas L₀ → d ∈ A₁.maximalAtlas L₁ →
        x ∈ c.source → h x ∈ d.source → Q = schwarzianQuadraticAt c h d x := by
  obtain ⟨c, hc, hxc⟩ := affine_chart_at_g12 A₀ x
  obtain ⟨d, hd, hxd⟩ := affine_chart_at_g12 A₁ (h x)
  refine ⟨schwarzianQuadraticAt c h d x, ?_⟩
  intro c' d' hc' hd' hxc' hxd'
  exact schwarzian_quadratic_coordinate_independent A₀ A₁ h hh c c' d d'
    hc hc' hd hd' x hxc hxc' hxh hxd hxd'

omit [ChartedSpace (ComplexModel 1) L₁] in
private theorem schwarzian_quadratic_germ_g12
    (c : OpenPartialHomeomorph L₀ ℂ) (d : OpenPartialHomeomorph L₁ ℂ)
    (h h' : OpenPartialHomeomorph L₀ L₁) (x : L₀) (hx : x ∈ c.source)
    (he : h =ᶠ[𝓝 x] h') :
    schwarzianQuadraticAt c h d x = schwarzianQuadraticAt c h' d x := by
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv hx] using (c.symm.continuousAt (c.map_source hx)).tendsto
  have hcoord : affineLocalMapExpression c h d =ᶠ[𝓝 (c x)]
      affineLocalMapExpression c h' d := by
    filter_upwards [ht.eventually he] with z hz
    exact congrArg d hz
  unfold schwarzianQuadraticAt schwarzian
  rw [hcoord.deriv.eq_of_nhds, hcoord.deriv.deriv.eq_of_nhds,
    hcoord.deriv.deriv.deriv.eq_of_nhds]


private theorem schwarzian_quadratic_chain_germ_g12
    [IsManifold (complexModel 1) ∞ L₀] [IsManifold (complexModel 1) ∞ L₁]
    {L₂ : Type w} [TopologicalSpace L₂] [ChartedSpace (ComplexModel 1) L₂]
    [IsManifold (complexModel 1) ∞ L₂]
    (A₀ : ComplexAffineStructure L₀) (A₁ : ComplexAffineStructure L₁)
    (A₂ : ComplexAffineStructure L₂)
    (h : OpenPartialHomeomorph L₀ L₁) (g : OpenPartialHomeomorph L₁ L₂)
    (k : OpenPartialHomeomorph L₀ L₂)
    (hh : IsHolomorphicCurveLocalMap h) (hg : IsHolomorphicCurveLocalMap g)
    (c : OpenPartialHomeomorph L₀ ℂ) (d : OpenPartialHomeomorph L₁ ℂ)
    (e : OpenPartialHomeomorph L₂ ℂ)
    (hc : c ∈ A₀.maximalAtlas L₀) (hd : d ∈ A₁.maximalAtlas L₁)
    (he : e ∈ A₂.maximalAtlas L₂)
    (x : L₀) (hxc : x ∈ c.source) (hxh : x ∈ h.source)
    (hxd : h x ∈ d.source) (hxg : h x ∈ g.source) (hxe : g (h x) ∈ e.source)
    (hk : k =ᶠ[𝓝 x] (g ∘ h)) :
    ∀ v : TangentSpace (complexModel 1) x,
      schwarzianQuadraticAt c k e x v = schwarzianQuadraticAt c h d x v +
        schwarzianQuadraticAt d g e (h x)
          (mfderiv (complexModel 1) (complexModel 1) h x v) := by
  have hkg : schwarzianQuadraticAt c k e x =
      schwarzianQuadraticAt c (h.trans g) e x :=
    schwarzian_quadratic_germ_g12 c e k (h.trans g) x hxc hk
  rw [hkg]
  exact ((schwarzian_affine_curve_calculus A₀ A₁ A₂ h hh c d hc hd x hxc hxh hxd).2.2.2.2.2.2
    g e hg he hxg hxe).2

private theorem schwarzian_quadratic_identity_germ_g12
    (A : ComplexAffineStructure L₀)
    (c d : OpenPartialHomeomorph L₀ ℂ)
    (hc : c ∈ A.maximalAtlas L₀) (hd : d ∈ A.maximalAtlas L₀)
    (h : OpenPartialHomeomorph L₀ L₀) (x : L₀)
    (hxc : x ∈ c.source) (hxd : x ∈ d.source)
    (hh : h =ᶠ[𝓝 x] id) :
    schwarzianQuadraticAt c h d x = 0 := by
  exact (schwarzian_quadratic_germ_g12 c d h (OpenPartialHomeomorph.refl L₀) x hxc hh).trans
    (schwarzian_quadratic_identity A c d hc hd x hxc hxd)

private theorem cocycle_diam_g12 {J : Type*} (a b : J → ℂ) (c : ℂ)
    (hab : ∀ z, a z = c + b z) (Ω : Set J) :
    Metric.diam (a '' Ω) = Metric.diam (b '' Ω) := by
  have heq : a '' Ω = (fun z : ℂ ↦ c + z) '' (b '' Ω) := by
    rw [Set.image_image]
    congr 1
    exact funext hab
  rw [heq]
  exact (show Isometry (fun z : ℂ ↦ c + z) from
    fun x y ↦ by simp only [edist_dist, dist_add_left]).diam_image _


private theorem schwarzian_quadratic_affine_naturality_g12
    [IsManifold (complexModel 1) ∞ L₀] [IsManifold (complexModel 1) ∞ L₁]
    {L₀' : Type w} {L₁' : Type u}
    [TopologicalSpace L₀'] [TopologicalSpace L₁']
    [ChartedSpace (ComplexModel 1) L₀'] [ChartedSpace (ComplexModel 1) L₁']
    [IsManifold (complexModel 1) ∞ L₀'] [IsManifold (complexModel 1) ∞ L₁']
    (A₀ : ComplexAffineStructure L₀) (A₁ : ComplexAffineStructure L₁)
    (A₀' : ComplexAffineStructure L₀') (A₁' : ComplexAffineStructure L₁')
    (h : OpenPartialHomeomorph L₀ L₁) (h' : OpenPartialHomeomorph L₀' L₁')
    (k : OpenPartialHomeomorph L₀ L₀') (k' : OpenPartialHomeomorph L₁ L₁')
    (hh : IsHolomorphicCurveLocalMap h) (hh' : IsHolomorphicCurveLocalMap h')
    (hk : IsHolomorphicCurveLocalMap k) (hk' : IsHolomorphicCurveLocalMap k')
    (c : OpenPartialHomeomorph L₀ ℂ) (e : OpenPartialHomeomorph L₁ ℂ)
    (c' : OpenPartialHomeomorph L₀' ℂ) (e' : OpenPartialHomeomorph L₁' ℂ)
    (hc : c ∈ A₀.maximalAtlas _) (he : e ∈ A₁.maximalAtlas _)
    (hc' : c' ∈ A₀'.maximalAtlas _) (he' : e' ∈ A₁'.maximalAtlas _)
    (x : L₀) (hxc : x ∈ c.source) (hxh : x ∈ h.source) (hxk : x ∈ k.source)
    (hxe : h x ∈ e.source) (hxk' : h x ∈ k'.source)
    (hxc' : k x ∈ c'.source) (hxh' : k x ∈ h'.source)
    (hxe' : k' (h x) ∈ e'.source) (hpoint : h' (k x) = k' (h x))
    (hsquare : (k' ∘ h) =ᶠ[𝓝 x] (h' ∘ k))
    (haffine : ∃ a : ComplexAffineTransformation,
      ∀ᶠ z in 𝓝 (c x), affineLocalMapExpression c k c' z = a.apply z)
    (haffine' : ∃ a : ComplexAffineTransformation,
      ∀ᶠ z in 𝓝 (e (h x)), affineLocalMapExpression e k' e' z = a.apply z) :
    ∀ v : TangentSpace (complexModel 1) x,
      schwarzianQuadraticAt c' h' e' (k x)
        (mfderiv (complexModel 1) (complexModel 1) k x v) =
      schwarzianQuadraticAt c h e x v := by
  have hkzero := (schwarzian_affine_curve_calculus A₀ A₀' A₁' k hk
    c c' hc hc' x hxc hxk hxc').2.2.2.2.2.1 haffine
  have hk'zero := (schwarzian_affine_curve_calculus A₁ A₁' A₁' k' hk'
    e e' he he' (h x) hxe hxk' hxe').2.2.2.2.2.1 haffine'
  have htop := (schwarzian_affine_curve_calculus A₀ A₁ A₁' h hh
    c e hc he x hxc hxh hxe).2.2.2.2.2.2 k' e' hk' he' hxk' hxe'
  have hbottom := (schwarzian_affine_curve_calculus A₀ A₀' A₁' k hk
    c c' hc hc' x hxc hxk hxc').2.2.2.2.2.2 h' e' hh' he' hxh'
      (by rwa [hpoint])
  have hsame := schwarzian_quadratic_germ_g12 c e' (h.trans k') (k.trans h') x hxc hsquare
  intro v
  have ht := htop.2 v
  have hb := hbottom.2 v
  rw [hk'zero, zero_apply, add_zero] at ht
  rw [hkzero, zero_apply, zero_add] at hb
  exact hb.symm.trans ((congrArg (fun Q ↦ Q v) hsame).symm.trans ht)


end CurveCalculus

section OriginalLeaves
variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  (f : Biholomorph d d M M) (AD : AnosovDatum f)
  (P : AnosovIntrinsicFoliationPresentation f AD)

/-- The point-preserving biholomorphism between intrinsic unstable leaves with equal quotient
labels. -/
def unstableLeafLabelBiholomorph_g17 :
    letI := P.realCharts
    ∀ (q q' : Quotient P.foliations.unstablePartition), q = q' →
      letI := P.foliations.unstableTopology q
      letI := P.foliations.unstableTopology q'
      letI := P.complexLeaves.charts q
      letI := P.complexLeaves.charts q'
      Biholomorph 1 1 (IntrinsicFoliationLeaf P.foliations.unstablePartition q)
        (IntrinsicFoliationLeaf P.foliations.unstablePartition q') := by
  letI := P.realCharts
  intro q q' h
  subst q'
  letI := P.foliations.unstableTopology q
  letI := P.complexLeaves.charts q
  exact Diffeomorph.refl _ _ ∞

omit [CompactSpace M] in
@[simp] theorem unstableLeafLabelBiholomorph_g17_val :
    letI := P.realCharts
    ∀ (q q' : Quotient P.foliations.unstablePartition) (h : q = q')
      (z : IntrinsicFoliationLeaf P.foliations.unstablePartition q),
      (unstableLeafLabelBiholomorph_g17 f AD P q q' h z).val = z.val := by
  letI := P.realCharts
  intro q q' h z
  subst q'
  rfl

omit [CompactSpace M] in
private theorem native_unstable_transport_derivative_g12 :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ x : M, ∃ E : Biholomorph 1 1 (P.foliations.ULeaf x)
      (P.foliations.ULeaf (f x)),
      (∀ z, (E z).val = f z.val) ∧
      ∀ v : TangentSpace (complexModel 1) (P.foliations.uPoint x),
        mfderiv (complexModel 1) (complexModel d)
          (Subtype.val : P.foliations.ULeaf (f x) → M)
          (P.foliations.uPoint (f x))
          (mfderiv (complexModel 1) (complexModel 1) E (P.foliations.uPoint x) v) =
        mfderiv (complexModel d) (complexModel d) f x
          (mfderiv (complexModel 1) (complexModel d)
            (Subtype.val : P.foliations.ULeaf x → M) (P.foliations.uPoint x) v) := by
  letI := P.realCharts
  letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  letI : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
  intro x
  obtain ⟨E, hE⟩ := intrinsicUnstable_transport_biholomorph_g5 f AD P x
  refine ⟨E, hE, ?_⟩
  have hpoint : E (P.foliations.uPoint x) = P.foliations.uPoint (f x) :=
    Subtype.ext (hE _)
  have heq : (Subtype.val : P.foliations.ULeaf (f x) → M) ∘ E =
      f ∘ (Subtype.val : P.foliations.ULeaf x → M) := funext hE
  have hd := mfderiv_congr (I := complexModel 1) (I' := complexModel d)
    (x := P.foliations.uPoint x) heq
  rw [mfderiv_comp _ ((P.unstable_holomorphic _).mdifferentiable (by simp) _)
    (E.contMDiff.mdifferentiable (by simp) _),
    mfderiv_comp _ (f.contMDiff.mdifferentiable (by simp) _)
      ((P.unstable_holomorphic _).mdifferentiable (by simp) _)] at hd
  rw [hpoint] at hd
  intro v
  exact congrArg (fun T : ComplexModel 1 →L[ℂ] ComplexModel d ↦ T v) hd


omit [CompactSpace M] in
private theorem native_stable_transport_g12 :
    letI := P.realCharts
    ∀ q : Quotient P.foliations.stablePartition,
    letI := P.foliations.stableTopology q
    ∃ q' : Quotient P.foliations.stablePartition,
    letI := P.foliations.stableTopology q'
    ∃ es : IntrinsicFoliationLeaf P.foliations.stablePartition q ≃ₜ
      IntrinsicFoliationLeaf P.foliations.stablePartition q',
      ∀ x, (es x).val = f x.val := by
  letI := P.realCharts
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    exact ⟨Quotient.mk P.foliations.stablePartition (f x),
      stableLeafHomeomorph_g9 P x⟩


omit [CompactSpace M] in
private theorem native_leaf_transport_family_g12 :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ (q q' : Quotient P.foliations.stablePartition)
      (es : IntrinsicFoliationLeaf P.foliations.stablePartition q →
        IntrinsicFoliationLeaf P.foliations.stablePartition q'),
      (∀ x, (es x).val = f x.val) →
    ∃ Φ : ∀ x : IntrinsicFoliationLeaf P.foliations.stablePartition q,
      Biholomorph 1 1 (P.foliations.ULeaf x.val) (P.foliations.ULeaf (es x).val),
      (∀ x z, (Φ x z).val = f z.val) ∧
      ∀ x (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
        mfderiv (complexModel 1) (complexModel d)
          (Subtype.val : P.foliations.ULeaf (es x).val → M)
          (P.foliations.uPoint (es x).val)
          (mfderiv (complexModel 1) (complexModel 1) (Φ x) (P.foliations.uPoint x.val) v) =
        mfderiv (complexModel d) (complexModel d) f x.val
          (mfderiv (complexModel 1) (complexModel d)
            (Subtype.val : P.foliations.ULeaf x.val → M) (P.foliations.uPoint x.val) v) := by
  letI := P.realCharts
  letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  intro q q' es hes
  have hfam (x : IntrinsicFoliationLeaf P.foliations.stablePartition q) :
      ∃ E : Biholomorph 1 1 (P.foliations.ULeaf x.val) (P.foliations.ULeaf (es x).val),
      (∀ z, (E z).val = f z.val) ∧
      ∀ v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val),
        mfderiv (complexModel 1) (complexModel d)
          (Subtype.val : P.foliations.ULeaf (es x).val → M)
          (P.foliations.uPoint (es x).val)
          (mfderiv (complexModel 1) (complexModel 1) E (P.foliations.uPoint x.val) v) =
        mfderiv (complexModel d) (complexModel d) f x.val
          (mfderiv (complexModel 1) (complexModel d)
            (Subtype.val : P.foliations.ULeaf x.val → M) (P.foliations.uPoint x.val) v) := by
    rw [hes x]
    exact native_unstable_transport_derivative_g12 f AD P x.val
  choose Φ hΦ hdΦ using hfam
  exact ⟨Φ, hΦ, hdΦ⟩

omit [CompactSpace M] in
private theorem native_quadratic_family_g12 :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    letI : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves)
      (q : Quotient P.foliations.stablePartition),
    let L := IntrinsicFoliationLeaf P.foliations.stablePartition q
    ∀ H : ∀ x y : L, PointedLeafHomeomorph P.foliations x.val y.val,
      (∀ x y, IsHolomorphicCurveLocalMap (H x y).map) →
      (∀ x y z, (H x z).map =ᶠ[𝓝 (P.foliations.uPoint x.val)]
        ((H y z).map ∘ (H x y).map)) →
      (∀ x, (H x x).map =ᶠ[𝓝 (P.foliations.uPoint x.val)] id) →
    ∃ Q : ∀ x _y : L, QuadraticForm ℂ
        (TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
      (∀ (x y : L) (c : OpenPartialHomeomorph (P.foliations.ULeaf x.val) ℂ)
        (e : OpenPartialHomeomorph (P.foliations.ULeaf y.val) ℂ),
        c ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves x.val) →
        e ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves y.val) →
        P.foliations.uPoint x.val ∈ c.source → P.foliations.uPoint y.val ∈ e.source →
        Q x y = schwarzianQuadraticAt c (H x y).map e (P.foliations.uPoint x.val)) ∧
      (∀ (x y z : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
        Q x z v = Q x y v + Q y z
          (mfderiv (complexModel 1) (complexModel 1) (H x y).map
            (P.foliations.uPoint x.val) v)) ∧
      (∀ x : L, Q x x = 0) ∧
      (∀ (x y : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val))
        (Ω : Set L),
        Metric.diam ((fun z : L ↦ Q x z v) '' Ω) =
          Metric.diam ((fun z : L ↦ Q y z
            (mfderiv (complexModel 1) (complexModel 1) (H x y).map
              (P.foliations.uPoint x.val) v)) '' Ω)) ∧
      (∀ (x y : L) (lam : ℂ)
        (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
        Q x y (lam • v) = lam ^ 2 * Q x y v) := by
  letI := P.realCharts
  letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  letI : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
  intro A q L H hhol hcomp hid
  let Ap (x : L) := A.atPoint P.foliations P.complexLeaves x.val
  have hQ (x y : L) := schwarzian_quadratic_exists_g12 (Ap x) (Ap y)
    (H x y).map (hhol x y) (P.foliations.uPoint x.val) (H x y).source_point
  choose Q hQ using hQ
  have hformula (x y : L) (c : OpenPartialHomeomorph (P.foliations.ULeaf x.val) ℂ)
      (e : OpenPartialHomeomorph (P.foliations.ULeaf y.val) ℂ)
      (hc : c ∈ (Ap x).maximalAtlas _) (he : e ∈ (Ap y).maximalAtlas _)
      (hxc : P.foliations.uPoint x.val ∈ c.source)
      (hye : P.foliations.uPoint y.val ∈ e.source) :
      Q x y = schwarzianQuadraticAt c (H x y).map e (P.foliations.uPoint x.val) := by
    apply hQ x y c e hc he hxc
    rwa [(H x y).map_point]
  have hcocycle (x y z : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)) :
      Q x z v = Q x y v + Q y z
        (mfderiv (complexModel 1) (complexModel 1) (H x y).map (P.foliations.uPoint x.val) v) := by
    obtain ⟨c,hc,hxc⟩ := affine_chart_at_g12 (Ap x) (P.foliations.uPoint x.val)
    obtain ⟨e,he,hye⟩ := affine_chart_at_g12 (Ap y) (P.foliations.uPoint y.val)
    obtain ⟨k,hk,hzk⟩ := affine_chart_at_g12 (Ap z) (P.foliations.uPoint z.val)
    rw [hformula x z c k hc hk hxc hzk, hformula x y c e hc he hxc hye,
      hformula y z e k he hk hye hzk]
    have hchain := schwarzian_quadratic_chain_germ_g12 (Ap x) (Ap y) (Ap z)
      (H x y).map (H y z).map (H x z).map (hhol x y) (hhol y z)
      c e k hc he hk (P.foliations.uPoint x.val) hxc (H x y).source_point
      (by rwa [(H x y).map_point])
      (by rw [(H x y).map_point]; exact (H y z).source_point)
      (by rwa [(H x y).map_point, (H y z).map_point]) (hcomp x y z) v
    rwa [(H x y).map_point] at hchain
  refine ⟨Q, hformula, hcocycle, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨c,hc,hxc⟩ := affine_chart_at_g12 (Ap x) (P.foliations.uPoint x.val)
    rw [hformula x x c c hc hc hxc hxc]
    exact schwarzian_quadratic_identity_germ_g12 (Ap x) c c hc hc
      (H x x).map (P.foliations.uPoint x.val) hxc hxc (hid x)
  · intro x y v Ω
    exact cocycle_diam_g12 _ _ (Q x y v) (fun z ↦ hcocycle x y z v) Ω
  · intro x y lam v
    simpa only [smul_eq_mul, pow_two] using (Q x y).map_smul lam v

omit [CompactSpace M] in
private theorem native_affine_transport_expression_g12 :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      A.ActsAffinely P.foliations P.complexLeaves f →
    ∀ (x : M) (E : Biholomorph 1 1 (P.foliations.ULeaf x) (P.foliations.ULeaf (f x))),
      (∀ z, (E z).val = f z.val) →
    ∀ (c : OpenPartialHomeomorph (P.foliations.ULeaf x) ℂ)
      (e : OpenPartialHomeomorph (P.foliations.ULeaf (f x)) ℂ),
      c ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves x) →
      e ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves (f x)) →
      P.foliations.uPoint x ∈ c.source → P.foliations.uPoint (f x) ∈ e.source →
    ∃ a : ComplexAffineTransformation,
      ∀ᶠ z in 𝓝 (c (P.foliations.uPoint x)),
        affineLocalMapExpression c E.toHomeomorph.toOpenPartialHomeomorph e z = a.apply z := by
  letI := P.realCharts
  letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  intro A hA x E hE c e hc he hxc hxe
  obtain ⟨a, ha⟩ := hA x c e hc he hxc hxe
  refine ⟨a, ?_⟩
  have ht : Tendsto c.symm (𝓝 (c (P.foliations.uPoint x))) (𝓝 (P.foliations.uPoint x)) := by
    simpa only [c.left_inv hxc] using (c.symm.continuousAt (c.map_source hxc)).tendsto
  filter_upwards [ht.eventually ha, c.open_target.mem_nhds (c.map_source hxc)] with z hz hzt
  obtain ⟨hzc, w, hw, hwe, heq⟩ := hz
  have hwE : w = E (c.symm z) := Subtype.ext (hw.trans (hE _).symm)
  change e (E (c.symm z)) = a.apply z
  rw [← hwE, heq, c.right_inv hzt]

omit [CompactSpace M] in
private theorem native_schwarzian_transport_g12 :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    letI : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      A.ActsAffinely P.foliations P.complexLeaves f →
    ∀ (x y x' y' : M) (_hx' : x' = f x) (_hy' : y' = f y)
      (h : PointedLeafHomeomorph P.foliations x y)
      (h' : PointedLeafHomeomorph P.foliations x' y')
      (E : Biholomorph 1 1 (P.foliations.ULeaf x) (P.foliations.ULeaf x'))
      (E' : Biholomorph 1 1 (P.foliations.ULeaf y) (P.foliations.ULeaf y')),
      (∀ z, (E z).val = f z.val) → (∀ z, (E' z).val = f z.val) →
      IsHolomorphicCurveLocalMap h.map → IsHolomorphicCurveLocalMap h'.map →
      (E' ∘ h.map) =ᶠ[𝓝 (P.foliations.uPoint x)] (h'.map ∘ E) →
    ∀ (c : OpenPartialHomeomorph (P.foliations.ULeaf x) ℂ)
      (e : OpenPartialHomeomorph (P.foliations.ULeaf y) ℂ)
      (c' : OpenPartialHomeomorph (P.foliations.ULeaf x') ℂ)
      (e' : OpenPartialHomeomorph (P.foliations.ULeaf y') ℂ),
      c ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves x) →
      e ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves y) →
      c' ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves x') →
      e' ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves y') →
      P.foliations.uPoint x ∈ c.source → P.foliations.uPoint y ∈ e.source →
      P.foliations.uPoint x' ∈ c'.source → P.foliations.uPoint y' ∈ e'.source →
    ∀ v : TangentSpace (complexModel 1) (P.foliations.uPoint x),
      schwarzianQuadraticAt c' h'.map e' (P.foliations.uPoint x')
        (mfderiv (complexModel 1) (complexModel 1) E (P.foliations.uPoint x) v) =
      schwarzianQuadraticAt c h.map e (P.foliations.uPoint x) v := by
  letI := P.realCharts
  letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  letI : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
  intro A hA x y x' y' hx' hy'
  subst x'
  subst y'
  intro h h' E E' hE hE' hh hh' hsquare c e c' e' hc he hc' he' hxc hye hxc' hye' v
  have hpoint : E (P.foliations.uPoint x) = P.foliations.uPoint (f x) :=
    Subtype.ext (hE _)
  have hpoint' : E' (P.foliations.uPoint y) = P.foliations.uPoint (f y) :=
    Subtype.ext (hE' _)
  have hk : IsHolomorphicCurveLocalMap E.toHomeomorph.toOpenPartialHomeomorph :=
    ⟨E.contMDiff.contMDiffOn, E.symm.contMDiff.contMDiffOn⟩
  have hk' : IsHolomorphicCurveLocalMap E'.toHomeomorph.toOpenPartialHomeomorph :=
    ⟨E'.contMDiff.contMDiffOn, E'.symm.contMDiff.contMDiffOn⟩
  have ha := native_affine_transport_expression_g12 f AD P A hA x E hE c c' hc hc' hxc hxc'
  have ha' := native_affine_transport_expression_g12 f AD P A hA y E' hE' e e' he he' hye hye'
  have hresult := schwarzian_quadratic_affine_naturality_g12
    (A.atPoint P.foliations P.complexLeaves x) (A.atPoint P.foliations P.complexLeaves y)
    (A.atPoint P.foliations P.complexLeaves (f x)) (A.atPoint P.foliations P.complexLeaves (f y))
    h.map h'.map E.toHomeomorph.toOpenPartialHomeomorph E'.toHomeomorph.toOpenPartialHomeomorph
    hh hh' hk hk' c e c' e' hc he hc' he' (P.foliations.uPoint x) hxc h.source_point
    (Set.mem_univ _) (by rwa [h.map_point]) (Set.mem_univ _)
    (by change E (P.foliations.uPoint x) ∈ c'.source; rwa [hpoint])
    (by change E (P.foliations.uPoint x) ∈ h'.map.source; rw [hpoint]; exact h'.source_point)
    (by change E' (h.map (P.foliations.uPoint x)) ∈ e'.source; rwa [h.map_point, hpoint'])
    (by change h'.map (E (P.foliations.uPoint x)) = E' (h.map (P.foliations.uPoint x));
        rw [hpoint, h.map_point, h'.map_point, hpoint'])
    hsquare ha (by simpa only [h.map_point] using ha') v
  change schwarzianQuadraticAt c' h'.map e' (E (P.foliations.uPoint x))
    (mfderiv (complexModel 1) (complexModel 1) E (P.foliations.uPoint x) v) = _ at hresult
  rwa [hpoint] at hresult


private theorem centered_unstable_coordinates_g12
    (hRank : HasComplexRankOne AD.splitting.unstable.toDistribution) :
    letI := P.realCharts
    ∃ φ : ∀ x : M, P.foliations.ULeaf x ≃ₜ ℂ,
      ∀ x, φ x (P.foliations.uPoint x) = 0 := by
  letI := P.realCharts
  obtain ⟨A, _, _, _, hcomplete⟩ := proposition31_affine_family f AD hRank P
  have he (x : M) : ∃ e : P.foliations.ULeaf x ≃ₜ ℂ,
      e (P.foliations.uPoint x) = 0 := by
    letI := P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    obtain ⟨D, _⟩ := (hcomplete (Quotient.mk P.foliations.unstablePartition x)).2
    exact ⟨D.toHomeomorph.trans (Homeomorph.subRight (D (P.foliations.uPoint x))), by simp⟩
  choose φ hφ using he
  exact ⟨φ, hφ⟩


/-- Stable holonomy on a simply connected intrinsic stable leaf determines a Schwarzian quadratic
cocycle satisfying the composition, diameter, scalar homogeneity, and dynamical equivariance
laws. Its unstable derivative agrees with the ambient derivative through the leaf inclusions
(Ghys, §4, pp. 594–595; Prop. 3.1). -/
theorem native_schwarzian_leaf_cocycle_provider :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    letI : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
    ∀
    (_hRank : HasComplexRankOne AD.splitting.unstable.toDistribution)
    (A : AffineUnstableLeafStructures P.foliations P.complexLeaves)
    (_hAffine : A.ActsAffinely P.foliations P.complexLeaves f)
    (_hContinuous : A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves),
    ∀ q : Quotient P.foliations.stablePartition,
    letI := P.foliations.stableTopology q
    let L := IntrinsicFoliationLeaf P.foliations.stablePartition q
    SimplyConnectedSpace L →
    ∃ q' : Quotient P.foliations.stablePartition,
    letI := P.foliations.stableTopology q'
    let L' := IntrinsicFoliationLeaf P.foliations.stablePartition q'
    ∃ es : L ≃ₜ L', (∀ x : L, (es x).val = f x.val) ∧
    ∃ (H : ∀ x y : L, PointedLeafHomeomorph P.foliations x.val y.val)
      (H' : ∀ x y : L', PointedLeafHomeomorph P.foliations x.val y.val)
      (Q : ∀ x _y : L, QuadraticForm ℂ
        (TangentSpace (complexModel 1) (P.foliations.uPoint x.val)))
      (Q' : ∀ x _y : L', QuadraticForm ℂ
        (TangentSpace (complexModel 1) (P.foliations.uPoint x.val))),
      (∀ (x y : L) (γ : Path x y), ∃ C : LocalHolonomyContinuation P.foliations γ,
        (Filter.Germ.ofFun (H (γ 0) (γ 1)).map :
          Filter.Germ (𝓝 (P.foliations.uPoint (γ 0).val)) (P.foliations.ULeaf (γ 1).val)) =
        Filter.Germ.ofFun (C.representative 0 1 (show (0 : unitInterval) ≤ 1 from bot_le)).map) ∧
      (∀ (x y : L) (γ : Path x y) (e : PathHolonomyRepresentative P.foliations γ 0 1),
        (Filter.Germ.ofFun (H (γ 0) (γ 1)).map :
          Filter.Germ (𝓝 (P.foliations.uPoint (γ 0).val)) (P.foliations.ULeaf (γ 1).val)) =
        Filter.Germ.ofFun e.map) ∧
      (∀ (x y : L') (γ : Path x y), ∃ C : LocalHolonomyContinuation P.foliations γ,
        (Filter.Germ.ofFun (H' (γ 0) (γ 1)).map :
          Filter.Germ (𝓝 (P.foliations.uPoint (γ 0).val)) (P.foliations.ULeaf (γ 1).val)) =
        Filter.Germ.ofFun (C.representative 0 1 (show (0 : unitInterval) ≤ 1 from bot_le)).map) ∧
      (∀ (x y : L') (γ : Path x y) (e : PathHolonomyRepresentative P.foliations γ 0 1),
        (Filter.Germ.ofFun (H' (γ 0) (γ 1)).map :
          Filter.Germ (𝓝 (P.foliations.uPoint (γ 0).val)) (P.foliations.ULeaf (γ 1).val)) =
        Filter.Germ.ofFun e.map) ∧
      (∀ x y : L, IsHolomorphicCurveLocalMap (H x y).map) ∧
      (∀ x y : L', IsHolomorphicCurveLocalMap (H' x y).map) ∧
      (∀ (x y : L) (c : OpenPartialHomeomorph (P.foliations.ULeaf x.val) ℂ)
        (e : OpenPartialHomeomorph (P.foliations.ULeaf y.val) ℂ),
        c ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves x.val) →
        e ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves y.val) →
        P.foliations.uPoint x.val ∈ c.source → P.foliations.uPoint y.val ∈ e.source →
        Q x y = schwarzianQuadraticAt c (H x y).map e (P.foliations.uPoint x.val)) ∧
      (∀ (x y : L') (c : OpenPartialHomeomorph (P.foliations.ULeaf x.val) ℂ)
        (e : OpenPartialHomeomorph (P.foliations.ULeaf y.val) ℂ),
        c ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves x.val) →
        e ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint P.foliations P.complexLeaves y.val) →
        P.foliations.uPoint x.val ∈ c.source → P.foliations.uPoint y.val ∈ e.source →
        Q' x y = schwarzianQuadraticAt c (H' x y).map e (P.foliations.uPoint x.val)) ∧
      (∀ (x y z : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
        Q x z v = Q x y v + Q y z
          (mfderiv (complexModel 1) (complexModel 1) (H x y).map
            (P.foliations.uPoint x.val) v)) ∧
      (∀ x : L, Q x x = 0) ∧
      (∀ (x y : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val))
        (Ω : Set L), IsCompact Ω →
        Metric.diam ((fun z : L ↦ Q x z v) '' Ω) =
          Metric.diam ((fun z : L ↦ Q y z
            (mfderiv (complexModel 1) (complexModel 1) (H x y).map
              (P.foliations.uPoint x.val) v)) '' Ω)) ∧
      (∀ (x y : L) (lam : ℂ)
        (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
        Q x y (lam • v) = lam ^ 2 * Q x y v) ∧
      ∃ Φ : ∀ x : L, Biholomorph 1 1
        (P.foliations.ULeaf x.val) (P.foliations.ULeaf (es x).val),
        (∀ (x : L) (z : P.foliations.ULeaf x.val), (Φ x z).val = f z.val) ∧
        (∀ (x y : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
          Q' (es x) (es y)
            (mfderiv (complexModel 1) (complexModel 1) (Φ x)
              (P.foliations.uPoint x.val) v) = Q x y v) ∧
        (∀ (x : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)),
          mfderiv (complexModel 1) (complexModel d)
              (Subtype.val : P.foliations.ULeaf (es x).val → M)
              (P.foliations.uPoint (es x).val)
              (mfderiv (complexModel 1) (complexModel 1) (Φ x)
                (P.foliations.uPoint x.val) v) =
            mfderiv (complexModel d) (complexModel d) f x.val
              (mfderiv (complexModel 1) (complexModel d)
                (Subtype.val : P.foliations.ULeaf x.val → M)
                (P.foliations.uPoint x.val) v))  := by
  classical
  letI := P.realCharts
  letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  letI : ∀ x : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.complex_manifold (Quotient.mk P.foliations.unstablePartition x)
  intro hRank A hAffine hContinuous q
  letI := P.foliations.stableTopology q
  dsimp only
  intro hsc
  letI := hsc
  obtain ⟨φ,hφ⟩ := centered_unstable_coordinates_g12 f AD P hRank
  have hsleaf := native_stable_transport_g12 f AD P
  obtain ⟨q',es,hes⟩ := hsleaf q
  letI := P.foliations.stableTopology q'
  letI : SimplyConnectedSpace (IntrinsicFoliationLeaf P.foliations.stablePartition q') :=
    es.symm.toHomotopyEquiv.simplyConnectedSpace
  let L := IntrinsicFoliationLeaf P.foliations.stablePartition q
  let L' := IntrinsicFoliationLeaf P.foliations.stablePartition q'
  let H : ∀ x y : L, PointedLeafHomeomorph P.foliations x.val y.val := endpointHolonomy_g12 P.foliations
  let H' : ∀ x y : L', PointedLeafHomeomorph P.foliations x.val y.val := endpointHolonomy_g12 P.foliations
  have hol (qq : Quotient P.foliations.stablePartition)
      [SimplyConnectedSpace (IntrinsicFoliationLeaf P.foliations.stablePartition qq)]
      (x y : IntrinsicFoliationLeaf P.foliations.stablePartition qq) :
      IsHolomorphicCurveLocalMap (endpointHolonomy_g12 P.foliations x y).map := by
    apply endpointHolonomy_holomorphic_g12 P.foliations
    intro a b γ e
    exact path_holonomy_representative_holomorphic_g12 f AD P hRank γ 0 1 e
  have comp (qq : Quotient P.foliations.stablePartition)
      [SimplyConnectedSpace (IntrinsicFoliationLeaf P.foliations.stablePartition qq)]
      (x y z : IntrinsicFoliationLeaf P.foliations.stablePartition qq) :
      (endpointHolonomy_g12 P.foliations x z).map =ᶠ[𝓝 (P.foliations.uPoint x.val)]
        (endpointHolonomy_g12 P.foliations y z).map ∘ (endpointHolonomy_g12 P.foliations x y).map :=
    normLeafMap_reflect_comp_g12 P.foliations φ hφ _ _ _
      (endpointHolonomy_composition_norm_g12 P.foliations φ hφ x y z)
  have hid (qq : Quotient P.foliations.stablePartition)
      [SimplyConnectedSpace (IntrinsicFoliationLeaf P.foliations.stablePartition qq)]
      (x : IntrinsicFoliationLeaf P.foliations.stablePartition qq) :
      (endpointHolonomy_g12 P.foliations x x).map =ᶠ[𝓝 (P.foliations.uPoint x.val)] id :=
    normLeafMap_reflect_identity_g12 P.foliations φ hφ _
      (endpointHolonomy_identity_norm_g12 P.foliations φ hφ x)
  have rep (qq : Quotient P.foliations.stablePartition)
      [SimplyConnectedSpace (IntrinsicFoliationLeaf P.foliations.stablePartition qq)]
      (x y : IntrinsicFoliationLeaf P.foliations.stablePartition qq) (γ : Path x y)
      (e : PathHolonomyRepresentative P.foliations γ 0 1) :
      (Germ.ofFun (endpointHolonomy_g12 P.foliations (γ 0) (γ 1)).map :
        Germ (𝓝 (P.foliations.uPoint (γ 0).val)) (P.foliations.ULeaf (γ 1).val)) = Germ.ofFun e.map :=
    Germ.coe_eq.mpr (normLeafMap_reflect_g12 P.foliations φ hφ _ _
      (endpointHolonomy_representative_norm_g12 P.foliations φ hφ γ e))
  obtain ⟨Q,hQ,hcocycle,hdiag,hdiam,hsmul⟩ :=
    native_quadratic_family_g12 f AD P A q H (hol q) (comp q) (hid q)
  obtain ⟨Q',hQ',_,_,_,_⟩ :=
    native_quadratic_family_g12 f AD P A q' H' (hol q') (comp q') (hid q')
  obtain ⟨Φ,hΦ,hdΦ⟩ := native_leaf_transport_family_g12 f AD P q q' es hes
  have hconj (x y : L) :
      (Φ y ∘ (H x y).map) =ᶠ[𝓝 (P.foliations.uPoint x.val)]
        ((H' (es x) (es y)).map ∘ Φ x) :=
    endpointHolonomy_equivariant_g12 P.foliations φ hφ f f.continuous hsleaf
      es es.continuous hes (fun z ↦ (Φ z).toHomeomorph) hΦ x y
  have hcov (x y : L) (v : TangentSpace (complexModel 1) (P.foliations.uPoint x.val)) :
      Q' (es x) (es y)
        (mfderiv (complexModel 1) (complexModel 1) (Φ x) (P.foliations.uPoint x.val) v) = Q x y v := by
    obtain ⟨c,hc,hxc⟩ := affine_chart_at_g12 (A.atPoint P.foliations P.complexLeaves x.val) (P.foliations.uPoint x.val)
    obtain ⟨e,he,hye⟩ := affine_chart_at_g12 (A.atPoint P.foliations P.complexLeaves y.val) (P.foliations.uPoint y.val)
    obtain ⟨c',hc',hxc'⟩ := affine_chart_at_g12 (A.atPoint P.foliations P.complexLeaves (es x).val) (P.foliations.uPoint (es x).val)
    obtain ⟨e',he',hye'⟩ := affine_chart_at_g12 (A.atPoint P.foliations P.complexLeaves (es y).val) (P.foliations.uPoint (es y).val)
    rw [hQ' (es x) (es y) c' e' hc' he' hxc' hye',hQ x y c e hc he hxc hye]
    exact native_schwarzian_transport_g12 f AD P A hAffine x.val y.val (es x).val (es y).val
      (hes x) (hes y) (H x y) (H' (es x) (es y)) (Φ x) (Φ y) (hΦ x) (hΦ y)
      (hol q x y) (hol q' (es x) (es y)) (hconj x y) c e c' e' hc he hc' he' hxc hye hxc' hye' v
  refine ⟨q',es,hes,H,H',Q,Q',?_,rep q,?_,rep q',hol q,hol q',hQ,hQ',hcocycle,hdiag,
    (fun x y v Ω _ ↦ hdiam x y v Ω),hsmul,Φ,hΦ,hcov,hdΦ⟩
  · intro x y γ
    obtain ⟨C⟩ := local_holonomy_continuation_exists_g9 P.foliations γ
    exact ⟨C,rep q x y γ (C.representative 0 1 zero_le_one)⟩
  · intro x y γ
    obtain ⟨C⟩ := local_holonomy_continuation_exists_g9 P.foliations γ
    exact ⟨C,rep q' x y γ (C.representative 0 1 zero_le_one)⟩


omit [CompactSpace M] in
/-- Every forward iterate of the Anosov map restricts to a biholomorphism between the corresponding
intrinsic unstable leaves. -/
theorem intrinsic_unstable_iterate_biholomorph_g17 :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ (n : ℕ) (x : M),
      ∃ E : Biholomorph 1 1 (P.foliations.ULeaf x)
          (P.foliations.ULeaf (((f : M → M)^[n]) x)),
        ∀ z, (E z).val = ((f : M → M)^[n]) z.val := by
  letI := P.realCharts
  letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  intro n
  induction n with
  | zero =>
    intro x
    exact ⟨Diffeomorph.refl _ _ ∞,fun _ ↦ rfl⟩
  | succ n ih =>
    intro x
    rw [Function.iterate_succ' (f : M → M) n]
    dsimp only [Function.comp_apply]
    obtain ⟨E,hE⟩ := ih x
    obtain ⟨E',hE'⟩ := intrinsicUnstable_transport_biholomorph_g5 f AD P
      (((f : M → M)^[n]) x)
    exact ⟨E.trans E',fun z ↦ (hE' (E z)).trans (congrArg f (hE z))⟩

omit [CompactSpace M] in
/-- Every forward iterate of the Anosov map restricts to a homeomorphism between the corresponding
intrinsic stable leaves. -/
theorem intrinsic_stable_iterate_homeomorph_g17 :
    letI := P.realCharts
    ∀ (n : ℕ) (x : M),
      let q := Quotient.mk P.foliations.stablePartition x
      let q' := Quotient.mk P.foliations.stablePartition (((f : M → M)^[n]) x)
      letI := P.foliations.stableTopology q
      letI := P.foliations.stableTopology q'
      ∃ E : IntrinsicFoliationLeaf P.foliations.stablePartition q ≃ₜ
          IntrinsicFoliationLeaf P.foliations.stablePartition q',
        ∀ z, (E z).val = ((f : M → M)^[n]) z.val := by
  letI := P.realCharts
  intro n
  induction n with
  | zero =>
    intro x
    letI := P.foliations.stableTopology (Quotient.mk P.foliations.stablePartition x)
    exact ⟨Homeomorph.refl _,fun _ ↦ rfl⟩
  | succ n ih =>
    intro x
    rw [Function.iterate_succ' (f : M → M) n]
    dsimp only [Function.comp_apply]
    letI := P.foliations.stableTopology (Quotient.mk P.foliations.stablePartition x)
    letI := P.foliations.stableTopology
      (Quotient.mk P.foliations.stablePartition (((f : M → M)^[n]) x))
    letI := P.foliations.stableTopology
      (Quotient.mk P.foliations.stablePartition (f (((f : M → M)^[n]) x)))
    obtain ⟨E,hE⟩ := ih x
    obtain ⟨E',hE'⟩ := stableLeafHomeomorph_g9 P (((f : M → M)^[n]) x)
    exact ⟨E.trans E',fun z ↦ (hE' (E z)).trans (congrArg f (hE z))⟩

omit [CompactSpace M] in
/-- An action that is affine in the specified unstable leaf structures remains affine under every
forward iterate. -/
theorem intrinsic_affine_action_iterate_g17 :
    letI := P.realCharts
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      A.ActsAffinely P.foliations P.complexLeaves f →
      ∀ n : ℕ, A.ActsAffinely P.foliations P.complexLeaves ((f : M → M)^[n]) := by
  letI := P.realCharts
  letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  intro A hA n
  induction n with
  | zero =>
    intro x c e hc he hxc hxe
    obtain ⟨b,hb⟩ := maximal_affine_charts_compatible_g1
      (A.atPoint P.foliations P.complexLeaves x) c e hc he
      (P.foliations.uPoint x) ⟨hxc,hxe⟩
    refine ⟨b,?_⟩
    filter_upwards [hb,c.open_source.mem_nhds hxc,e.open_source.mem_nhds hxe] with y hy hyc hye
    exact ⟨hyc,y,rfl,hye,hy⟩
  | succ n ih =>
    rw [Function.iterate_succ]
    intro x c e hc he hxc hxe
    obtain ⟨k,hk,hxk⟩ := affine_chart_at_g12
      (A.atPoint P.foliations P.complexLeaves (f x)) (P.foliations.uPoint (f x))
    obtain ⟨E,hE⟩ := intrinsicUnstable_transport_biholomorph_g5 f AD P x
    obtain ⟨b,hb⟩ := hA x c k hc hk hxc hxk
    obtain ⟨b',hb'⟩ := ih (f x) k e hk he hxk hxe
    have hpoint : E (P.foliations.uPoint x) = P.foliations.uPoint (f x) := Subtype.ext (hE _)
    have hnear := E.continuous.continuousAt.eventually (by rw [hpoint]; exact hb')
    refine ⟨⟨b'.slope * b.slope,mul_ne_zero b'.slope_ne_zero b.slope_ne_zero,
      b'.slope * b.translation + b'.translation⟩,?_⟩
    filter_upwards [hb,hnear] with y hy hy'
    obtain ⟨hyc,w,hw,_,hwk⟩ := hy
    obtain ⟨_,z,hz,hze,hzeg⟩ := hy'
    have hwE : w = E y := Subtype.ext (hw.trans (hE y).symm)
    refine ⟨hyc,z,?_,hze,?_⟩
    · simpa only [Function.comp_apply,hE] using hz
    · rw [hzeg,← hwE,hwk]
      simp only [ComplexAffineTransformation.apply]
      ring

omit [CompactSpace M] in
/-- A leaf map inducing an affine ambient action is affine as a germ at each point in the specified
unstable leaf structures. -/
theorem intrinsic_affine_action_germ_at_g17 :
    letI := P.realCharts
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves)
      (g : M → M), A.ActsAffinely P.foliations P.complexLeaves g →
      ∀ q q' : Quotient P.foliations.unstablePartition,
      letI := P.foliations.unstableTopology q
      letI := P.foliations.unstableTopology q'
      letI := P.complexLeaves.charts q
      letI := P.complexLeaves.charts q'
      ∀ (E : IntrinsicFoliationLeaf P.foliations.unstablePartition q →
        IntrinsicFoliationLeaf P.foliations.unstablePartition q'),
      (∀ z, (E z).val = g z.val) →
      ∀ (c : OpenPartialHomeomorph (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ℂ)
        (e : OpenPartialHomeomorph (IntrinsicFoliationLeaf P.foliations.unstablePartition q') ℂ),
      c ∈ (A.structureAt q).maximalAtlas _ → e ∈ (A.structureAt q').maximalAtlas _ →
      ∀ p, p ∈ c.source → E p ∈ e.source →
        ∃ b : ComplexAffineTransformation, ∀ᶠ z in 𝓝 p, e (E z) = b.apply (c z) := by
  letI := P.realCharts
  intro A g hA q q'
  letI := P.foliations.unstableTopology q
  letI := P.foliations.unstableTopology q'
  letI := P.complexLeaves.charts q
  letI := P.complexLeaves.charts q'
  intro E hE c e hc he p hpc hpe
  rcases p with ⟨x,hx⟩
  subst q
  have hq' : Quotient.mk P.foliations.unstablePartition (g x) = q' := by
    rw [← hE ⟨x,rfl⟩]
    exact (E ⟨x,rfl⟩).property
  subst q'
  have hpoint : E ⟨x,rfl⟩ = P.foliations.uPoint (g x) := Subtype.ext (hE _)
  obtain ⟨b,hb⟩ := hA x c e hc he hpc (by rwa [← hpoint])
  refine ⟨b,?_⟩
  filter_upwards [hb] with z hz
  obtain ⟨_,w,hw,_,heq⟩ := hz
  exact (congrArg e (Subtype.ext ((hE z).trans hw.symm))).trans heq

omit [CompactSpace M] in
/-- Pulling back a maximal affine chart by an intrinsic biholomorphism inducing an affine ambient
action gives a maximal affine chart of the source leaf. -/
theorem intrinsic_affine_pullback_chart_g17 :
    letI := P.realCharts
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves)
      (g : M → M), A.ActsAffinely P.foliations P.complexLeaves g →
      ∀ q q' : Quotient P.foliations.unstablePartition,
      letI := P.foliations.unstableTopology q
      letI := P.foliations.unstableTopology q'
      letI := P.complexLeaves.charts q
      letI := P.complexLeaves.charts q'
      ∀ (E : Biholomorph 1 1 (IntrinsicFoliationLeaf P.foliations.unstablePartition q)
        (IntrinsicFoliationLeaf P.foliations.unstablePartition q')),
      (∀ z, (E z).val = g z.val) →
      ∀ e : OpenPartialHomeomorph (IntrinsicFoliationLeaf P.foliations.unstablePartition q') ℂ,
      e ∈ (A.structureAt q').maximalAtlas _ →
      E.toHomeomorph.toOpenPartialHomeomorph.trans e ∈ (A.structureAt q).maximalAtlas _ := by
  letI := P.realCharts
  intro A g hA q q'
  letI := P.foliations.unstableTopology q
  letI := P.foliations.unstableTopology q'
  letI := P.complexLeaves.charts q
  letI := P.complexLeaves.charts q'
  intro E hE e he
  constructor
  · constructor
    · exact he.1.1.comp E.contMDiff.contMDiffOn (fun z hz ↦ hz.2)
    · exact E.symm.contMDiff.comp_contMDiffOn
        (he.1.2.mono (fun z hz ↦ hz.1))
  · intro c hc p hp
    have hcmax : c ∈ (A.structureAt q).maximalAtlas _ :=
      ⟨(A.structureAt q).out.holomorphic c hc,
        fun d hd ↦ (A.structureAt q).out.compatible d hd c hc⟩
    exact intrinsic_affine_action_germ_at_g17 f AD P A g hA q q' E hE c e
      hcmax he p hp.1 hp.2.2

end OriginalLeaves
end HolomorphicAnosov.Ghys






