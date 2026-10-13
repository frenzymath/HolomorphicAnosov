import HolomorphicAnosov.Paper.Ghys.NativePartitionsEq
import HolomorphicAnosov.Geometry.Holonomy.StableBoxPath
import HolomorphicAnosov.Geometry.FinitePlaqueHolonomy
import HolomorphicAnosov.Paper.Ghys.NativeStablePointHomeomorph
import HolomorphicAnosov.Paper.Ghys.NativeUnstablePointHomeomorph

noncomputable section
namespace HolomorphicAnosov
open Set _root_.Topology
universe u v w

/-- The union of two box presentations of the same intrinsic foliations presents the same leaf
partitions and topologies. (Nisoli, §1.3) -/
noncomputable def TransverseContinuousFoliations.union
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (G : TransverseContinuousFoliations.{u,w} s t M)
    (hS : F.stablePartition = G.stablePartition)
    (hU : F.unstablePartition = G.unstablePartition)
    (hST : HEq F.stableTopology G.stableTopology)
    (hUT : HEq F.unstableTopology G.unstableTopology) :
    TransverseContinuousFoliations.{u,max v w} s t M := by
  rcases F with ⟨I, B, cov, Rs, Ru, sg, ug, Ts, Tu, Cs, Cu, sc, uc, si, ui,
    Ls, Lu, sl, ul, sp, up, stg, utg⟩
  rcases G with ⟨J, B', cov', Rs', Ru', sg', ug', Ts', Tu', Cs', Cu', sc', uc', si', ui',
    Ls', Lu', sl', ul', sp', up', stg', utg'⟩
  dsimp only at hS hU hST hUT
  subst Rs'
  subst Ru'
  have hs : Ts = Ts' := eq_of_heq hST
  have hu : Tu = Tu' := eq_of_heq hUT
  subst Ts'
  subst Tu'
  refine {
    boxIndex := I ⊕ J
    box := Sum.elim B B'
    cover := fun x ↦ ?_
    stablePartition := Rs
    unstablePartition := Ru
    stable_generated := ?_
    unstable_generated := ?_
    stableTopology := Ts
    unstableTopology := Tu
    stableCharts := Cs
    unstableCharts := Cu
    stable_connected := sc
    unstable_connected := uc
    stable_inclusion := si
    unstable_inclusion := ui
    stableLabel := Sum.elim Ls Ls'
    unstableLabel := Sum.elim Lu Lu'
    stable_label := ?_
    unstable_label := ?_
    stable_plaque := ?_
    unstable_plaque := ?_
    stable_topology_generated := ?_
    unstable_topology_generated := ?_ }
  · obtain ⟨i, hi⟩ := cov x
    exact ⟨Sum.inl i, hi⟩
  · intro x y
    constructor
    · intro h
      apply Relation.EqvGen.mono (fun a b hab ↦ ?_) x y ((sg x y).mp h)
      rcases hab with ⟨i, w, z, z', hz, hz'⟩
      exact ⟨Sum.inl i, w, z, z', hz, hz'⟩
    · intro h
      induction h with
      | rel a b hab =>
        rcases hab with ⟨i, w, z, z', hz, hz'⟩
        cases i with
        | inl i => exact (sg a b).mpr (.rel _ _ ⟨i,w,z,z',hz,hz'⟩)
        | inr i => exact (sg' a b).mpr (.rel _ _ ⟨i,w,z,z',hz,hz'⟩)
      | refl a => exact Rs.refl a
      | symm a b _ ih => exact Rs.symm ih
      | trans a b c _ _ hab hbc => exact Rs.trans hab hbc
  · intro x y
    constructor
    · intro h
      apply Relation.EqvGen.mono (fun a b hab ↦ ?_) x y ((ug x y).mp h)
      rcases hab with ⟨i, z, w, w', hw, hw'⟩
      exact ⟨Sum.inl i, z, w, w', hw, hw'⟩
    · intro h
      induction h with
      | rel a b hab =>
        rcases hab with ⟨i, z, w, w', hw, hw'⟩
        cases i with
        | inl i => exact (ug a b).mpr (.rel _ _ ⟨i,z,w,w',hw,hw'⟩)
        | inr i => exact (ug' a b).mpr (.rel _ _ ⟨i,z,w,w',hw,hw'⟩)
      | refl a => exact Ru.refl a
      | symm a b _ ih => exact Ru.symm ih
      | trans a b c _ _ hab hbc => exact Ru.trans hab hbc
  · intro i z w
    cases i with
    | inl i => exact sl i z w
    | inr i => exact sl' i z w
  · intro i z w
    cases i with
    | inl i => exact ul i z w
    | inr i => exact ul' i z w
  · intro i w
    cases i with
    | inl i => exact sp i w
    | inr i => exact sp' i w
  · intro i z
    cases i with
    | inl i => exact up i z
    | inr i => exact up' i z
  · intro q W
    constructor
    · intro h i w hw
      cases i with
      | inl i => exact (stg q W).mp h i w hw
      | inr i => exact (stg' q W).mp h i w hw
    · intro h
      exact (stg q W).mpr (fun i w hw ↦ h (Sum.inl i) w hw)
  · intro q W
    constructor
    · intro h i z hz
      cases i with
      | inl i => exact (utg q W).mp h i z hz
      | inr i => exact (utg' q W).mp h i z hz
    · intro h
      exact (utg q W).mpr (fun i z hz ↦ h (Sum.inl i) z hz)

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set _root_.Topology
universe u v w

/-- An additional transverse box family compatible with the given intrinsic leaf carriers. -/
structure CompatibleTransverseBoxes
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M) {J : Type w}
    (B : J → TransverseFoliationBox s t M) where
  stableLabel : ∀ _j : J, FoliationCoordinateDisk t → Quotient F.stablePartition
  unstableLabel : ∀ _j : J, FoliationCoordinateDisk s → Quotient F.unstablePartition
  stable_label : ∀ j z w, Quotient.mk F.stablePartition ((B j).chart (z,w)).val = stableLabel j w
  unstable_label : ∀ j z w, Quotient.mk F.unstablePartition ((B j).chart (z,w)).val = unstableLabel j z
  stable_plaque : ∀ j w,
    letI := F.stableTopology (stableLabel j w)
    IsOpenEmbedding (fun z ↦ (⟨((B j).chart (z,w)).val, stable_label j z w⟩ :
      IntrinsicFoliationLeaf F.stablePartition (stableLabel j w)))
  unstable_plaque : ∀ j z,
    letI := F.unstableTopology (unstableLabel j z)
    IsOpenEmbedding (fun w ↦ (⟨((B j).chart (z,w)).val, unstable_label j z w⟩ :
      IntrinsicFoliationLeaf F.unstablePartition (unstableLabel j z)))

noncomputable def compatibleTransverseBoxes_of_equal_leaves
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (G : TransverseContinuousFoliations.{u,w} s t M)
    (hS : F.stablePartition = G.stablePartition)
    (hU : F.unstablePartition = G.unstablePartition)
    (hST : HEq F.stableTopology G.stableTopology)
    (hUT : HEq F.unstableTopology G.unstableTopology) : CompatibleTransverseBoxes F G.box := by
  rcases F with ⟨I, B, cov, Rs, Ru, sg, ug, Ts, Tu, Cs, Cu, sc, uc, si, ui,
    Ls, Lu, sl, ul, sp, up, stg, utg⟩
  rcases G with ⟨J, B', cov', Rs', Ru', sg', ug', Ts', Tu', Cs', Cu', sc', uc', si', ui',
    Ls', Lu', sl', ul', sp', up', stg', utg'⟩
  dsimp only at hS hU hST hUT
  subst Rs'
  subst Ru'
  have hs : Ts = Ts' := eq_of_heq hST
  have hu : Tu = Tu' := eq_of_heq hUT
  subst Ts'
  subst Tu'
  exact ⟨Ls', Lu', sl', ul', sp', up'⟩

/-- The union box presentation retains the first presentation's intrinsic leaf carriers and
topologies. -/
noncomputable def TransverseContinuousFoliations.unionNative
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (G : TransverseContinuousFoliations.{u,w} s t M)
    (hS : F.stablePartition = G.stablePartition)
    (hU : F.unstablePartition = G.unstablePartition)
    (hST : HEq F.stableTopology G.stableTopology)
    (hUT : HEq F.unstableTopology G.unstableTopology) :
    TransverseContinuousFoliations.{u,max v w} s t M := by
  let A := compatibleTransverseBoxes_of_equal_leaves F G hS hU hST hUT
  refine {
    boxIndex := F.boxIndex ⊕ G.boxIndex
    box := Sum.elim F.box G.box
    cover := fun x ↦ ?_
    stablePartition := F.stablePartition
    unstablePartition := F.unstablePartition
    stable_generated := ?_
    unstable_generated := ?_
    stableTopology := F.stableTopology
    unstableTopology := F.unstableTopology
    stableCharts := F.stableCharts
    unstableCharts := F.unstableCharts
    stable_connected := F.stable_connected
    unstable_connected := F.unstable_connected
    stable_inclusion := F.stable_inclusion
    unstable_inclusion := F.unstable_inclusion
    stableLabel := Sum.elim F.stableLabel A.stableLabel
    unstableLabel := Sum.elim F.unstableLabel A.unstableLabel
    stable_label := ?_
    unstable_label := ?_
    stable_plaque := ?_
    unstable_plaque := ?_
    stable_topology_generated := ?_
    unstable_topology_generated := ?_ }
  · obtain ⟨i, hi⟩ := F.cover x
    exact ⟨Sum.inl i, hi⟩
  · intro x y
    constructor
    · intro h
      apply Relation.EqvGen.mono (fun a b hab ↦ ?_) x y ((F.stable_generated x y).mp h)
      rcases hab with ⟨i, w, z, z', hz, hz'⟩
      exact ⟨Sum.inl i, w, z, z', hz, hz'⟩
    · intro h
      induction h with
      | rel a b hab =>
        rcases hab with ⟨i, w, z, z', hz, hz'⟩
        cases i with
        | inl i => exact (F.stable_generated a b).mpr (.rel _ _ ⟨i,w,z,z',hz,hz'⟩)
        | inr i =>
          apply Quotient.exact
          rw [← hz, ← hz']
          exact (A.stable_label i z w).trans (A.stable_label i z' w).symm
      | refl a => exact F.stablePartition.refl a
      | symm a b _ ih => exact F.stablePartition.symm ih
      | trans a b c _ _ hab hbc => exact F.stablePartition.trans hab hbc
  · intro x y
    constructor
    · intro h
      apply Relation.EqvGen.mono (fun a b hab ↦ ?_) x y ((F.unstable_generated x y).mp h)
      rcases hab with ⟨i, z, w, w', hw, hw'⟩
      exact ⟨Sum.inl i, z, w, w', hw, hw'⟩
    · intro h
      induction h with
      | rel a b hab =>
        rcases hab with ⟨i, z, w, w', hw, hw'⟩
        cases i with
        | inl i => exact (F.unstable_generated a b).mpr (.rel _ _ ⟨i,z,w,w',hw,hw'⟩)
        | inr i =>
          apply Quotient.exact
          rw [← hw, ← hw']
          exact (A.unstable_label i z w).trans (A.unstable_label i z w').symm
      | refl a => exact F.unstablePartition.refl a
      | symm a b _ ih => exact F.unstablePartition.symm ih
      | trans a b c _ _ hab hbc => exact F.unstablePartition.trans hab hbc
  · intro i z w
    cases i with
    | inl i => exact F.stable_label i z w
    | inr i => exact A.stable_label i z w
  · intro i z w
    cases i with
    | inl i => exact F.unstable_label i z w
    | inr i => exact A.unstable_label i z w
  · intro i w
    cases i with
    | inl i => exact F.stable_plaque i w
    | inr i => exact A.stable_plaque i w
  · intro i z
    cases i with
    | inl i => exact F.unstable_plaque i z
    | inr i => exact A.unstable_plaque i z
  · intro q W
    constructor
    · intro h i w hw
      cases i with
      | inl i => exact (F.stable_topology_generated q W).mp h i w hw
      | inr i =>
        subst q
        let := F.stableTopology (A.stableLabel i w)
        exact h.preimage (A.stable_plaque i w).continuous
    · intro h
      exact (F.stable_topology_generated q W).mpr (fun i w hw ↦ h (Sum.inl i) w hw)
  · intro q W
    constructor
    · intro h i z hz
      cases i with
      | inl i => exact (F.unstable_topology_generated q W).mp h i z hz
      | inr i =>
        subst q
        let := F.unstableTopology (A.unstableLabel i z)
        exact h.preimage (A.unstable_plaque i z).continuous
    · intro h
      exact (F.unstable_topology_generated q W).mpr (fun i z hz ↦ h (Sum.inl i) z hz)

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set Filter _root_.Topology
universe u v w

/-- Holonomy germs along the same stable path agree for two box presentations of the same intrinsic
foliations. (Nisoli, §1.3; Ghys, p. 594) -/
theorem same_path_holonomy_germ_of_equal_intrinsic_foliations
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (G : TransverseContinuousFoliations.{u,w} s t M)
    (hS : F.stablePartition = G.stablePartition)
    (hU : F.unstablePartition = G.unstablePartition)
    (hST : HEq F.stableTopology G.stableTopology)
    (hUT : HEq F.unstableTopology G.unstableTopology)
    {qF : Quotient F.stablePartition} {qG : Quotient G.stablePartition}
    {xF yF : IntrinsicFoliationLeaf F.stablePartition qF}
    {xG yG : IntrinsicFoliationLeaf G.stablePartition qG}
    (γF : Path xF yF) (γG : Path xG yG)
    (hγ : ∀ r : unitInterval, (γF r).val = (γG r).val)
    (eF : PathHolonomyRepresentative F γF 0 1)
    (eG : PathHolonomyRepresentative G γG 0 1)
    (H0 : F.ULeaf (γF 0).val ≃ₜ G.ULeaf (γG 0).val)
    (H1 : F.ULeaf (γF 1).val ≃ₜ G.ULeaf (γG 1).val)
    (hH0 : ∀ z, (H0 z).val = z.val) (hH1 : ∀ z, (H1 z).val = z.val) :
    ∀ᶠ z in 𝓝 (F.uPoint (γF 0).val), H1 (eF.map z) = eG.map (H0 z) := by
  rcases F with ⟨I, B, cov, Rs, Ru, sg, ug, Ts, Tu, Cs, Cu, sc, uc, si, ui,
    Ls, Lu, sl, ul, sp, up, stg, utg⟩
  rcases G with ⟨J, B', cov', Rs', Ru', sg', ug', Ts', Tu', Cs', Cu', sc', uc', si', ui',
    Ls', Lu', sl', ul', sp', up', stg', utg'⟩
  dsimp only at hS hU hST hUT
  subst Rs'
  subst Ru'
  have hs : Ts = Ts' := eq_of_heq hST
  have hu : Tu = Tu' := eq_of_heq hUT
  subst Ts'
  subst Tu'
  let F : TransverseContinuousFoliations.{u,v} s t M :=
    ⟨I,B,cov,Rs,Ru,sg,ug,Ts,Tu,Cs,Cu,sc,uc,si,ui,Ls,Lu,sl,ul,sp,up,stg,utg⟩
  let G : TransverseContinuousFoliations.{u,w} s t M :=
    ⟨J,B',cov',Rs,Ru,sg',ug',Ts,Tu,Cs',Cu',sc',uc',si',ui',Ls',Lu',sl',ul',sp',up',stg',utg'⟩
  have hq : qF = qG := (γF 0).property.symm.trans
    ((congrArg (Quotient.mk Rs) (hγ 0)).trans (γG 0).property)
  subst qG
  have hx : xF = xG := Subtype.ext (by simpa using hγ 0)
  have hy : yF = yG := Subtype.ext (by simpa using hγ 1)
  subst xG
  subst yG
  have hpath : γF = γG := Path.ext (funext (fun r ↦ Subtype.ext (hγ r)))
  subst γG
  have h0 (z) : H0 z = z := Subtype.ext (hH0 z)
  have h1 (z) : H1 z = z := Subtype.ext (hH1 z)
  let H := F.unionNative G rfl rfl HEq.rfl HEq.rfl
  have liftF {a b : unitInterval}
      {e : OpenPartialHomeomorph (F.ULeaf (γF a).val) (F.ULeaf (γF b).val)}
      (he : PlaqueChainAlong F γF a b e) : PlaqueChainAlong H γF a b e := by
    induction he with
    | single a b hab e hseg =>
      let e' : LocalPlaqueTransport H (γF a).val (γF b).val :=
        { e with box := Sum.inl e.box }
      exact .single a b hab e' hseg
    | compose hab hbc hl hr ihl ihr => exact .compose hab hbc ihl ihr
  have liftG {a b : unitInterval}
      {e : OpenPartialHomeomorph (G.ULeaf (γF a).val) (G.ULeaf (γF b).val)}
      (he : PlaqueChainAlong G γF a b e) : PlaqueChainAlong H γF a b e := by
    induction he with
    | single a b hab e hseg =>
      let e' : LocalPlaqueTransport H (γF a).val (γF b).val :=
        { e with box := Sum.inr e.box }
      exact .single a b hab e' hseg
    | compose hab hbc hl hr ihl ihr => exact .compose hab hbc ihl ihr
  have heq := same_subpath_plaque_chain_germ H γF (liftF eF.chain) eG.map (liftG eG.chain)
  have heq' := Filter.Germ.coe_eq.mp heq
  filter_upwards [heq'] with z hz
  change eF.map z = eG.map z at hz
  simpa only [h0, h1] using hz

end HolomorphicAnosov

namespace HolomorphicAnosov.Ghys
universe u

/-- Point-preserving intrinsic leaf homeomorphisms identify the topology families on equal point
partitions. (HPS, §7, p. 116) -/
theorem leaf_topologies_heq_of_point_homeomorph
    {M : Type u} {R R' : Setoid M} (hR : R = R')
    (T : ∀ q : Quotient R, TopologicalSpace (IntrinsicFoliationLeaf R q))
    (T' : ∀ q : Quotient R', TopologicalSpace (IntrinsicFoliationLeaf R' q))
    (h : ∀ x : M,
      ∃ e : @Homeomorph (IntrinsicFoliationLeaf R (Quotient.mk R x))
        (IntrinsicFoliationLeaf R' (Quotient.mk R' x)) (T _) (T' _),
        ∀ z, (e z).val = z.val) : HEq T T' := by
  subst R'
  apply heq_of_eq
  funext q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨e, he⟩ := h x
    have hid : (e : IntrinsicFoliationLeaf R (Quotient.mk R x) →
        IntrinsicFoliationLeaf R (Quotient.mk R x)) = id := by
      funext z
      exact Subtype.ext (he z)
    have ht := @Homeomorph.induced_eq _ _ (T _) (T' _) e
    exact ht.symm.trans ((congrArg (fun f ↦ TopologicalSpace.induced f (T' _)) hid).trans
      (@induced_id _ (T' _)))

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v w

/-- Native presentations with the same unstable dimension have the same stable dimension. (HPS, §7) -/
theorem native_presentation_stable_dimension_eq
    {d s s' t : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t)
    (B : NativeTransverseAsymptoticIdentification.{u,w} f Ps Pu s' t) : s = s' := by
  have h := (A.realCoordinates.symm.trans B.realCoordinates).toLinearEquiv.finrank_eq
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  omega

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov
universe u v

/-- Changing the ambient real atlas retains the continuous transverse foliation's boxes, partitions,
intrinsic topologies, and plaque maps. -/
def TransverseContinuousFoliations.rechart
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [C₀ : ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (C : ChartedSpace (Fin (s+t) → ℝ) M) :
    letI := C
    TransverseContinuousFoliations.{u,v} s t M := by
  letI := C
  exact {
    boxIndex := (letI := C₀; F.boxIndex)
    box := (letI := C₀; F.box)
    cover := (letI := C₀; F.cover)
    stablePartition := (letI := C₀; F.stablePartition)
    unstablePartition := (letI := C₀; F.unstablePartition)
    stable_generated := (letI := C₀; F.stable_generated)
    unstable_generated := (letI := C₀; F.unstable_generated)
    stableTopology := (letI := C₀; F.stableTopology)
    unstableTopology := (letI := C₀; F.unstableTopology)
    stableCharts := (letI := C₀; F.stableCharts)
    unstableCharts := (letI := C₀; F.unstableCharts)
    stable_connected := (letI := C₀; F.stable_connected)
    unstable_connected := (letI := C₀; F.unstable_connected)
    stable_inclusion := (letI := C₀; F.stable_inclusion)
    unstable_inclusion := (letI := C₀; F.unstable_inclusion)
    stableLabel := (letI := C₀; F.stableLabel)
    unstableLabel := (letI := C₀; F.unstableLabel)
    stable_label := (letI := C₀; F.stable_label)
    unstable_label := (letI := C₀; F.unstable_label)
    stable_plaque := (letI := C₀; F.stable_plaque)
    unstable_plaque := (letI := C₀; F.unstable_plaque)
    stable_topology_generated := (letI := C₀; F.stable_topology_generated)
    unstable_topology_generated := (letI := C₀; F.unstable_topology_generated) }

namespace Ghys
open scoped ContDiff Manifold
universe w

/-- Native presentations of the same dynamics have identical intrinsic partition topology families.
(HPS, §7, pp. 115–116) -/
theorem native_partition_topologies_heq
    {d s t s' t' : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t)
    (B : NativeTransverseAsymptoticIdentification.{u,w} f Ps Pu s' t') :
    (letI := A.realAmbientCharts; letI := B.realAmbientCharts;
      HEq A.F.stableTopology B.F.stableTopology ∧ HEq A.F.unstableTopology B.F.unstableTopology) := by
  let := A.realAmbientCharts
  let := B.realAmbientCharts
  obtain ⟨hS, hU⟩ := native_identification_partitions_eq f Ps Pu A B
  exact ⟨leaf_topologies_heq_of_point_homeomorph hS A.F.stableTopology B.F.stableTopology
      (native_stable_point_homeomorph A B),
    leaf_topologies_heq_of_point_homeomorph hU A.F.unstableTopology B.F.unstableTopology
      (native_unstable_point_homeomorph A B)⟩

end Ghys
end HolomorphicAnosov

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v w

/-- Equal leaf labels induce a homeomorphism between the corresponding intrinsic leaves. -/
def intrinsicLeafLabelHomeomorph {M : Type u} (R : Setoid M)
    (T : ∀ q : Quotient R, TopologicalSpace (IntrinsicFoliationLeaf R q))
    (q q' : Quotient R) (h : q = q') :
    @Homeomorph (IntrinsicFoliationLeaf R q) (IntrinsicFoliationLeaf R q') (T q) (T q') := by
  subst q'
  letI := T q
  exact Homeomorph.refl _

@[simp] theorem intrinsicLeafLabelHomeomorph_val {M : Type u} (R : Setoid M)
    (T : ∀ q : Quotient R, TopologicalSpace (IntrinsicFoliationLeaf R q))
    (q q' : Quotient R) (h : q = q') (z : IntrinsicFoliationLeaf R q) :
    (intrinsicLeafLabelHomeomorph R T q q' h z).val = z.val := by
  subst q'
  rfl

/-- Every stable quotient class admits a point-preserving homeomorphism between its native leaf
presentations. (HPS, §7, p. 116) -/
theorem native_stable_class_point_homeomorph
    {d s t s' t' : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t)
    (B : NativeTransverseAsymptoticIdentification.{u,w} f Ps Pu s' t') :
    letI := A.realAmbientCharts
    letI := B.realAmbientCharts
    ∀ q : Quotient A.F.stablePartition,
      ∃ q' : Quotient B.F.stablePartition,
        ∃ E : @Homeomorph (IntrinsicFoliationLeaf A.F.stablePartition q)
          (IntrinsicFoliationLeaf B.F.stablePartition q') (A.F.stableTopology q) (B.F.stableTopology q'),
          ∀ z, (E z).val = z.val := by
  let := A.realAmbientCharts
  let := B.realAmbientCharts
  intro q
  obtain ⟨E, hE⟩ := native_stable_point_homeomorph A B q.out
  let J := intrinsicLeafLabelHomeomorph A.F.stablePartition A.F.stableTopology q
    (Quotient.mk A.F.stablePartition q.out) (Quotient.out_eq q).symm
  refine ⟨Quotient.mk B.F.stablePartition q.out, J.trans E, ?_⟩
  intro z
  exact (hE (J z)).trans (intrinsicLeafLabelHomeomorph_val _ _ _ _ _ z)

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov
universe u v

/-- Changing the ambient atlas preserves finite plaque-chain witnesses, their paths, and their
partial maps. -/
theorem plaque_chain_rechart
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [C₀ : ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (C : ChartedSpace (Fin (s+t) → ℝ) M)
    {q : Quotient (letI := C₀; F.stablePartition)}
    {x y : IntrinsicFoliationLeaf (letI := C₀; F.stablePartition) q} (γ : Path x y)
    {a b : unitInterval}
    {h : OpenPartialHomeomorph (letI := C₀; F.ULeaf (γ a).val) (letI := C₀; F.ULeaf (γ b).val)}
    (he : letI := C₀; PlaqueChainAlong F γ a b h) :
    letI := C
    PlaqueChainAlong ((letI := C₀; F.rechart C)) γ a b h := by
  let := C
  induction he with
  | single a b hab e hs =>
    let e' : LocalPlaqueTransport ((letI := C₀; F.rechart C)) (γ a).val (γ b).val := {e with}
    exact .single a b hab e' hs
  | compose hab hbc hl hr ihl ihr => exact .compose hab hbc ihl ihr

/-- A pointed path representative in the new ambient atlas with the same source and function. -/
def path_representative_rechart
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [C₀ : ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (C : ChartedSpace (Fin (s+t) → ℝ) M)
    {q : Quotient (letI := C₀; F.stablePartition)}
    {x y : IntrinsicFoliationLeaf (letI := C₀; F.stablePartition) q} (γ : Path x y)
    {a b : unitInterval} (e : letI := C₀; PathHolonomyRepresentative F γ a b) :
    letI := C
    PathHolonomyRepresentative ((letI := C₀; F.rechart C)) γ a b := by
  letI := C
  exact {e with chain := (letI := C₀; plaque_chain_rechart F C γ e.chain)}

end HolomorphicAnosov


namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v w

/-- Every point-preserving homeomorphism between native unstable leaves is holomorphic in their
complex atlases. (Demailly, I §3.C; HPS, §7) -/
theorem native_point_homeomorph_holomorphic
    {d s t s' t' : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t)
    (B : NativeTransverseAsymptoticIdentification.{u,w} f Ps Pu s' t') (x y : M) :
    letI := A.unstableTopology x
    letI := A.unstableCharts x
    letI := (A.complexU1 x).charts
    letI := B.unstableTopology y
    letI := B.unstableCharts y
    letI := (B.complexU1 y).charts
    ∀ E : UnstableAsymptoticLeaf f x ≃ₜ UnstableAsymptoticLeaf f y,
      (∀ z, (E z).val = z.val) →
      ContMDiff (complexModel 1) (complexModel 1) ∞ E := by
  let := A.unstableTopology x
  let := A.unstableCharts x
  let := (A.complexU1 x).charts
  let := B.unstableTopology y
  let := B.unstableCharts y
  let := (B.complexU1 y).charts
  let := (A.complexU1 x).complex_manifold
  let := (B.complexU1 y).complex_manifold
  intro E hE z
  apply (ContMDiffAt.iff_comp_isImmersionAt ((B.complexU1 y).inclusion_immersion (E z))).mpr
  refine ⟨E.continuous.continuousAt, ?_⟩
  have heq : Subtype.val ∘ E = (Subtype.val : UnstableAsymptoticLeaf f x → M) := funext hE
  rw [heq]
  exact (A.complexU1 x).inclusion_holomorphic z

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Filter
open scoped _root_.Topology ContDiff
universe u v w r

/-- Holomorphicity of a germ is preserved by biholomorphic changes of its source and target
intrinsic leaves. (Demailly, I §3.C) -/
theorem holomorphic_at_of_conjugate_germ
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type r}
    [TopologicalSpace X] [ChartedSpace (ComplexModel 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel 1) Y]
    [TopologicalSpace X'] [ChartedSpace (ComplexModel 1) X']
    [TopologicalSpace Y'] [ChartedSpace (ComplexModel 1) Y']
    (E : X ≃ₜ X') (J : Y ≃ₜ Y') {f : X → Y} {g : X' → Y'} {x : X}
    (hE : ContMDiffAt (complexModel 1) (complexModel 1) ∞ E x)
    (hJ : ContMDiffAt (complexModel 1) (complexModel 1) ∞ J.symm (g (E x)))
    (hg : ContMDiffAt (complexModel 1) (complexModel 1) ∞ g (E x))
    (heq : ∀ᶠ z in 𝓝 x, J (f z) = g (E z)) :
    ContMDiffAt (complexModel 1) (complexModel 1) ∞ f x := by
  apply (hJ.comp x (hg.comp x hE)).congr_of_eventuallyEq
  filter_upwards [heq] with z hz
  change f z = J.symm (g (E z))
  rw [← hz, J.symm_apply_apply]

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped ContDiff Manifold
universe u v w

/-- The condition that every native stable-path representative is holomorphic at its marked point. -/
def CenteredNativeHolonomyHolomorphic
    {d s t : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t) : Prop :=
    letI := A.realAmbientCharts
    letI (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f a) := A.unstableTopology a
    letI (a : M) : ChartedSpace (Fin (A.nativeU a).rank → ℝ) (UnstableAsymptoticLeaf f a) := A.unstableCharts a
    letI (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f a) := (A.complexU1 a).charts
    ∀ q : Quotient A.F.stablePartition,
    letI := A.F.stableTopology q
    ∀ (x y : IntrinsicFoliationLeaf A.F.stablePartition q) (γ : Path x y)
      (e : PathHolonomyRepresentative A.F γ 0 1),
      ContMDiffAt (complexModel 1) (complexModel 1) ∞
        (A.transportUnstableLocalMap (γ 0).val (γ 1).val e.map)
        (A.unstableClassHomeomorph (γ 0).val (A.F.uPoint (γ 0).val))

/-- Holomorphicity at marked points of stable-path representatives is independent of the native
foliation presentation. (HPS, §7; Nisoli, §1.3; Ghys, p. 594) -/
theorem centered_native_holonomy_transfer
    {d s s' t : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t)
    (B : NativeTransverseAsymptoticIdentification.{u,w} f Ps Pu s' t)
    (hB : CenteredNativeHolonomyHolomorphic B) : CenteredNativeHolonomyHolomorphic A := by
  have hdim : s = s' := native_presentation_stable_dimension_eq A B
  subst s'
  let := A.realAmbientCharts
  let (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f a) := A.unstableTopology a
  let (a : M) : ChartedSpace (Fin (A.nativeU a).rank → ℝ) (UnstableAsymptoticLeaf f a) := A.unstableCharts a
  let (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f a) := (A.complexU1 a).charts
  intro q
  let := A.F.stableTopology q
  intro x y γ e
  obtain ⟨q', E, hE⟩ := native_stable_class_point_homeomorph A B q
  let := (letI := B.realAmbientCharts; B.F.stableTopology q')
  let γ' := γ.map E.continuous
  have hγ (r : unitInterval) : (γ r).val = (γ' r).val := (hE (γ r)).symm
  let := B.realAmbientCharts
  obtain ⟨e'⟩ := path_holonomy_representative_exists B.F γ'
  obtain ⟨H0, hH0⟩ : ∃ H0 : (letI := A.realAmbientCharts; A.F.ULeaf (γ 0).val) ≃ₜ B.F.ULeaf (γ' 0).val,
      ∀ z, (H0 z).val = z.val := by
    rw [← hγ 0]
    exact native_unstable_point_homeomorph A B (γ 0).val
  obtain ⟨H1, hH1⟩ : ∃ H1 : (letI := A.realAmbientCharts; A.F.ULeaf (γ 1).val) ≃ₜ B.F.ULeaf (γ' 1).val,
      ∀ z, (H1 z).val = z.val := by
    rw [← hγ 1]
    exact native_unstable_point_homeomorph A B (γ 1).val
  obtain ⟨hS, hU⟩ := native_identification_partitions_eq f Ps Pu A B
  obtain ⟨hST, hUT⟩ := native_partition_topologies_heq A B
  let G := B.F.rechart A.realAmbientCharts
  let eG := path_representative_rechart B.F A.realAmbientCharts γ' e'
  let := A.realAmbientCharts
  have hGerm := same_path_holonomy_germ_of_equal_intrinsic_foliations
    A.F G hS hU hST hUT γ γ' hγ e eG H0 H1 hH0 hH1
  let := B.unstableTopology (γ' 0).val
  let := B.unstableCharts (γ' 0).val
  let := (B.complexU1 (γ' 0).val).charts
  let := B.unstableTopology (γ' 1).val
  let := B.unstableCharts (γ' 1).val
  let := (B.complexU1 (γ' 1).val).charts
  let AX := A.unstableClassHomeomorph (γ 0).val
  let AY := A.unstableClassHomeomorph (γ 1).val
  let BX := B.unstableClassHomeomorph (γ' 0).val
  let BY := B.unstableClassHomeomorph (γ' 1).val
  let J0 := AX.symm.trans (H0.trans BX)
  let J1 := AY.symm.trans (H1.trans BY)
  have hJ0 (z) : (J0 z).val = z.val := by
    calc
      _ = (H0 (AX.symm z)).val := B.unstable_points _ _
      _ = (AX.symm z).val := hH0 _
      _ = z.val := by
        have h := (A.unstable_points _ (AX.symm z)).symm
        change (AX.symm z).val = (AX (AX.symm z)).val at h
        simpa only [Homeomorph.apply_symm_apply] using h
  have hJ1 (z) : (J1 z).val = z.val := by
    calc
      _ = (H1 (AY.symm z)).val := B.unstable_points _ _
      _ = (AY.symm z).val := hH1 _
      _ = z.val := by
        have h := (A.unstable_points _ (AY.symm z)).symm
        change (AY.symm z).val = (AY (AY.symm z)).val at h
        simpa only [Homeomorph.apply_symm_apply] using h
  have hJ1i (z) : (J1.symm z).val = z.val := by
    simpa only [Homeomorph.apply_symm_apply] using (hJ1 (J1.symm z)).symm
  let a := AX (A.F.uPoint (γ 0).val)
  let b := BX ((letI := B.realAmbientCharts; B.F.uPoint (γ' 0).val))
  have hab : J0 a = b := by
    apply Subtype.ext
    have ha : a.val = (γ 0).val := A.unstable_points _ _
    have hb : b.val = (γ' 0).val := by
      let := B.realAmbientCharts
      exact B.unstable_points _ _
    exact (hJ0 a).trans (ha.trans ((hγ 0).trans hb.symm))
  have hBholo := hB q' (E x) (E y) γ' e'
  have hBholo' : ContMDiffAt (complexModel 1) (complexModel 1) ∞
      ((letI := B.realAmbientCharts; B.transportUnstableLocalMap (γ' 0).val (γ' 1).val e'.map)) (J0 a) := by
    rw [hab]
    exact hBholo
  apply holomorphic_at_of_conjugate_germ J0 J1
    (native_point_homeomorph_holomorphic A B _ _ J0 hJ0 a)
    (native_point_homeomorph_holomorphic B A _ _ J1.symm hJ1i _)
    hBholo'
  have ht : Tendsto AX.symm (𝓝 a) (𝓝 (A.F.uPoint (γ 0).val)) := by
    simpa only [a, Homeomorph.symm_apply_apply] using AX.symm.continuous.continuousAt.tendsto (x := a)
  filter_upwards [ht.eventually hGerm] with z hz
  let := B.realAmbientCharts
  change BY (H1 (AY.symm (AY ((letI := A.realAmbientCharts; e.map) (AX.symm z))))) =
    BY (e'.map (BX.symm (BX (H0 (AX.symm z)))))
  simp only [Homeomorph.symm_apply_apply]
  exact congrArg BY hz

end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v
variable {d s t : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t)

/-- Holomorphicity at the marked point of a one-box map is preserved under equal endpoint labels. -/
theorem native_center_rebase_iff {x y x' y' : M}
    (e : letI := A.realAmbientCharts; LocalPlaqueTransport A.F x y)
    (hx : x = x') (hy : y = y') :
    letI := A.realAmbientCharts
    letI (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f a) := A.unstableTopology a
    letI (a : M) : ChartedSpace (Fin (A.nativeU a).rank → ℝ) (UnstableAsymptoticLeaf f a) := A.unstableCharts a
    letI (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f a) := (A.complexU1 a).charts
    ContMDiffAt (complexModel 1) (complexModel 1) ∞
      (A.transportUnstableLocalMap x' y' (rebasePlaqueTransport A.F e hx hy).map)
      (A.unstableClassHomeomorph x' (A.F.uPoint x')) ↔
    ContMDiffAt (complexModel 1) (complexModel 1) ∞
      (A.transportUnstableLocalMap x y e.map)
      (A.unstableClassHomeomorph x (A.F.uPoint x)) := by
  subst x'
  subst y'
  rfl

/-- Holomorphicity at marked points of stable-path representatives implies holomorphicity of each
one-box transport at its source mark. (Ghys, p. 594) -/
theorem native_centered_plaque_holomorphic
    (hA : CenteredNativeHolonomyHolomorphic A) :
    letI := A.realAmbientCharts
    letI (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f a) := A.unstableTopology a
    letI (a : M) : ChartedSpace (Fin (A.nativeU a).rank → ℝ) (UnstableAsymptoticLeaf f a) := A.unstableCharts a
    letI (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f a) := (A.complexU1 a).charts
    ∀ (x y : M) (e : LocalPlaqueTransport A.F x y),
    ContMDiffAt (complexModel 1) (complexModel 1) ∞
      (A.transportUnstableLocalMap x y e.map)
      (A.unstableClassHomeomorph x (A.F.uPoint x)) := by
  let := A.realAmbientCharts
  let (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f a) := A.unstableTopology a
  let (a : M) : ChartedSpace (Fin (A.nativeU a).rank → ℝ) (UnstableAsymptoticLeaf f a) := A.unstableCharts a
  let (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f a) := (A.complexU1 a).charts
  intro x y e
  let γ := stableBoxPath A.F e.box e.first e.second e.transverse
  have hx : x = (γ 0).val := e.first_point.symm.trans (congrArg Subtype.val γ.source).symm
  have hy : y = (γ 1).val := e.second_point.symm.trans (congrArg Subtype.val γ.target).symm
  let e' := rebasePlaqueTransport A.F e hx hy
  let r : PathHolonomyRepresentative A.F γ 0 1 := {
    toPointedLeafHomeomorph := e'.toPointedLeafHomeomorph
    chain := .single 0 1 (by norm_num) e' (by
      intro a ha hb
      exact (rebasePlaqueTransport_segment A.F e hx hy _).mpr
        (stableBoxPath_in_plaque A.F e.box e.first e.second e.transverse a)) }
  exact (native_center_rebase_iff A e hx hy).mp (hA _ _ _ γ r)

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
universe u v
variable {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,v} s t M)

/-- A homeomorphism relabeling an intrinsic unstable leaf by one of its points. -/
def unstableLeafRecenter (x : M) (z : F.ULeaf x) : F.ULeaf x ≃ₜ F.ULeaf z.val :=
  intrinsicLeafLabelHomeomorph F.unstablePartition F.unstableTopology
    (Quotient.mk F.unstablePartition x) (Quotient.mk F.unstablePartition z.val) z.property.symm

@[simp] theorem unstableLeafRecenter_val (x : M) (z a : F.ULeaf x) :
    (unstableLeafRecenter F x z a).val = a.val :=
  intrinsicLeafLabelHomeomorph_val _ _ _ _ _ _

@[simp] theorem unstableLeafRecenter_symm_val (x : M) (z : F.ULeaf x)
    (a : F.ULeaf z.val) : ((unstableLeafRecenter F x z).symm a).val = a.val := by
  have h := unstableLeafRecenter_val F x z ((unstableLeafRecenter F x z).symm a)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

@[simp] theorem unstableLeafRecenter_point (x : M) (z : F.ULeaf x) :
    unstableLeafRecenter F x z z = F.uPoint z.val := by
  apply Subtype.ext
  exact unstableLeafRecenter_val F x z z

@[simp] theorem unstableLeafRecenter_symm_point (x : M) (z : F.ULeaf x) :
    (unstableLeafRecenter F x z).symm (F.uPoint z.val) = z := by
  rw [← unstableLeafRecenter_point F x z, Homeomorph.symm_apply_apply]

/-- A one-box transport recentered at a point of its source and its image. (Ghys, p. 594) -/
def recenteredPlaqueTransport {x y : M} (e : LocalPlaqueTransport F x y)
    (z : F.ULeaf x) (hz : z ∈ e.map.source) :
    LocalPlaqueTransport F z.val (e.map z).val := by
  let Hx := unstableLeafRecenter F x z
  let Hy := unstableLeafRecenter F y (e.map z)
  let g := Hx.symm.toOpenPartialHomeomorph.trans (e.map.trans Hy.toOpenPartialHomeomorph)
  let w := Classical.choose (e.source_in_plaque z hz)
  have hw := Classical.choose_spec (e.source_in_plaque z hz)
  refine { map := g
           source_point := ?_
           map_point := ?_
           box := e.box
           first := e.first
           second := e.second
           transverse := w
           first_point := hw
           second_point := (e.coordinate_map z w hz hw).symm
           source_in_plaque := ?_
           coordinate_map := ?_ }
  · change F.uPoint z.val ∈ Set.univ ∩ Hx.symm ⁻¹' (e.map.source ∩ e.map ⁻¹' Set.univ)
    exact ⟨Set.mem_univ _, by simpa [Hx] using And.intro hz (Set.mem_univ (e.map z))⟩
  · change Hy (e.map (Hx.symm (F.uPoint z.val))) = F.uPoint (e.map z).val
    simp [Hx, Hy]
  · intro a ha
    have ha' : Hx.symm a ∈ e.map.source := ha.2.1
    obtain ⟨v, hv⟩ := e.source_in_plaque (Hx.symm a) ha'
    exact ⟨v, hv.trans (unstableLeafRecenter_symm_val F x z a)⟩
  · intro a v ha hv
    change (Hy (e.map (Hx.symm a))).val = _
    rw [unstableLeafRecenter_val]
    apply e.coordinate_map (Hx.symm a) v ha.2.1
    exact hv.trans (unstableLeafRecenter_symm_val F x z a).symm

end HolomorphicAnosov.Ghys

namespace HolomorphicAnosov.Ghys
open scoped ContDiff Manifold
universe u v

/-- Holomorphicity at marked points implies holomorphicity on the full source of every one-box
transport. (Ghys, p. 594) -/
theorem native_full_plaque_holomorphic
    {d s t : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t)
    (hA : CenteredNativeHolonomyHolomorphic A) :
    letI := A.realAmbientCharts
    letI (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f a) := A.unstableTopology a
    letI (a : M) : ChartedSpace (Fin (A.nativeU a).rank → ℝ) (UnstableAsymptoticLeaf f a) := A.unstableCharts a
    letI (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f a) := (A.complexU1 a).charts
    ∀ (x y : M) (e : LocalPlaqueTransport A.F x y),
      let g := A.transportUnstableLocalMap x y e.map
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ g g.source := by
  let := A.realAmbientCharts
  let (a : M) : TopologicalSpace (UnstableAsymptoticLeaf f a) := A.unstableTopology a
  let (a : M) : ChartedSpace (Fin (A.nativeU a).rank → ℝ) (UnstableAsymptoticLeaf f a) := A.unstableCharts a
  let (a : M) : ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f a) := (A.complexU1 a).charts
  intro x y e g a ha
  apply ContMDiffAt.contMDiffWithinAt
  let AX := A.unstableClassHomeomorph x
  let AY := A.unstableClassHomeomorph y
  let z := AX.symm a
  have hz : z ∈ e.map.source := ha.1.2
  let Hx := unstableLeafRecenter A.F x z
  let Hy := unstableLeafRecenter A.F y (e.map z)
  let AZ := A.unstableClassHomeomorph z.val
  let AW := A.unstableClassHomeomorph (e.map z).val
  let J0 := AX.symm.trans (Hx.trans AZ)
  let J1 := AY.symm.trans (Hy.trans AW)
  have hJ0 (b) : (J0 b).val = b.val := by
    calc
      _ = (Hx (AX.symm b)).val := A.unstable_points _ _
      _ = (AX.symm b).val := unstableLeafRecenter_val A.F x z _
      _ = b.val := by
        have h := (A.unstable_points _ (AX.symm b)).symm
        change (AX.symm b).val = (AX (AX.symm b)).val at h
        simpa only [Homeomorph.apply_symm_apply] using h
  have hJ1 (b) : (J1 b).val = b.val := by
    calc
      _ = (Hy (AY.symm b)).val := A.unstable_points _ _
      _ = (AY.symm b).val := unstableLeafRecenter_val A.F y (e.map z) _
      _ = b.val := by
        have h := (A.unstable_points _ (AY.symm b)).symm
        change (AY.symm b).val = (AY (AY.symm b)).val at h
        simpa only [Homeomorph.apply_symm_apply] using h
  have hJ1i (b) : (J1.symm b).val = b.val := by
    simpa only [Homeomorph.apply_symm_apply] using (hJ1 (J1.symm b)).symm
  let r := recenteredPlaqueTransport A.F e z hz
  have hm : J0 a = AZ (A.F.uPoint z.val) := by
    change AZ (Hx z) = _
    rw [unstableLeafRecenter_point]
  have hr : ContMDiffAt (complexModel 1) (complexModel 1) ∞
      (A.transportUnstableLocalMap z.val (e.map z).val r.map) (J0 a) := by
    rw [hm]
    exact native_centered_plaque_holomorphic A hA _ _ r
  apply holomorphic_at_of_conjugate_germ J0 J1
    (native_point_homeomorph_holomorphic A A _ _ J0 hJ0 a)
    (native_point_homeomorph_holomorphic A A _ _ J1.symm hJ1i _)
    hr
  apply Filter.Eventually.of_forall
  intro b
  change AW (Hy (AY.symm (AY (e.map (AX.symm b))))) =
    AW (Hy (e.map (Hx.symm (AZ.symm (AZ (Hx (AX.symm b)))))))
  simp only [Homeomorph.symm_apply_apply]

end HolomorphicAnosov.Ghys
