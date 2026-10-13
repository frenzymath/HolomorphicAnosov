import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Bases

/-!
# Continuity of lifts to native lamination leaves

Source: HPS, Invariant Manifolds, §7 pp.115–116. This generalizes the existing
fixed-rank argument in `continuous_stable_leaf_lift_g9` to the native lamination
interface: one separable leaf meets a box in countably many open plaques, and
the transverse image of a connected set in that leaf is therefore constant.
-/

namespace HolomorphicAnosov.HPS
open Set _root_.Topology TopologicalSpace
open scoped ContDiff Manifold Topology
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

variable {D : RealTangentDistribution 𝓘(ℝ, E) M}
variable {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]

/-- A map into one native leaf from a locally connected space is continuous
whenever its ambient inclusion is continuous.

Proof: fix a box around the image point. Its plaques belonging to the given
leaf are nonempty, pairwise disjoint and intrinsically open, so second
countability of the leaf makes their transverse labels countable. Restrict
the domain to a connected open neighborhood whose image lies in that box.
The continuous transverse coordinate has countable connected image in a
Euclidean coordinate domain, hence is constant. The map then factors through
one box plaque chart and its continuous inclusion into the intrinsic leaf.
Such neighborhoods prove continuity at every domain point. The argument uses
no differentiability in transverse directions. Source: HPS §7 pp.115–116,
agent-written topological expansion of its intrinsic open-plaque topology.
-/
theorem native_lamination_leaf_lift_continuous
    (F : LeafPartition D ι L r)
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (B : LaminationBoxes F β d T) (i : ι)
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (g : X → L i) (hg : Continuous ((F.leaf i).inclusion ∘ g)) : Continuous g := by
  classical
  have : SecondCountableTopology (L i) := (F.leaf i).countable
  have hcount (b : β) : {t : T b | (B.boxes b).label t = i}.Countable := by
    let W := {t : T b | (B.boxes b).label t = i}
    let plaque (t : W) (v : (B.boxes b).disc) : L i :=
      t.property ▸ ((B.boxes b).chart t.val v).val
    have hopen (t : W) : IsOpen (range (plaque t)) := by
      have hgeneral (j : ι) (hj : (B.boxes b).label t.val = j) :
          IsOpen (range (fun v : (B.boxes b).disc ↦
            (hj ▸ ((B.boxes b).chart t.val v).val : L j))) := by
        subst j
        have hrange : range (fun v : (B.boxes b).disc ↦
            (((B.boxes b).chart t.val v).val : L ((B.boxes b).label t.val))) =
            ((B.boxes b).plaque t.val : Set (L ((B.boxes b).label t.val))) := by
          ext y
          constructor
          · rintro ⟨v, rfl⟩
            exact ((B.boxes b).chart t.val v).property
          · intro hy
            obtain ⟨v, hv⟩ := ((B.boxes b).chart t.val).surjective ⟨y, hy⟩
            exact ⟨v, congrArg Subtype.val hv⟩
        rw [hrange]
        exact ((B.boxes b).plaque t.val).isOpen
      exact hgeneral i t.property
    have hne (t : W) : (range (plaque t)).Nonempty := by
      obtain ⟨v, hv⟩ := (B.boxes b).disc_connected.nonempty
      exact ⟨_, mem_range_self (⟨v, hv⟩ : (B.boxes b).disc)⟩
    have hfactor (t : W) (v : (B.boxes b).disc) :
        (F.leaf i).inclusion (plaque t v) = ((B.boxes b).box (v, t.val)).val := by
      have hgeneral (j : ι) (hj : (B.boxes b).label t.val = j) :
          (F.leaf j).inclusion (hj ▸ ((B.boxes b).chart t.val v).val) =
            ((B.boxes b).box (v, t.val)).val := by
        subst j
        exact ((B.boxes b).factorization t.val v).symm
      exact hgeneral i t.property
    have hd : Pairwise (fun t t' : W ↦ Disjoint (range (plaque t)) (range (plaque t'))) := by
      intro t t' hne
      rw [disjoint_left]
      rintro _ ⟨v, rfl⟩ ⟨v', heq⟩
      apply hne
      have hp : (B.boxes b).box (v', t'.val) = (B.boxes b).box (v, t.val) := by
        apply Subtype.ext
        rw [← hfactor t' v', ← hfactor t v, heq]
      exact Subtype.ext (congrArg Prod.snd ((B.boxes b).box.injective hp)).symm
    exact hd.countable_of_isOpen_disjoint hopen hne
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨b, hb⟩ := B.cover ((F.leaf i).inclusion (g x))
  have hU : ((F.leaf i).inclusion ∘ g) ⁻¹' (B.boxes b).ambient ∈ 𝓝 x :=
    ((B.boxes b).ambient.isOpen.preimage hg).mem_nhds hb
  obtain ⟨V, hVU, hVopen, hxV, hVconn⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance x _ hU
  let intoBox : V → (B.boxes b).ambient := fun z ↦
    ⟨(F.leaf i).inclusion (g z.val), hVU z.property⟩
  have hinto : Continuous intoBox := (hg.comp continuous_subtype_val).subtype_mk _
  let coords : V → (B.boxes b).disc × T b := (B.boxes b).box.symm ∘ intoBox
  have hcoords : Continuous coords := (B.boxes b).box.symm.continuous.comp hinto
  have hpoint (z : V) : ((B.boxes b).box (coords z)).val = (F.leaf i).inclusion (g z.val) :=
    congrArg Subtype.val ((B.boxes b).box.apply_symm_apply (intoBox z))
  have hlabel (z : V) : (B.boxes b).label (coords z).2 = i := by
    apply F.disjoint _ _ ((B.boxes b).chart (coords z).2 (coords z).1).val (g z.val)
    rw [← (B.boxes b).factorization, hpoint]
  let transverse : V → (B.boxes b).transverseDisc :=
    (B.boxes b).transverse_chart ∘ fun z ↦ (coords z).2
  have htransverse : Continuous transverse := (B.boxes b).transverse_chart.continuous.comp hcoords.snd
  have hrange : range transverse ⊆ (B.boxes b).transverse_chart ''
      {t : T b | (B.boxes b).label t = i} := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(coords z).2, hlabel z, rfl⟩
  have : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  have hconstant := ((hcount b).image (B.boxes b).transverse_chart).isTotallyDisconnected
    _ hrange (isPreconnected_range htransverse)
  let t := (coords ⟨x, hxV⟩).2
  have ht : (B.boxes b).label t = i := hlabel ⟨x, hxV⟩
  have heq (z : V) : (coords z).2 = t :=
    (B.boxes b).transverse_chart.injective
      (hconstant (mem_range_self z) (mem_range_self (⟨x, hxV⟩ : V)))
  let plaque (v : (B.boxes b).disc) : L i := ht ▸ ((B.boxes b).chart t v).val
  have hplaque : Continuous plaque := by
    have hgeneral (j : ι) (hj : (B.boxes b).label t = j) :
        Continuous (fun v : (B.boxes b).disc ↦
          (hj ▸ ((B.boxes b).chart t v).val : L j)) := by
      subst j
      exact continuous_subtype_val.comp ((B.boxes b).chart t).continuous
    exact hgeneral i ht
  have hplaque_point (v : (B.boxes b).disc) :
      (F.leaf i).inclusion (plaque v) = ((B.boxes b).box (v, t)).val := by
    have hgeneral (j : ι) (hj : (B.boxes b).label t = j) :
        (F.leaf j).inclusion (hj ▸ ((B.boxes b).chart t v).val) =
          ((B.boxes b).box (v, t)).val := by
      subst j
      exact ((B.boxes b).factorization t v).symm
    exact hgeneral i ht
  have hrestrict : Continuous (fun z : V ↦ g z.val) := by
    apply (hplaque.comp hcoords.fst).congr
    intro z
    apply (F.leaf i).injective
    change (F.leaf i).inclusion (plaque (coords z).1) = (F.leaf i).inclusion (g z.val)
    rw [hplaque_point, ← heq z]
    exact hpoint z
  exact (continuousOn_iff_continuous_domRestrict.mpr hrestrict).continuousAt
    (hVopen.mem_nhds hxV)

/-- A smooth ambient map taking values in one native leaf is smooth intrinsically.
The preceding continuity result supplies the topology guard in Mathlib's smooth
lifting theorem for immersions. Source: HPS §7 pp.115–116 and the smooth immersion
criterion `ContMDiff.iff_comp_isImmersion`. -/
theorem native_lamination_leaf_lift_contMDiff
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (F : LeafPartition D ι L r)
    {β : Type u} {d : β → ℕ} {T : β → Type u} [∀ b, TopologicalSpace (T b)]
    (B : LaminationBoxes F β d T) (i : ι)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {X : Type*} [TopologicalSpace X] [ChartedSpace E' X]
    [IsManifold 𝓘(ℝ, E') ∞ X] [LocallyConnectedSpace X]
    (g : X → L i) (hg : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ ((F.leaf i).inclusion ∘ g)) :
    ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, Fin (r i) → ℝ) ∞ g := by
  exact (ContMDiff.iff_comp_isImmersion (F.leaf i).immersion).mpr
    ⟨native_lamination_leaf_lift_continuous F B i g hg.continuous, hg⟩

end HolomorphicAnosov.HPS
