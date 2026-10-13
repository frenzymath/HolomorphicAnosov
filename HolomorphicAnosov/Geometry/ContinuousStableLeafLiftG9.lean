import HolomorphicAnosov.Geometry.FoliationPlaqueLabelFiberCountableG9
import Mathlib.Topology.Separation.Lemmas

/-!
Continuity of maps from locally connected spaces to separable intrinsic stable leaves. (HPS, §7,
pp.115–116)
-/

namespace HolomorphicAnosov
open Set _root_.Topology TopologicalSpace
open scoped Topology
universe u v

/-- A map from a locally connected space to a separable intrinsic stable leaf is continuous if its
composition with the leaf inclusion is continuous. -/
theorem continuous_stable_leaf_lift_g9 {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (q : Quotient F.stablePartition) {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] :
    letI := F.stableTopology q
    ∀ (_hsep : SeparableSpace (IntrinsicFoliationLeaf F.stablePartition q))
      (g : X → IntrinsicFoliationLeaf F.stablePartition q),
      Continuous (fun x ↦ (g x).val) → Continuous g := by
  let := F.stableTopology q
  intro hsep g hg
  let := hsep
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨b, hb⟩ := F.cover (g x).val
  have hU : (fun z ↦ (g z).val) ⁻¹' (F.box b).image ∈ 𝓝 x :=
    ((F.box b).isOpen_image.preimage hg).mem_nhds hb
  obtain ⟨V, hVU, hVopen, hxV, hVconn⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance x _ hU
  let intoBox : V → (F.box b).image := fun z ↦ ⟨(g z.val).val, hVU z.property⟩
  have hinto : Continuous intoBox := (hg.comp continuous_subtype_val).subtype_mk _
  let coords : V → FoliationCoordinateDisk s × FoliationCoordinateDisk t :=
    (F.box b).chart.symm ∘ intoBox
  have hcoords : Continuous coords := (F.box b).chart.symm.continuous.comp hinto
  have hpoint (z : V) : ((F.box b).chart (coords z)).val = (g z.val).val := by
    exact congrArg Subtype.val ((F.box b).chart.apply_symm_apply (intoBox z))
  have hlabel (z : V) : F.stableLabel b (coords z).2 = q := by
    calc
      F.stableLabel b (coords z).2 =
          Quotient.mk F.stablePartition ((F.box b).chart (coords z)).val :=
        (F.stable_label b (coords z).1 (coords z).2).symm
      _ = q := by rw [hpoint]; exact (g z.val).property
  have hcount := stable_plaque_label_fiber_countable_g9 F b q hsep
  have hrange : range (fun z : V ↦ (coords z).2) ⊆
      {w | F.stableLabel b w = q} := by
    rintro _ ⟨z, rfl⟩
    exact hlabel z
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  have hconstant := hcount.isTotallyDisconnected _ hrange
    (isPreconnected_range hcoords.snd)
  let w := (coords ⟨x, hxV⟩).2
  have hw : F.stableLabel b w = q := hlabel ⟨x, hxV⟩
  have heq (z : V) : (coords z).2 = w :=
    hconstant (mem_range_self z) (mem_range_self (⟨x, hxV⟩ : V))
  let plaque (a : FoliationCoordinateDisk s) : IntrinsicFoliationLeaf F.stablePartition q :=
    ⟨((F.box b).chart (a, w)).val, (F.stable_label b a w).trans hw⟩
  have hplaque : Continuous plaque := by
    have hgeneral : ∀ (q₀ : Quotient F.stablePartition) (hw₀ : F.stableLabel b w = q₀),
        letI := F.stableTopology q₀
        Continuous (fun a : FoliationCoordinateDisk s ↦
          (⟨((F.box b).chart (a, w)).val, (F.stable_label b a w).trans hw₀⟩ :
            IntrinsicFoliationLeaf F.stablePartition q₀)) := by
      intro q₀ hw₀
      subst q₀
      let := F.stableTopology (F.stableLabel b w)
      exact (F.stable_plaque b w).continuous
    exact hgeneral q hw
  have hrestrict : Continuous (fun z : V ↦ g z.val) := by
    apply (hplaque.comp hcoords.fst).congr
    intro z
    apply Subtype.ext
    change ((F.box b).chart ((coords z).1, w)).val = (g z.val).val
    rw [← heq z]
    exact hpoint z
  exact (continuousOn_iff_continuous_domRestrict.mpr hrestrict).continuousAt
    (hVopen.mem_nhds hxV)

end HolomorphicAnosov

