import HolomorphicAnosov.Geometry.UnstablePlaqueLabelFiberCountableG1
import Mathlib.Topology.Separation.Lemmas

/-!
Continuity of maps from locally connected spaces to separable intrinsic unstable leaves. (HPS,
§7, pp.115–116)
-/

namespace HolomorphicAnosov
open Set _root_.Topology TopologicalSpace
open scoped Topology
universe u v

/-- A map from a locally connected space to a separable intrinsic unstable leaf is continuous if its
composition with the leaf inclusion is continuous. -/
theorem continuous_unstable_leaf_lift_g1 {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (q : Quotient F.unstablePartition) {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] :
    letI := F.unstableTopology q
    ∀ (_hsep : SeparableSpace (IntrinsicFoliationLeaf F.unstablePartition q))
      (g : X → IntrinsicFoliationLeaf F.unstablePartition q),
      Continuous (fun x ↦ (g x).val) → Continuous g := by
  let := F.unstableTopology q
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
  have hlabel (z : V) : F.unstableLabel b (coords z).1 = q := by
    calc
      F.unstableLabel b (coords z).1 =
          Quotient.mk F.unstablePartition ((F.box b).chart (coords z)).val :=
        (F.unstable_label b (coords z).1 (coords z).2).symm
      _ = q := by rw [hpoint]; exact (g z.val).property
  have hcount := unstable_plaque_label_fiber_countable_g1 F b q hsep
  have hrange : range (fun z : V ↦ (coords z).1) ⊆
      {w | F.unstableLabel b w = q} := by
    rintro _ ⟨z, rfl⟩
    exact hlabel z
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  have hconstant := hcount.isTotallyDisconnected _ hrange
    (isPreconnected_range hcoords.fst)
  let w := (coords ⟨x, hxV⟩).1
  have hw : F.unstableLabel b w = q := hlabel ⟨x, hxV⟩
  have heq (z : V) : (coords z).1 = w :=
    hconstant (mem_range_self z) (mem_range_self (⟨x, hxV⟩ : V))
  let plaque (a : FoliationCoordinateDisk t) : IntrinsicFoliationLeaf F.unstablePartition q :=
    ⟨((F.box b).chart (w, a)).val, (F.unstable_label b w a).trans hw⟩
  have hplaque : Continuous plaque := by
    have hgeneral : ∀ (q₀ : Quotient F.unstablePartition) (hw₀ : F.unstableLabel b w = q₀),
        letI := F.unstableTopology q₀
        Continuous (fun a : FoliationCoordinateDisk t ↦
          (⟨((F.box b).chart (w, a)).val, (F.unstable_label b w a).trans hw₀⟩ :
            IntrinsicFoliationLeaf F.unstablePartition q₀)) := by
      intro q₀ hw₀
      subst q₀
      let := F.unstableTopology (F.unstableLabel b w)
      exact (F.unstable_plaque b w).continuous
    exact hgeneral q hw
  have hrestrict : Continuous (fun z : V ↦ g z.val) := by
    apply (hplaque.comp hcoords.snd).congr
    intro z
    apply Subtype.ext
    change ((F.box b).chart (w, (coords z).2)).val = (g z.val).val
    rw [← heq z]
    exact hpoint z
  exact (continuousOn_iff_continuous_domRestrict.mpr hrestrict).continuousAt
    (hVopen.mem_nhds hxV)

end HolomorphicAnosov

