import HolomorphicAnosov.Ghys.NativeInvariantJetAffineLeafFamily
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Lemmas

noncomputable section
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u v
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace


theorem affine_completeness_intrinsic_plaque_lift_continuous_provider
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U) (i : ι)
    {X : Type v} [TopologicalSpace X] [LocallyConnectedSpace X]
    (g : X → L i)
    (hg : Continuous (fun x ↦ (U.leaf i).inclusion (g x))) :
    Continuous g := by
  let : SecondCountableTopology (L i) := (U.leaf i).countable
  classical
  let plaque (j : Fin G.boxCount) (t : G.transverse j) (ht : G.label j t = i) :
      nativeAffineFlowboxSlice (G.box j) t.val → L i :=
    fun z ↦ ht ▸ (G.parametrization j t z).val
  have hplaque (j : Fin G.boxCount) (t : G.transverse j) (ht : G.label j t = i) :
      IsOpenEmbedding (plaque j t ht) := by
    have hgen : ∀ (k : ι) (hk : G.label j t = k),
        IsOpenEmbedding (fun z : nativeAffineFlowboxSlice (G.box j) t.val ↦
          (hk ▸ (G.parametrization j t z).val : L k)) := by
      intro k hk
      subst k
      exact (G.branch j t).isOpen.isOpenEmbedding_subtypeVal.comp
        (G.parametrization j t).toHomeomorph.isOpenEmbedding
    exact hgen i ht
  have hpoint (j : Fin G.boxCount) (t : G.transverse j) (ht : G.label j t = i)
      (z : nativeAffineFlowboxSlice (G.box j) t.val) :
      (U.leaf i).inclusion (plaque j t ht z) = (G.box j).symm (z.val,t.val) := by
    have hgen : ∀ (k : ι) (hk : G.label j t = k),
        (U.leaf k).inclusion (hk ▸ (G.parametrization j t z).val) =
          (G.box j).symm (z.val,t.val) := by
      intro k hk
      subst k
      exact (G.parametrization_inclusion j t z).symm
    exact hgen i ht
  have hcount (j : Fin G.boxCount) :
      {t : G.transverse j | G.label j t = i ∧
        (nativeAffineFlowboxSlice (G.box j) t.val : Set ℂ).Nonempty}.Countable := by
    let W := {t : G.transverse j | G.label j t = i ∧
      (nativeAffineFlowboxSlice (G.box j) t.val : Set ℂ).Nonempty}
    let P (w : W) := range (plaque j w.val w.property.1)
    have hopen (w : W) : IsOpen (P w) := (hplaque j w.val w.property.1).isOpen_range
    have hne (w : W) : (P w).Nonempty := by
      obtain ⟨z,hz⟩ := w.property.2
      exact ⟨_, mem_range_self (⟨z,hz⟩ : nativeAffineFlowboxSlice (G.box j) w.val.val)⟩
    have hdis : Pairwise (fun w w' : W ↦ Disjoint (P w) (P w')) := by
      intro w w' hww
      rw [disjoint_left]
      rintro y ⟨z,rfl⟩ ⟨z',he⟩
      apply hww
      have heq := congrArg (U.leaf i).inclusion he
      rw [hpoint, hpoint] at heq
      have hp := (G.box j).symm.injOn z'.property z.property heq
      exact Subtype.ext (Subtype.ext (congrArg Prod.snd hp).symm)
    exact hdis.countable_of_isOpen_disjoint hopen hne
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j,hj⟩ := G.box_cover ((U.leaf i).inclusion (g x))
  have hn : (fun z ↦ (U.leaf i).inclusion (g z)) ⁻¹' (G.box j).source ∈ 𝓝 x :=
    ((G.box j).open_source.preimage hg).mem_nhds hj
  obtain ⟨V,hVU,hVopen,hxV,hVconn⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance x _ hn
  let coords : V → ℂ × (Fin (2*d-2) → ℝ) :=
    fun z ↦ G.box j ((U.leaf i).inclusion (g z.val))
  have hcoords : Continuous coords :=
    (G.box j).continuousOn.comp_continuous (hg.comp continuous_subtype_val)
      (fun z ↦ hVU z.property)
  have htarget (z : V) : coords z ∈ (G.box j).target :=
    (G.box j).map_source (hVU z.property)
  let transverseCoord (z : V) : G.transverse j :=
    ⟨(coords z).2,G.transverse_contains j (coords z) (htarget z)⟩
  have htransverse : Continuous transverseCoord := hcoords.snd.subtype_mk _
  have hlabel (z : V) : G.label j (transverseCoord z) = i := by
    let q : nativeAffineFlowboxSlice (G.box j) (transverseCoord z).val :=
      ⟨(coords z).1,htarget z⟩
    apply U.disjoint (G.label j (transverseCoord z)) i
      (G.parametrization j (transverseCoord z) q).val (g z.val)
    rw [← G.parametrization_inclusion]
    exact (G.box j).left_inv (hVU z.property)
  have hrange : range transverseCoord ⊆
      {t : G.transverse j | G.label j t = i ∧
        (nativeAffineFlowboxSlice (G.box j) t.val : Set ℂ).Nonempty} := by
    rintro t ⟨z,rfl⟩
    exact ⟨hlabel z,⟨(coords z).1,htarget z⟩⟩
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  have hconstant := (hcount j).isTotallyDisconnected _ hrange
    (isPreconnected_range htransverse)
  let xV : V := ⟨x,hxV⟩
  let t := transverseCoord xV
  have heq (z : V) : transverseCoord z = t :=
    hconstant (mem_range_self z) (mem_range_self xV)
  let leafCoord (z : V) : nativeAffineFlowboxSlice (G.box j) t.val :=
    ⟨(coords z).1,by
      change ((coords z).1,t.val) ∈ (G.box j).target
      rw [← heq z]
      exact htarget z⟩
  have hleafCoord : Continuous leafCoord := hcoords.fst.subtype_mk _
  have hrestrict : Continuous (fun z : V ↦ g z.val) := by
    apply ((hplaque j t (hlabel xV)).continuous.comp hleafCoord).congr
    intro z
    apply (U.leaf i).injective
    change (U.leaf i).inclusion (plaque j t (hlabel xV) (leafCoord z)) = _
    rw [hpoint]
    change (G.box j).symm ((coords z).1,t.val) = _
    rw [← heq z]
    exact (G.box j).left_inv (hVU z.property)
  exact (continuousOn_iff_continuous_domRestrict.mpr hrestrict).continuousAt
    (hVopen.mem_nhds hxV)

end HolomorphicAnosov.Ghys