import HolomorphicAnosov.Dynamics.Anosov.SelectedPartitionProducts
import HolomorphicAnosov.Geometry.AdaptedNativeProductRealBoxes
import HolomorphicAnosov.Geometry.IntrinsicPresentationOfNativeRealBoxes
import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaques
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorMetric
import HolomorphicAnosov.Dynamics.Anosov.DistanceLeafRange
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Paper.Ghys.IntrinsicPresentationPlaqueHolomorphic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
set_option linter.style.haveILetI false
noncomputable section
open Set _root_.Topology
open scoped _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
/-- The diffeomorphism obtained by restricting a smooth partial homeomorphism with smooth inverse to
its open source and target. -/
def partialHomeomorphDiffeomorph
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [ChartedSpace K Y]
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F K)
    (e : OpenPartialHomeomorph X Y)
    (he : ContMDiffOn I J ∞ e e.source)
    (hi : ContMDiffOn J I ∞ e.symm e.target) :
    Diffeomorph I J (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens X)
      (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens Y) ∞ where
  toEquiv := e.toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    intro x
    exact contMDiffAt_subtype_iff.mpr
      ((he x.val x.property).contMDiffAt (e.open_source.mem_nhds x.property))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    intro y
    exact contMDiffAt_subtype_iff.mpr
      ((hi y.val y.property).contMDiffAt (e.open_target.mem_nhds y.property))
end HolomorphicAnosov
namespace HolomorphicAnosov
universe u
variable {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,u} s t M)
  (b : F.boxIndex) (z : FoliationCoordinateDisk s) (w₀ : FoliationCoordinateDisk t)

def nativeBoxUnstablePlaque : FoliationCoordinateDisk t →
    F.ULeaf ((F.box b).chart (z,w₀)).val := fun w ↦
  ⟨((F.box b).chart (z,w)).val,
    (F.unstable_label b z w).trans (F.unstable_label b z w₀).symm⟩

theorem nativeBoxUnstablePlaque_open : IsOpenEmbedding (nativeBoxUnstablePlaque F b z w₀) := by
  let q := Quotient.mk F.unstablePartition ((F.box b).chart (z,w₀)).val
  have h : F.unstableLabel b z = q := (F.unstable_label b z w₀).symm
  exact Eq.rec (motive := fun q h ↦
    letI := F.unstableTopology q
    IsOpenEmbedding (fun w : FoliationCoordinateDisk t ↦
      (⟨((F.box b).chart (z,w)).val, (F.unstable_label b z w).trans h⟩ :
        IntrinsicFoliationLeaf F.unstablePartition q)))
    (F.unstable_plaque b z) h

variable (z' : FoliationCoordinateDisk s)

def nativeBoxPlaqueTransport :
    LocalPlaqueTransport F ((F.box b).chart (z,w₀)).val ((F.box b).chart (z',w₀)).val := by
  letI : Nonempty (FoliationCoordinateDisk t) := ⟨w₀⟩
  let j := nativeBoxUnstablePlaque F b z w₀
  let j' := nativeBoxUnstablePlaque F b z' w₀
  let e := (nativeBoxUnstablePlaque_open F b z w₀).toOpenPartialHomeomorph j
  let e' := (nativeBoxUnstablePlaque_open F b z' w₀).toOpenPartialHomeomorph j'
  refine { map := e.symm.trans e'
           source_point := ?_
           map_point := ?_
           box := b
           first := z
           second := z'
           transverse := w₀
           first_point := rfl
           second_point := rfl
           source_in_plaque := ?_
           coordinate_map := ?_ }
  · exact ⟨⟨w₀, Set.mem_univ _, rfl⟩, Set.mem_univ _⟩
  · change e' (e.symm (j w₀)) = j' w₀
    rw [(nativeBoxUnstablePlaque_open F b z w₀).toOpenPartialHomeomorph_left_inv]
    rfl
  · intro x hx
    obtain ⟨w, hw⟩ := hx.1
    exact ⟨w, congrArg Subtype.val hw.2⟩
  · intro x w hx hw
    have heq : j w = x := Subtype.ext hw
    subst x
    change (e' (e.symm (j w))).val = _
    rw [(nativeBoxUnstablePlaque_open F b z w₀).toOpenPartialHomeomorph_left_inv]
    rfl

@[simp] theorem nativeBoxPlaqueTransport_apply (w : FoliationCoordinateDisk t) :
    (nativeBoxPlaqueTransport F b z w₀ z').map (nativeBoxUnstablePlaque F b z w₀ w) =
      nativeBoxUnstablePlaque F b z' w₀ w := by
  letI : Nonempty (FoliationCoordinateDisk t) := ⟨w₀⟩
  change (nativeBoxUnstablePlaque F b z' w₀)
    (((nativeBoxUnstablePlaque_open F b z w₀).toOpenPartialHomeomorph
      (nativeBoxUnstablePlaque F b z w₀)).symm
        (nativeBoxUnstablePlaque F b z w₀ w)) = _
  rw [(nativeBoxUnstablePlaque_open F b z w₀).toOpenPartialHomeomorph_left_inv]

@[simp] theorem nativeBoxPlaqueTransport_source :
    (nativeBoxPlaqueTransport F b z w₀ z').map.source = Set.range
      (nativeBoxUnstablePlaque F b z w₀) := by
  simp [nativeBoxPlaqueTransport]
end HolomorphicAnosov

namespace HolomorphicAnosov
open TopologicalSpace
variable {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,u} s 2 M)
  (charts : ∀ q : Quotient F.unstablePartition,
    letI := F.unstableTopology q
    ChartedSpace ℂ (IntrinsicFoliationLeaf F.unstablePartition q))
  (smooth : ∀ q : Quotient F.unstablePartition,
    letI := F.unstableTopology q; letI := charts q
    IsManifold 𝓘(ℂ) ∞ (IntrinsicFoliationLeaf F.unstablePartition q))
  (hol : ∀ (x y : M) (e : LocalPlaqueTransport F x y),
    letI := charts (Quotient.mk F.unstablePartition x)
    letI := charts (Quotient.mk F.unstablePartition y)
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.map e.map.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.map.symm e.map.target)

include smooth hol in
/-- An intrinsic holomorphic coordinate on an unstable plaque extends to scalar parameters for all
unstable plaques in the same real box. -/
theorem native_scalar_box_parameter
    (b : F.boxIndex) (z₀ : FoliationCoordinateDisk s) (w₀ : FoliationCoordinateDisk 2) :
    ∃ k : OpenPartialHomeomorph ℂ (FoliationCoordinateDisk 2), w₀ ∈ k.target ∧
      ∀ z : FoliationCoordinateDisk s,
        letI := charts (Quotient.mk F.unstablePartition ((F.box b).chart (z,w₀)).val)
        ∃ g : OpenPartialHomeomorph ℂ (F.ULeaf ((F.box b).chart (z,w₀)).val),
          g.source = k.source ∧
          ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g g.source ∧
          ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g.symm g.target ∧
          ∀ v ∈ k.source, (g v).val = ((F.box b).chart (z,k v)).val := by
  classical
  letI : Nonempty (FoliationCoordinateDisk 2) := ⟨w₀⟩
  let x := ((F.box b).chart (z₀,w₀)).val
  letI := charts (Quotient.mk F.unstablePartition x)
  letI := smooth (Quotient.mk F.unstablePartition x)
  let j := nativeBoxUnstablePlaque F b z₀ w₀
  let e := (nativeBoxUnstablePlaque_open F b z₀ w₀).toOpenPartialHomeomorph j
  let c := chartAt ℂ (F.uPoint x)
  let k : OpenPartialHomeomorph ℂ (FoliationCoordinateDisk 2) := c.symm.trans e.symm
  have hw : w₀ ∈ k.target := by
    refine ⟨Set.mem_univ _, ?_⟩
    exact mem_chart_source ℂ (F.uPoint x)
  refine ⟨k, hw, ?_⟩
  intro z
  let y := ((F.box b).chart (z,w₀)).val
  letI := charts (Quotient.mk F.unstablePartition y)
  let h := nativeBoxPlaqueTransport F b z₀ w₀ z
  let g := c.symm.trans h.map
  have he : e.target = Set.range j := by simp [e]
  have hsource : g.source = k.source := by
    change c.target ∩ c.symm ⁻¹' h.map.source = c.target ∩ c.symm ⁻¹' e.target
    rw [he, nativeBoxPlaqueTransport_source]
  obtain ⟨hh, hi⟩ := hol x y h
  refine ⟨g, hsource, ?_, ?_, ?_⟩
  · exact hh.comp ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (x := F.uPoint x)).mono
      Set.inter_subset_left) (fun v hv ↦ hv.2)
  · exact (contMDiffOn_chart (I := 𝓘(ℂ)) (x := F.uPoint x)).comp
      (hi.mono Set.inter_subset_left) (fun v hv ↦ hv.2)
  · intro v hv
    have hj : j (k v) = c.symm v := by
      exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv j
        (nativeBoxUnstablePlaque_open F b z₀ w₀) (by rw [← he]; exact hv.2)
    change (h.map (c.symm v)).val = _
    rw [← hj]
    exact congrArg Subtype.val (nativeBoxPlaqueTransport_apply F b z₀ w₀ z (k v))
end HolomorphicAnosov
namespace HolomorphicAnosov
open TopologicalSpace
variable {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,u} s 2 M)
  (b : F.boxIndex) (z₀ : FoliationCoordinateDisk s) (w₀ : FoliationCoordinateDisk 2)
  (k : OpenPartialHomeomorph ℂ (FoliationCoordinateDisk 2))

def nativeScalarInverseBox : OpenPartialHomeomorph (ℂ × (Fin s → ℝ)) M := by
  letI : Nonempty (FoliationCoordinateDisk s) := ⟨z₀⟩
  letI : Nonempty (F.box b).image := ⟨(F.box b).chart (z₀,w₀)⟩
  let es := (Metric.isOpen_ball : IsOpen (Metric.ball (0 : Fin s → ℝ) 1)).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  let eO := (F.box b).isOpen_image.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  exact (((k.prod es.symm).transHomeomorph
    (Homeomorph.prodComm (FoliationCoordinateDisk 2) (FoliationCoordinateDisk s))).transHomeomorph
      (F.box b).chart).trans eO

@[simp] theorem nativeScalarInverseBox_apply (v : ℂ) (z : Fin s → ℝ)
    (hz : z ∈ Metric.ball 0 1) :
    nativeScalarInverseBox F b z₀ w₀ k (v,z) = ((F.box b).chart (⟨z,hz⟩,k v)).val := by
  letI : Nonempty (FoliationCoordinateDisk s) := ⟨z₀⟩
  change ((F.box b).chart
    (((Metric.isOpen_ball : IsOpen (Metric.ball (0 : Fin s → ℝ) 1)).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val).symm z, k v)).val = _
  congr 2
  apply Prod.ext
  · apply Subtype.ext
    exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv Subtype.val
      Metric.isOpen_ball.isOpenEmbedding_subtypeVal ⟨⟨z,hz⟩,rfl⟩
  · rfl

@[simp] theorem nativeScalarInverseBox_source :
    (nativeScalarInverseBox F b z₀ w₀ k).source = k.source ×ˢ Metric.ball 0 1 := by
  ext p
  simp [nativeScalarInverseBox, FoliationCoordinateDisk]

 theorem nativeScalarInverseBox_center (hw : w₀ ∈ k.target) :
    ((F.box b).chart (z₀,w₀)).val ∈ (nativeScalarInverseBox F b z₀ w₀ k).target := by
  have hsrc : (k.symm w₀,z₀.val) ∈ (nativeScalarInverseBox F b z₀ w₀ k).source := by
    rw [nativeScalarInverseBox_source]
    exact ⟨k.map_target hw,z₀.property⟩
  have hval : nativeScalarInverseBox F b z₀ w₀ k (k.symm w₀,z₀.val) =
      ((F.box b).chart (z₀,w₀)).val := by
    rw [nativeScalarInverseBox_apply F b z₀ w₀ k _ _ z₀.property, k.right_inv hw]
  exact hval ▸ (nativeScalarInverseBox F b z₀ w₀ k).map_source hsrc
end HolomorphicAnosov
namespace HolomorphicAnosov
open Set TopologicalSpace
universe u v w
variable {M : Type u} {R : Type v} {L : Type w}
  [TopologicalSpace M] [TopologicalSpace R]
  [TopologicalSpace L] [ChartedSpace ℂ L]

/-- A scalar biholomorphic parameter induces a diffeomorphism from any open set equal to its source
onto its target. -/
theorem scalarParameterDiffeomorph
    (g : OpenPartialHomeomorph ℂ L) (A : Opens ℂ)
    (hs : g.source = (A : Set ℂ))
    (hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g g.source)
    (hi : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g.symm g.target) :
    ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A (⟨g.target,g.open_target⟩ : Opens L) ∞,
      ∀ z : A, (e z).val = g z.val := by
  have hA : A = (⟨g.source,g.open_source⟩ : Opens ℂ) := Opens.ext hs.symm
  subst A
  exact ⟨partialHomeomorphDiffeomorph 𝓘(ℂ) 𝓘(ℂ) g hg hi, fun _ ↦ rfl⟩

/-- A scalar biholomorphic parameter restricts to a biholomorphic parameter on any open subset of
its source. -/
theorem restrictedScalarParameter
    (g : OpenPartialHomeomorph ℂ L) (A : Opens ℂ) (hA : (A : Set ℂ) ⊆ g.source)
    (hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g g.source)
    (hi : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g.symm g.target) :
    ∃ V : Opens L, ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A V ∞,
      ∀ z : A, (e z).val = g z.val := by
  let h := g.restr A
  have hs : h.source = (A : Set ℂ) := by
    rw [OpenPartialHomeomorph.restr_source' _ _ A.isOpen, Set.inter_eq_right.mpr hA]
  have hh : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ h h.source := by
    exact hg.mono (by rw [hs]; exact hA)
  have hhi : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ h.symm h.target :=
    hi.mono Set.inter_subset_left
  obtain ⟨e,he⟩ := scalarParameterDiffeomorph h A hs hh hhi
  exact ⟨⟨h.target,h.open_target⟩,e,he⟩

/-- Two scalar box parameters on the same injectively immersed complex leaf have holomorphic
transitions on their overlaps. -/
theorem scalarBoxOverlapOnLeaf
    (c c' : OpenPartialHomeomorph M (ℂ × R)) (t t' : R)
    (j : L → M) (hj : Function.Injective j)
    (g g' : OpenPartialHomeomorph ℂ L)
    (hsource : g.source = {z | (z,t) ∈ c.target})
    (hsource' : g'.source = {z | (z,t') ∈ c'.target})
    (hinc : ∀ z ∈ g.source, j (g z) = c.symm (z,t))
    (hinc' : ∀ z ∈ g'.source, j (g' z) = c'.symm (z,t'))
    (hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g g.source)
    (hgi : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g.symm g.target)
    (hg' : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g' g'.source)
    (hgi' : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g'.symm g'.target)
    (z : ℂ) (hz : (z,t) ∈ c.target)
    (hz' : c.symm (z,t) ∈ c'.source)
    (ht' : (c' (c.symm (z,t))).2 = t') :
    ∃ (A B : Opens ℂ), z ∈ A ∧
      (∀ w ∈ A, (w,t) ∈ c.target ∩ c.symm ⁻¹' c'.source) ∧
      ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A B ∞,
        ∀ w : A, (e w : ℂ) = (c' (c.symm (w.val,t))).1 := by
  let h := g.trans g'.symm
  have hz₁ : z ∈ g.source := by rwa [hsource]
  have hz₂ : (c' (c.symm (z,t))).1 ∈ g'.source := by
    rw [hsource']
    simpa only [Set.mem_ofPred_eq, ← ht', Prod.mk.eta] using c'.map_source hz'
  have heq : g z = g' ((c' (c.symm (z,t))).1) := by
    apply hj
    rw [hinc z hz₁, hinc' _ hz₂]
    have he : ((c' (c.symm (z,t))).1,t') = c' (c.symm (z,t)) :=
      Prod.ext rfl ht'.symm
    rw [he, c'.left_inv hz']
  have hzh : z ∈ h.source := by
    refine ⟨hz₁, ?_⟩
    change g z ∈ g'.target
    rw [heq]
    exact g'.map_source hz₂
  have hval (w : ℂ) (hw : w ∈ h.source) :
      c' (c.symm (w,t)) = (h w,t') := by
    have hh : h w ∈ g'.source := g'.map_target hw.2
    have hjw : j (g' (h w)) = j (g w) := congrArg j (g'.right_inv hw.2)
    rw [hinc' _ hh, hinc _ hw.1] at hjw
    rw [← hjw]
    apply c'.right_inv
    simpa only [hsource', Set.mem_ofPred_eq] using hh
  refine ⟨⟨h.source,h.open_source⟩,⟨h.target,h.open_target⟩,hzh,?_,?_,?_⟩
  · intro w hw
    refine ⟨by simpa only [hsource, Set.mem_ofPred_eq] using (show w ∈ g.source from hw.1), ?_⟩
    have hh : h w ∈ g'.source := g'.map_target hw.2
    have hjw : j (g' (h w)) = j (g w) := congrArg j (g'.right_inv hw.2)
    rw [hinc' _ hh, hinc _ hw.1] at hjw
    change c.symm (w,t) ∈ c'.source
    rw [← hjw]
    apply c'.map_target
    simpa only [hsource', Set.mem_ofPred_eq] using hh
  · exact partialHomeomorphDiffeomorph 𝓘(ℂ) 𝓘(ℂ) h
      (hgi'.comp (hg.mono inter_subset_left) (fun _ hw ↦ hw.2))
      (hgi.comp (hg'.mono inter_subset_left) (fun _ hw ↦ hw.2))
  · intro w
    exact (congrArg Prod.fst (hval w.val w.property)).symm
end HolomorphicAnosov

namespace HolomorphicAnosov
open Set TopologicalSpace
universe u v w
/-- Scalar box parameters whose ambient slices belong to a partition have holomorphic overlap
transitions. -/
theorem scalarBoxOverlapOfPartition
    {M : Type u} {R : Type v} {ι : Type w} {L : ι → Type w}
    [TopologicalSpace M] [TopologicalSpace R]
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
    (j : ∀ i, L i → M) (hj : ∀ i, Function.Injective (j i))
    (hd : ∀ i i' z z', j i z = j i' z' → i = i')
    (c c' : OpenPartialHomeomorph M (ℂ × R)) (t t' : R)
    (i i' : ι) (g : OpenPartialHomeomorph ℂ (L i))
    (g' : OpenPartialHomeomorph ℂ (L i'))
    (hsource : g.source = {z | (z,t) ∈ c.target})
    (hsource' : g'.source = {z | (z,t') ∈ c'.target})
    (hinc : ∀ z ∈ g.source, j i (g z) = c.symm (z,t))
    (hinc' : ∀ z ∈ g'.source, j i' (g' z) = c'.symm (z,t'))
    (hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g g.source)
    (hgi : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g.symm g.target)
    (hg' : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g' g'.source)
    (hgi' : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g'.symm g'.target)
    (z : ℂ) (hz : (z,t) ∈ c.target)
    (hz' : c.symm (z,t) ∈ c'.source)
    (ht' : (c' (c.symm (z,t))).2 = t') :
    ∃ (A B : Opens ℂ), z ∈ A ∧
      (∀ w ∈ A, (w,t) ∈ c.target ∩ c.symm ⁻¹' c'.source) ∧
      ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A B ∞,
        ∀ w : A, (e w : ℂ) = (c' (c.symm (w.val,t))).1 := by
  have hz₁ : z ∈ g.source := by rwa [hsource]
  have hz₂ : (c' (c.symm (z,t))).1 ∈ g'.source := by
    rw [hsource']
    simpa only [Set.mem_ofPred_eq, ← ht', Prod.mk.eta] using c'.map_source hz'
  have hij : i = i' := by
    apply hd i i' (g z) (g' ((c' (c.symm (z,t))).1))
    rw [hinc z hz₁, hinc' _ hz₂]
    have he : ((c' (c.symm (z,t))).1,t') = c' (c.symm (z,t)) :=
      Prod.ext rfl ht'.symm
    rw [he, c'.left_inv hz']
  subst i'
  exact scalarBoxOverlapOnLeaf c c' t t' (j i) (hj i) g g'
    hsource hsource' hinc hinc' hg hgi hg' hgi' z hz hz' ht'
end HolomorphicAnosov
noncomputable section
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u v
/-- A point-preserving intrinsic homeomorphism between immersed complex leaves is a biholomorphism. -/
def pointPreservingLeafBiholomorph
    {d : ℕ} {L K : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    [TopologicalSpace K] [ChartedSpace (ComplexModel 1) K]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (i : L → M) (j : K → M) (e : L ≃ₜ K)
    (hi : ContMDiff (complexModel 1) (complexModel d) ∞ i)
    (hj : ContMDiff (complexModel 1) (complexModel d) ∞ j)
    (hii : ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞ i z)
    (hji : ∀ z, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞ j z)
    (he : ∀ z, j (e z) = i z) : Diffeomorph (complexModel 1) (complexModel 1) L K ∞ where
  toEquiv := e.toEquiv
  contMDiff_toFun := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt (hji (e z))).mpr
    refine ⟨e.continuous.continuousAt, ?_⟩
    have hcomp : j ∘ e = i := funext he
    rw [hcomp]
    exact hi z
  contMDiff_invFun := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt (hii (e.symm z))).mpr
    refine ⟨e.symm.continuous.continuousAt, ?_⟩
    have hcomp : i ∘ e.symm = j := by
      funext w
      simpa using (he (e.symm w)).symm
    rw [hcomp]
    exact hj z
end HolomorphicAnosov.Ghys
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Manifold
namespace HolomorphicAnosov
universe u v w
/-- Parametrizations of the stable and unstable plaque families yield a local product on open
subsets of the central intrinsic leaves. -/
theorem localProductFromParameters
    {M : Type u} [TopologicalSpace M]
    {ιu ιs : Type v} {Lu : ιu → Type w} {Ls : ιs → Type w}
    [∀ i, TopologicalSpace (Lu i)] [∀ i, ChartedSpace ℂ (Lu i)]
    [∀ i, TopologicalSpace (Ls i)]
    (iu : ∀ i, Lu i → M) (is : ∀ i, Ls i → M)
    (A : Opens ℂ) [ConnectedSpace A]
    {Z : Type*} [TopologicalSpace Z] [ConnectedSpace Z]
    (Q : A × Z → M) (hQ : Topology.IsOpenEmbedding Q)
    (v₀ : A) (z₀ : Z)
    (hu : ∀ z : Z, ∃ i : ιu, ∃ V : Opens (Lu i),
      ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A V ∞,
        ∀ v : A, iu i (e v).val = Q (v,z))
    (hs : ∀ v : A, ∃ i : ιs, ∃ V : Opens (Ls i),
      ∃ e : Z ≃ₜ V, ∀ z : Z, is i (e z).val = Q (v,z)) :
    ∃ (qu : ιu) (qs : ιs) (Pu : Opens (Lu qu)) (Ps : Opens (Ls qs)),
      IsConnected (Pu : Set (Lu qu)) ∧ IsConnected (Ps : Set (Ls qs)) ∧
      ∃ (u₀ : Pu) (s₀ : Ps) (O : Opens M) (Ψ : (Pu × Ps) ≃ₜ O),
        iu qu u₀.val = Q (v₀,z₀) ∧ is qs s₀.val = Q (v₀,z₀) ∧
        (Ψ (u₀,s₀)).val = Q (v₀,z₀) ∧
        (∀ u : Pu, (Ψ (u,s₀)).val = iu qu u.val) ∧
        (∀ t : Ps, (Ψ (u₀,t)).val = is qs t.val) ∧
        (∀ t : Ps, ∃ i : ιu, ∃ V : Opens (Lu i),
          ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Pu V ∞,
            ∀ u : Pu, iu i (e u).val = (Ψ (u,t)).val) ∧
        (∀ u : Pu, ∃ i : ιs, ∃ V : Opens (Ls i),
          ∃ e : Ps ≃ₜ V, ∀ t : Ps, is i (e t).val = (Ψ (u,t)).val) := by
  obtain ⟨qu,Pu,eu,heu⟩ := hu z₀
  obtain ⟨qs,Ps,es,hes⟩ := hs v₀
  let O : Opens M := ⟨Set.range Q,hQ.isOpen_range⟩
  let Ψ : (Pu × Ps) ≃ₜ O :=
    (eu.symm.toHomeomorph.prodCongr es.symm).trans hQ.isEmbedding.toHomeomorph
  have hΨ (u : Pu) (t : Ps) : (Ψ (u,t)).val = Q (eu.symm u,es.symm t) := rfl
  refine ⟨qu,qs,Pu,Ps,?_,?_,eu v₀,es z₀,O,Ψ,heu v₀,hes z₀,?_,?_,?_,?_,?_⟩
  · exact isConnected_iff_connectedSpace.mpr
      (eu.toHomeomorph.connectedSpace_iff.mp inferInstance)
  · exact isConnected_iff_connectedSpace.mpr
      (es.connectedSpace_iff.mp inferInstance)
  · rw [hΨ, eu.symm_apply_apply, es.symm_apply_apply]
  · intro u
    rw [hΨ, es.symm_apply_apply]
    simpa using (heu (eu.symm u)).symm
  · intro t
    rw [hΨ, eu.symm_apply_apply]
    simpa using (hes (es.symm t)).symm
  · intro t
    obtain ⟨i,V,e,he⟩ := hu (es.symm t)
    exact ⟨i,V,eu.symm.trans e,fun u ↦ he (eu.symm u)⟩
  · intro u
    obtain ⟨i,V,e,he⟩ := hs (eu.symm u)
    exact ⟨i,V,es.symm.trans e,fun t ↦ he (es.symm t)⟩
end HolomorphicAnosov


noncomputable section
namespace HolomorphicAnosov.Ghys
universe u
open Set _root_.Topology TopologicalSpace
open scoped ContDiff Manifold Bundle
set_option autoImplicit false
variable {d : ℕ} {M : Type u}
variable [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
variable [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real

section ScalarModelTransport
open Filter _root_.Topology
variable (L : Type u) [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]

@[instance_reducible]
def scalarNativeCharts : ChartedSpace ℂ L where
  atlas := (fun c : OpenPartialHomeomorph L (ComplexModel 1) ↦
    c.trans (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)).toHomeomorph.toOpenPartialHomeomorph) '' atlas (ComplexModel 1) L
  chartAt x := (chartAt (ComplexModel 1) x).trans
    (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)).toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt _ x, chart_mem_atlas _ x, rfl⟩

theorem scalarNativeCharts_isManifold [IsManifold (complexModel 1) ∞ L] :
    let := scalarNativeCharts L
    IsManifold 𝓘(ℂ) ∞ L := by
  let := scalarNativeCharts L
  apply isManifold_of_contDiffOn 𝓘(ℂ) ∞ L
  rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  let E := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  have ht : ContDiffOn ℂ ∞ (c.symm.trans c') (c.symm.trans c').source := by
    have h := ((contDiffGroupoid ∞ (complexModel 1)).compatible hc hc').1
    change ContDiffOn ℂ ∞ ((complexModel 1) ∘ (c.symm.trans c') ∘ (complexModel 1).symm)
      ((complexModel 1).symm ⁻¹' (c.symm.trans c').source ∩ Set.range (complexModel 1)) at h
    simpa only [complexModel, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ] using h
  have hcomp := E.contDiff.comp_contDiffOn (ht.comp E.symm.contDiff.contDiffOn
    (show MapsTo E.symm (E.symm ⁻¹' (c.symm.trans c').source) (c.symm.trans c').source from
      fun _ h ↦ h))
  simpa [E, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans_symm,
    Function.comp_def, ← Set.preimage_comp] using hcomp

def scalarNativeChartsDiffeomorph :
    letI := scalarNativeCharts L
    Diffeomorph 𝓘(ℂ) (complexModel 1) L L ∞ := by
  let := scalarNativeCharts L
  refine { toEquiv := Equiv.refl L, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    apply contMDiffAt_iff.mpr
    refine ⟨continuousAt_id, ?_⟩
    simp only [extChartAt_coe, extChartAt_coe_symm, complexModel,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.range_id, contDiffWithinAt_univ]
    let E := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
    let c := chartAt (ComplexModel 1) x
    change ContDiffAt ℂ ∞ (fun z ↦ c (c.symm (E.symm z))) (E (c x))
    apply E.symm.contDiff.contDiffAt.congr_of_eventuallyEq
    have ht : ∀ᶠ z in 𝓝 (E (c x)), E.symm z ∈ c.target :=
      E.symm.continuous.continuousAt.preimage_mem_nhds (by
        simpa using c.open_target.mem_nhds (mem_chart_target (ComplexModel 1) x))
    filter_upwards [ht] with z hz
    exact c.right_inv hz
  · intro x
    apply contMDiffAt_iff.mpr
    refine ⟨continuousAt_id, ?_⟩
    simp only [extChartAt_coe, extChartAt_coe_symm, complexModel,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.range_id, contDiffWithinAt_univ]
    let E := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
    let c := chartAt (ComplexModel 1) x
    change ContDiffAt ℂ ∞ (fun z ↦ E (c (c.symm z))) (c x)
    apply E.contDiff.contDiffAt.congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds (mem_chart_target (ComplexModel 1) x)] with z hz
    exact congrArg E (c.right_inv hz)

/-- Transport from the one-coordinate complex model to `ℂ` preserves holomorphicity of a local map
and its inverse. -/
theorem scalarNativeCharts_localMap
    {K : Type*} [TopologicalSpace K] [ChartedSpace (ComplexModel 1) K]
    [IsManifold (complexModel 1) ∞ L] [IsManifold (complexModel 1) ∞ K]
    (h : OpenPartialHomeomorph L K)
    (hf : ContMDiffOn (complexModel 1) (complexModel 1) ∞ h h.source)
    (hi : ContMDiffOn (complexModel 1) (complexModel 1) ∞ h.symm h.target) :
    letI := scalarNativeCharts L; letI := scalarNativeCharts K
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ h h.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ h.symm h.target := by
  let eL := scalarNativeChartsDiffeomorph L
  let eK := scalarNativeChartsDiffeomorph K
  letI := scalarNativeCharts L
  letI := scalarNativeCharts K
  constructor
  · have h₁ := hf.comp eL.contMDiff.contMDiffOn (fun z hz ↦ hz)
    have h₂ := eK.symm.contMDiff.comp_contMDiffOn h₁
    exact h₂
  · have h₁ := hi.comp eK.contMDiff.contMDiffOn (fun z hz ↦ hz)
    have h₂ := eL.symm.contMDiff.comp_contMDiffOn h₁
    exact h₂

end ScalarModelTransport

/-! This file constructs finite scalar holomorphic flowboxes and local products on intrinsic stable
and unstable leaves for a holomorphic Anosov diffeomorphism with complex rank-one unstable
distribution. (Hirsch–Pugh–Shub, §7, pp. 115–116; Shub, Prop. 10.10, pp. 126–127; Ghys, Prop.
2.2, pp. 589–590; Demailly, I §§3.A, 3.C) -/
theorem native_actual_invariant_flowbox_input
    [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    let scalarSlice := fun (c : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (t : Fin (2 * d - 2) → ℝ) ↦
      (⟨{z | (z, t) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
    let overlapDomain := fun (c c' : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) ↦ c.target ∩ c.symm ⁻¹' c'.source
    let overlapScalar := fun (c c' : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (p : ℂ × (Fin (2 * d - 2) → ℝ)) ↦
      (c' (c.symm p)).1
    ∃ (ιs ιu : Type u) (Ls : ιs → Type u) (Lu : ιu → Type u)
      (topS : ∀ i, TopologicalSpace (Ls i)) (topU : ∀ i, TopologicalSpace (Lu i)),
    let := topS
    let := topU
    ∃ (chartS : ∀ i, ChartedSpace (Fin (2 * d - 2) → ℝ) (Ls i))
      (chartU : ∀ i, ChartedSpace (Fin 2 → ℝ) (Lu i)),
    let := chartS
    let := chartU
    ∃ (smoothS : ∀ i, IsManifold 𝓘(ℝ, Fin (2 * d - 2) → ℝ) ∞ (Ls i))
      (smoothU : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Lu i)),
    let := smoothS
    let := smoothU
    ∃ (S : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls (fun _ ↦ 2 * d - 2))
      (U : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu (fun _ ↦ 2))
      (complexChart : ∀ i, ChartedSpace ℂ (Lu i)),
      (∀ i, letI := complexChart i
        IsManifold 𝓘(ℂ) ∞ (Lu i)) ∧
      (∀ i, letI := complexChart i
        ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
        ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z)) ∧
      (∃ m : MetricSpace M,
        m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
          (inferInstance : TopologicalSpace M) ∧
        (∀ i (x : Ls i) y,
          (∃ z, (S.leaf i).inclusion z = y) ↔
            @ForwardAsymptotic M m (f : M → M) ((S.leaf i).inclusion x) y) ∧
        (∀ i (x : Lu i) y,
          (∃ z, (U.leaf i).inclusion z = y) ↔
            @ForwardAsymptotic M m (f.symm : M → M) ((U.leaf i).inclusion x) y)) ∧
      Nonempty (HPS.LeafDynamicalInvariance S f.toReal) ∧
      Nonempty (HPS.LeafDynamicalInvariance U f.toReal) ∧
      (∃ (βs βu : Type u) (Ts : βs → Type u) (Tu : βu → Type u)
        (topTs : ∀ b, TopologicalSpace (Ts b)) (topTu : ∀ b, TopologicalSpace (Tu b)),
        let := topTs
        let := topTu
        Nonempty (HPS.LaminationBoxes S βs (fun _ ↦ 2 * d - 2) Ts) ∧
        Nonempty (HPS.LaminationBoxes U βu (fun _ ↦ 2) Tu)) ∧
      (∃ (n : ℕ) (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
        (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
        (label : ∀ i, T i → ιu) (branch : ∀ i t, Opens (Lu (label i t)))
        (parametrization : ∀ i t, letI := complexChart (label i t)
          Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (scalarSlice (c i) t.val) (branch i t) ∞),
        (∀ x : M, ∃ i, x ∈ (c i).source) ∧
        (∀ i p, p ∈ (c i).target → p.2 ∈ T i) ∧
        (∀ i t (z : scalarSlice (c i) t.val),
          (c i).symm (z.val, t.val) =
            (U.leaf (label i t)).inclusion ((parametrization i t z).val)) ∧
        (∀ i j, let Ω := overlapDomain (c i) (c j)
          let h := overlapScalar (c i) (c j)
          ∀ p ∈ Ω, ∃ (A B : Opens ℂ), p.1 ∈ A ∧
            (∀ z ∈ A, (z, p.2) ∈ Ω) ∧
            ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A B ∞,
              ∀ z : A, (e z : ℂ) = h (z.val, p.2))) ∧
      (∀ x : M,
        ∃ (qu : ιu) (qs : ιs),
        let := complexChart qu
        ∃ (Pu : Opens (Lu qu)) (Ps : Opens (Ls qs)),
          IsConnected (Pu : Set (Lu qu)) ∧ IsConnected (Ps : Set (Ls qs)) ∧
          ∃ (u₀ : Pu) (s₀ : Ps) (O : Opens M) (Ψ : (Pu × Ps) ≃ₜ O),
            (U.leaf qu).inclusion u₀.val = x ∧
            (S.leaf qs).inclusion s₀.val = x ∧
            (Ψ (u₀, s₀)).val = x ∧
            (∀ u : Pu, (Ψ (u, s₀)).val = (U.leaf qu).inclusion u.val) ∧
            (∀ t : Ps, (Ψ (u₀, t)).val = (S.leaf qs).inclusion t.val) ∧
              (∀ t : Ps, ∃ q : ιu,
                let := complexChart q
                ∃ (V : Opens (Lu q)) (b : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Pu V ∞),
                  ∀ u : Pu, (U.leaf q).inclusion (b u).val = (Ψ (u, t)).val) ∧
              (∀ u : Pu, ∃ q : ιs,
                ∃ (V : Opens (Ls q)) (b : Ps ≃ₜ V),
                  ∀ t : Ps, (S.leaf q).inclusion (b t).val = (Ψ (u, t)).val) ∧
              (d = 1 → (∀ t : Ps, t.val = s₀.val) ∧
                ∃ j : Pu ≃ₜ O,
                  (∀ u : Pu, (j u).val = (U.leaf qu).inclusion u.val) ∧
                  (∀ w : O, Ψ.symm w = (j.symm w, s₀)))) := by
  
  classical
  by_cases hM : IsEmpty M
  · let := hM
    let ιs : Type u := ULift.{u} Empty
    let ιu : Type u := ULift.{u} Empty
    let Ls : ιs → Type u := fun i ↦ isEmptyElim i
    let Lu : ιu → Type u := fun i ↦ isEmptyElim i
    let topS : ∀ i, TopologicalSpace (Ls i) := fun i ↦ isEmptyElim i
    let topU : ∀ i, TopologicalSpace (Lu i) := fun i ↦ isEmptyElim i
    let : ∀ i, TopologicalSpace (Ls i) := topS
    let : ∀ i, TopologicalSpace (Lu i) := topU
    let chartS : ∀ i, ChartedSpace (Fin (2 * d - 2) → ℝ) (Ls i) :=
      fun i ↦ isEmptyElim i
    let chartU : ∀ i, ChartedSpace (Fin 2 → ℝ) (Lu i) :=
      fun i ↦ isEmptyElim i
    let : ∀ i, ChartedSpace (Fin (2 * d - 2) → ℝ) (Ls i) := chartS
    let : ∀ i, ChartedSpace (Fin 2 → ℝ) (Lu i) := chartU
    let smoothS : ∀ i, IsManifold 𝓘(ℝ, Fin (2 * d - 2) → ℝ) ∞ (Ls i) :=
      fun i ↦ isEmptyElim i
    let smoothU : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Lu i) :=
      fun i ↦ isEmptyElim i
    let : ∀ i, IsManifold 𝓘(ℝ, Fin (2 * d - 2) → ℝ) ∞ (Ls i) := smoothS
    let : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Lu i) := smoothU
    let S : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls (fun _ ↦ 2 * d - 2) :=
      { leaf := fun i ↦ isEmptyElim i
        cover := fun p ↦ isEmptyElim p
        disjoint := fun i ↦ isEmptyElim i }
    let U : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu (fun _ ↦ 2) :=
      { leaf := fun i ↦ isEmptyElim i
        cover := fun p ↦ isEmptyElim p
        disjoint := fun i ↦ isEmptyElim i }
    let complexChart : ∀ i, ChartedSpace ℂ (Lu i) :=
      fun i ↦ isEmptyElim i
    let βs : Type u := ULift.{u} Empty
    let βu : Type u := ULift.{u} Empty
    let Ts : βs → Type u := fun i ↦ ULift.{u} Empty
    let Tu : βu → Type u := fun i ↦ ULift.{u} Empty
    let topTs : ∀ i, TopologicalSpace (Ts i) := fun i ↦ inferInstance
    let topTu : ∀ i, TopologicalSpace (Tu i) := fun i ↦ inferInstance
    let : ∀ i, TopologicalSpace (Ts i) := topTs
    let : ∀ i, TopologicalSpace (Tu i) := topTu
    let invS : HPS.LeafDynamicalInvariance S f.toReal :=
      { permutation := Equiv.refl _
        transport := fun i ↦ isEmptyElim i
        intertwining := fun i ↦ isEmptyElim i }
    let invU : HPS.LeafDynamicalInvariance U f.toReal :=
      { permutation := Equiv.refl _
        transport := fun i ↦ isEmptyElim i
        intertwining := fun i ↦ isEmptyElim i }
    let boxesS : HPS.LaminationBoxes S βs (fun _ ↦ 2 * d - 2) Ts :=
      { boxes := fun i ↦ isEmptyElim i
        cover := fun p ↦ isEmptyElim p
        topology_generated := fun i ↦ isEmptyElim i }
    let boxesU : HPS.LaminationBoxes U βu (fun _ ↦ 2) Tu :=
      { boxes := fun i ↦ isEmptyElim i
        cover := fun p ↦ isEmptyElim p
        topology_generated := fun i ↦ isEmptyElim i }
    refine ⟨ιs, ιu, Ls, Lu, topS, topU, ?_⟩
    refine ⟨chartS, chartU, ?_⟩
    refine ⟨smoothS, smoothU, ?_⟩
    refine ⟨S, U, complexChart, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun i ↦ isEmptyElim i
    · exact fun i ↦ isEmptyElim i
    · exact ⟨MetricSpace.induced (isEmptyElim : M → ULift.{u} Empty) (by intro x; exact isEmptyElim x) inferInstance,
        Subsingleton.elim _ _,
        fun i x y ↦ isEmptyElim i,
        fun i x y ↦ isEmptyElim i⟩
    · exact ⟨invS⟩
    · exact ⟨invU⟩
    · exact ⟨βs, βu, Ts, Tu, topTs, topTu, ⟨boxesS⟩, ⟨boxesU⟩⟩
    · refine ⟨0, (fun i ↦ isEmptyElim i), (fun i ↦ isEmptyElim i),
        (fun i ↦ isEmptyElim i), (fun i t ↦ isEmptyElim i),
        (fun i t ↦ isEmptyElim i), ?_⟩
      exact ⟨fun x ↦ isEmptyElim x, fun i p ↦ isEmptyElim i, fun i t z ↦ isEmptyElim i,
        fun i j p hp ↦ isEmptyElim i⟩
    · intro x
      exact isEmptyElim x
  · let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    obtain ⟨C, rate, hC, hr, hr1, hs, hu⟩ := fixed_block_uniform_anosov_estimates f a
    have hi (x : M) (v w : TangentSpace (realModel d) x) :
        inner ℝ v w = a.metric.inner x v w := rfl
    have hb : Nonempty (TensorAnosovBounds f.toReal a.splitting a.metric) := by
      refine ⟨⟨C, rate, hC, hr, hr1, ?_, ?_⟩⟩
      · intro n x v hv
        have he : (realIterate (realModel d) f.toReal n : M → M) =
            (f : M → M)^[n] := rfl
        rw [he]
        simpa only [norm_eq_sqrt_real_inner, hi] using hs n x v hv
      · intro n x v hv
        have he : (realIterate (realModel d) f.toReal.symm n : M → M) =
            (f.symm : M → M)^[n] := rfl
        rw [he]
        simpa only [norm_eq_sqrt_real_inner, hi] using hu n x v hv
    let ambientMetric : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
    let : MetricSpace M := ambientMetric
    obtain ⟨hstableNative, hunstableNative⟩ :=
      HPS.anosov_global_lamination_tensor_metric f.toReal a.splitting a.metric hb
    obtain ⟨ιu, Lu, ru, topU, chartU, smoothU, U, hboxesU, hinvariantU,
      familiesU, coherentU, hextraU⟩ := hunstableNative
    let := topU
    let := chartU
    let := smoothU
    have hrankU (i : ιu) : ru i = 2 := by
      let := (U.leaf i).connected
      obtain ⟨z⟩ := (inferInstance : Nonempty (Lu i))
      exact ((U.leaf i).finrank_tangent z).symm.trans
        (TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two hRank _)
    have hrufun : ru = (fun _ ↦ 2) := funext hrankU
    cases hrufun
    obtain ⟨ιs, Ls, rs, topS, chartS, smoothS, S, hboxesS, hinvariantS,
      familiesS, coherentS, hextraS⟩ := hstableNative
    let := topS
    let := chartS
    let := smoothS
    have hrankS (i : ιs) : rs i = 2 * d - 2 := by
      let := (S.leaf i).connected
      obtain ⟨z⟩ := (inferInstance : Nonempty (Ls i))
      have hsum := Submodule.finrank_add_eq_of_isCompl
        (a.splitting.isCompl ((S.leaf i).inclusion z))
      rw [(S.leaf i).finrank_tangent z,
        TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two hRank,
        TheoremAProof.Dimension.original_real_tangent_finrank] at hsum
      omega
    have hrsfun : rs = (fun _ ↦ 2 * d - 2) := funext hrankS
    cases hrsfun
    obtain ⟨_, _, _, _, ⟨identificationS, _⟩, _, _⟩ := hextraS
    obtain ⟨_, _, _, _, ⟨identificationU, _⟩, _, _⟩ := hextraU
    have hmetric : ∃ m : MetricSpace M,
        m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
          (inferInstance : TopologicalSpace M) ∧
        (∀ i (x : Ls i) y,
          (∃ z, (S.leaf i).inclusion z = y) ↔
            @ForwardAsymptotic M m (f : M → M) ((S.leaf i).inclusion x) y) ∧
        (∀ i (x : Lu i) y,
          (∃ z, (U.leaf i).inclusion z = y) ↔
            @ForwardAsymptotic M m (f.symm : M → M) ((U.leaf i).inclusion x) y) := by
      refine ⟨ambientMetric, rfl, ?_, ?_⟩
      · intro i x y
        exact Set.ext_iff.mp (identificationS.range_eq_forwardAsymptotic i x) y
      · intro i x y
        exact Set.ext_iff.mp (identificationU.range_eq_forwardAsymptotic i x) y
    obtain ⟨βs, ds, Ts, topTs, ⟨Bs⟩⟩ := hboxesS
    let := topTs
    have hds : ds = (fun _ ↦ 2 * d - 2) :=
      funext (fun b ↦ (Bs.boxes b).dimension_eq)
    cases hds
    obtain ⟨βu, du, Tu, topTu, ⟨Bu⟩⟩ := hboxesU
    let := topTu
    have hdu : du = (fun _ ↦ 2) := funext (fun b ↦ (Bu.boxes b).dimension_eq)
    cases hdu
    have hsAP (x : M) (n : ℕ) (v : TangentSpace (realModel d) x)
        (hv : v ∈ a.splitting.stable.toDistribution x) :
        hyperbolicRiemannianNorm a.metric
          (mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) x v) ≤
            max C 1 * rate ^ n * hyperbolicRiemannianNorm a.metric v := by
      have h := (hs n x v hv).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hr.le n)) (norm_nonneg v))
      simpa only [hyperbolicRiemannianNorm, norm_eq_sqrt_real_inner, hi] using h
    have huAP (x : M) (n : ℕ) (v : TangentSpace (realModel d) x)
        (hv : v ∈ a.splitting.unstable.toDistribution x) :
        hyperbolicRiemannianNorm a.metric
          (mfderiv (realModel d) (realModel d) ((f.symm : M → M)^[n]) x v) ≤
            max C 1 * rate ^ n * hyperbolicRiemannianNorm a.metric v := by
      have h := (hu n x v hv).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hr.le n)) (norm_nonneg v))
      simpa only [hyperbolicRiemannianNorm, norm_eq_sqrt_real_inner, hi] using h
    let dynS := Classical.choice hinvariantS
    let dynU := Classical.choice hinvariantU
    obtain ⟨productMetric, β, γ, ε, hγ, hβ, hε, hproductTopology,
      ⟨stableOrbitPlaques⟩, ⟨unstableOrbitPlaques⟩, bracket, hbracketContinuous,
      hbracketIntersection, products⟩ :=
      selectedPartitionProducts f.toReal a.splitting a.metric (max C 1) rate
        (le_max_right C 1) hr hr1 hsAP huAP S U dynS dynU
    let NS := nativeInvariantLeafSystemOfPartition a.splitting.stable.toDistribution f.toReal S dynS
    let NU := nativeInvariantLeafSystemInverse a.splitting.unstable.toDistribution f.toReal
      (nativeInvariantLeafSystemOfPartition a.splitting.unstable.toDistribution f.toReal U dynU)
    have hRealBoxes (x : M) :
        ∃ (Ds : Opens (Fin (2*d-2) → ℝ)) (Du : Opens (Fin 2 → ℝ))
          (O : Opens M) (e : (Ds × Du) ≃ₜ O), x ∈ O ∧
          (∀ w : Du, ∃ (i : ιs) (V : Opens (Ls i)) (c : Ds ≃ₜ V),
            ∀ z : Ds, (e (z,w)).val = (S.leaf i).inclusion (c z).val) ∧
          (∀ z : Ds, ∃ (i : ιu) (V : Opens (Lu i)) (c : Du ≃ₜ V),
            ∀ w : Du, (e (z,w)).val = (U.leaf i).inclusion (c w).val) := by
      obtain ⟨Ds, Du, O, e, hx, hs, hu⟩ := adaptedProduct_real_box f.toReal
        a.splitting.stable.toDistribution a.splitting.unstable.toDistribution productMetric
        NS NU hγ hε bracket hbracketIntersection stableOrbitPlaques unstableOrbitPlaques hβ
        hproductTopology x (Classical.choice (products x))
      refine ⟨Ds, Du, O, e, hx, ?_, ?_⟩
      · intro w
        obtain ⟨y, V, c, hc⟩ := hs w
        exact ⟨Classical.choose (S.cover y), V, c, hc⟩
      · intro z
        obtain ⟨y, V, c, hc⟩ := hu z
        exact ⟨Classical.choose (U.cover y), V, c, hc⟩
    have hmetricCopy := hmetric
    obtain ⟨sourceMetric, hsourceMetricTopology, hrS, hrU⟩ := hmetricCopy
    letI : Nonempty M := not_isEmpty_iff.mp hM
    obtain ⟨presentation, hpresS, hpresU, hpresIdentS, hpresIdentU⟩ :=
      intrinsicPresentation_of_native_real_boxes f a hRank S U sourceMetric
        hsourceMetricTopology hrS hrU hRealBoxes
    obtain ⟨K, T, hT, hdim, hreal⟩ :=
      exists_continuous_complex_rank_one_subbundle a.splitting.unstable hRank
    have upgrades (i : ιu) : Nonempty (NativeLeafComplexUpgrade (d := d) (r := 2) 1
        (U.leaf i).inclusion) := by
      apply nativeLeafComplexUpgrade_of_complex_tangent (k := 1)
        (U.leaf i).inclusion a.splitting.unstable (U.leaf i).immersion
        (U.leaf i).tangent T
      intro z
      rw [(U.leaf i).tangent, hT]
      exact hreal ((U.leaf i).inclusion z)
    let upgrade (i : ιu) := Classical.choice (upgrades i)
    let complexChart (i : ιu) : ChartedSpace ℂ (Lu i) :=
      letI := (upgrade i).charts
      scalarNativeCharts (Lu i)
    have hcomplex (i : ιu) : letI := complexChart i; IsManifold 𝓘(ℂ) ∞ (Lu i) := by
      let := (upgrade i).charts
      let := (upgrade i).complex_manifold
      exact scalarNativeCharts_isManifold (Lu i)
    have hinclusion (i : ιu) : letI := complexChart i
        ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
        ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z) := by
      let := (upgrade i).charts
      let := (upgrade i).complex_manifold
      let := complexChart i
      let := hcomplex i
      let e := scalarNativeChartsDiffeomorph (Lu i)
      have heq : (U.leaf i).inclusion ∘ e = (U.leaf i).inclusion := rfl
      constructor
      · exact heq ▸ (upgrade i).inclusion_holomorphic.comp e.contMDiff
      · intro z
        rw [← heq, mfderiv_comp z
          ((upgrade i).inclusion_holomorphic.mdifferentiable (by simp) (e z))
          (e.contMDiff.mdifferentiable (by simp) z)]
        apply ((upgrade i).inclusion_immersion (e z)).mfderiv_injective (by simp) |>.comp
        exact (e.mfderivToContinuousLinearEquiv (by simp) z).injective
    letI := presentation.realCharts
    let pScalar (q : Quotient presentation.foliations.unstablePartition) :=
      letI := presentation.foliations.unstableTopology q
      letI := presentation.complexLeaves.charts q
      scalarNativeCharts (IntrinsicFoliationLeaf presentation.foliations.unstablePartition q)
    have pSmooth (q : Quotient presentation.foliations.unstablePartition) :
        letI := presentation.foliations.unstableTopology q
        letI := pScalar q
        IsManifold 𝓘(ℂ) ∞
          (IntrinsicFoliationLeaf presentation.foliations.unstablePartition q) := by
      letI := presentation.foliations.unstableTopology q
      letI := presentation.complexLeaves.charts q
      letI := presentation.complexLeaves.complex_manifold q
      exact scalarNativeCharts_isManifold _
    have pHol (x y : M) (e : LocalPlaqueTransport presentation.foliations x y) :
        letI := pScalar (Quotient.mk presentation.foliations.unstablePartition x)
        letI := pScalar (Quotient.mk presentation.foliations.unstablePartition y)
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.map e.map.source ∧
          ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ e.map.symm e.map.target := by
      letI := presentation.complexLeaves.charts (Quotient.mk _ x)
      letI := presentation.complexLeaves.charts (Quotient.mk _ y)
      letI := presentation.complexLeaves.complex_manifold (Quotient.mk _ x)
      letI := presentation.complexLeaves.complex_manifold (Quotient.mk _ y)
      obtain ⟨he, hi⟩ := intrinsicPresentation_plaque_holomorphic f a hRank presentation x y e
      exact scalarNativeCharts_localMap _ e.map he hi
    have hIdentUComplex (q : Quotient presentation.foliations.unstablePartition) :
        letI := presentation.foliations.unstableTopology q
        letI := pScalar q
        ∃ i, letI := complexChart i
          ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
            (IntrinsicFoliationLeaf presentation.foliations.unstablePartition q) (Lu i) ∞,
            ∀ z, (U.leaf i).inclusion (e z) = z.val := by
      letI := presentation.foliations.unstableTopology q
      letI := presentation.foliations.unstableCharts q
      letI := presentation.unstableSmooth q
      letI := presentation.complexLeaves.charts q
      letI := presentation.complexLeaves.complex_manifold q
      obtain ⟨i, e, he⟩ := hpresIdentU q
      letI := (upgrade i).charts
      letI := (upgrade i).complex_manifold
      have hpImm (z : IntrinsicFoliationLeaf presentation.foliations.unstablePartition q) :
          Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
            (Subtype.val : IntrinsicFoliationLeaf presentation.foliations.unstablePartition q → M) z := by
        apply complex_holomorphic_immersion_of_injective_derivative
          (presentation.unstable_holomorphic q z)
        apply complexDerivative_injective_of_compatible_real_charts (r := 2)
        · exact ((presentation.unstable_real_complex_compatible q).1 z).mdifferentiableAt (by simp)
        · exact ((presentation.unstable_real_complex_compatible q).2 z).mdifferentiableAt (by simp)
        · exact (presentation.unstable_holomorphic q z).mdifferentiableAt (by simp)
        · rw [← presentation.unstable_inclusion_eq q]
          exact (presentation.unstableNative q).immersion.mfderiv_injective (by simp) z
      let ec := pointPreservingLeafBiholomorph (U.leaf i).inclusion Subtype.val e.toHomeomorph
        (upgrade i).inclusion_holomorphic (presentation.unstable_holomorphic q)
        (upgrade i).inclusion_immersion hpImm he
      let en := scalarNativeChartsDiffeomorph (Lu i)
      let ep := scalarNativeChartsDiffeomorph
        (IntrinsicFoliationLeaf presentation.foliations.unstablePartition q)
      letI := complexChart i
      letI := pScalar q
      refine ⟨i, (en.trans (ec.trans ep.symm)).symm, ?_⟩
      intro z
      exact (he (e.symm z)).symm.trans (congrArg Subtype.val (e.apply_symm_apply z))
    refine ⟨ιs, ιu, Ls, Lu, topS, topU, chartS, chartU, smoothS, smoothU, S, U, ?_⟩
    refine Exists.imp (fun complexChart (h : _ ∧ _ ∧ _ ∧ _) ↦
      ⟨h.1, h.2.1, hmetric, hinvariantS, hinvariantU,
        ⟨βs, βu, Ts, Tu, topTs, topTu, ⟨Bs⟩, ⟨Bu⟩⟩,
        h.2.2.1, h.2.2.2⟩) ?_
    refine ⟨complexChart, hcomplex, hinclusion, ?_⟩
    let scalarSlice := fun (c : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (t : Fin (2 * d - 2) → ℝ) ↦
      (⟨{z | (z, t) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
    let overlapDomain := fun (c c' : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) ↦ c.target ∩ c.symm ⁻¹' c'.source
    let overlapScalar := fun (c c' : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (p : ℂ × (Fin (2 * d - 2) → ℝ)) ↦
      (c' (c.symm p)).1
    have hNativeBox (x : M) :
        ∃ (T : Opens (Fin (2*d-2) → ℝ))
          (c : OpenPartialHomeomorph M (ℂ × (Fin (2*d-2) → ℝ))),
          x ∈ c.source ∧ (∀ p ∈ c.target, p.2 ∈ T) ∧
          ∀ t : T, ∃ i : ιu, letI := complexChart i
            ∃ g : OpenPartialHomeomorph ℂ (Lu i),
              g.source = {z | (z,t.val) ∈ c.target} ∧
              ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g g.source ∧
              ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ g.symm g.target ∧
              ∀ z ∈ g.source, (U.leaf i).inclusion (g z) = c.symm (z,t.val) := by
      let F := presentation.foliations
      obtain ⟨b, hb⟩ := F.cover x
      let zw := (F.box b).chart.symm ⟨x,hb⟩
      let z₀ := zw.1
      let w₀ := zw.2
      have hcenter : ((F.box b).chart (z₀,w₀)).val = x :=
        congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨x,hb⟩)
      obtain ⟨k,hk,hparams⟩ := native_scalar_box_parameter F pScalar pSmooth pHol b z₀ w₀
      let c := (nativeScalarInverseBox F b z₀ w₀ k).symm
      refine ⟨⟨Metric.ball 0 1,Metric.isOpen_ball⟩,c,?_,?_,?_⟩
      · rw [← hcenter]
        exact nativeScalarInverseBox_center F b z₀ w₀ k hk
      · intro p hp
        exact (show p ∈ k.source ×ˢ Metric.ball 0 1 by
          simpa only [c, OpenPartialHomeomorph.symm_target,
            nativeScalarInverseBox_source] using hp).2
      · intro t
        let y := ((F.box b).chart (t,w₀)).val
        let q := Quotient.mk F.unstablePartition y
        letI := pScalar q
        obtain ⟨g,hgsrc,hg,hgi,hgval⟩ := hparams t
        obtain ⟨i,e,he⟩ := hIdentUComplex q
        letI := complexChart i
        let gN := g.transHomeomorph e.toHomeomorph
        have hsrc : gN.source = k.source := by
          simpa only [gN, OpenPartialHomeomorph.transHomeomorph_source] using hgsrc
        refine ⟨i,gN,?_,?_,?_,?_⟩
        · rw [hsrc]
          ext z
          simp only [c, OpenPartialHomeomorph.symm_target,
            nativeScalarInverseBox_source, Set.mem_ofPred_eq, Set.mem_prod]
          exact ⟨fun h ↦ ⟨h,t.property⟩, And.left⟩
        · exact e.contMDiff.comp_contMDiffOn hg
        · exact hgi.comp e.symm.contMDiff.contMDiffOn (fun z hz ↦ hz)
        · intro z hz
          have hz' : z ∈ k.source := hsrc ▸ hz
          change (U.leaf i).inclusion (e (g z)) = _
          rw [he, hgval z hz']
          exact (nativeScalarInverseBox_apply F b z₀ w₀ k z t.val t.property).symm
    suffices hboxes :
      (∃ (T : M → Opens (Fin (2 * d - 2) → ℝ))
        (c : M → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
        (label : ∀ i, T i → ιu) (branch : ∀ i t, Opens (Lu (label i t)))
        (parametrization : ∀ i t, letI := complexChart (label i t)
          Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (scalarSlice (c i) t.val) (branch i t) ∞),
        (∀ x : M, x ∈ (c x).source) ∧
        (∀ i p, p ∈ (c i).target → p.2 ∈ T i) ∧
        (∀ i t (z : scalarSlice (c i) t.val),
          (c i).symm (z.val, t.val) =
            (U.leaf (label i t)).inclusion ((parametrization i t z).val)) ∧
        (∀ i j, let Ω := overlapDomain (c i) (c j)
          let h := overlapScalar (c i) (c j)
          ∀ p ∈ Ω, ∃ (A B : Opens ℂ), p.1 ∈ A ∧
            (∀ z ∈ A, (z, p.2) ∈ Ω) ∧
            ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A B ∞,
              ∀ z : A, (e z : ℂ) = h (z.val, p.2))) ∧
      (∀ x : M,
        ∃ (qu : ιu) (qs : ιs),
        let := complexChart qu
        ∃ (Pu : Opens (Lu qu)) (Ps : Opens (Ls qs)),
          IsConnected (Pu : Set (Lu qu)) ∧ IsConnected (Ps : Set (Ls qs)) ∧
          ∃ (u₀ : Pu) (s₀ : Ps) (O : Opens M) (Ψ : (Pu × Ps) ≃ₜ O),
            (U.leaf qu).inclusion u₀.val = x ∧
            (S.leaf qs).inclusion s₀.val = x ∧
            (Ψ (u₀, s₀)).val = x ∧
            (∀ u : Pu, (Ψ (u, s₀)).val = (U.leaf qu).inclusion u.val) ∧
            (∀ t : Ps, (Ψ (u₀, t)).val = (S.leaf qs).inclusion t.val) ∧
              (∀ t : Ps, ∃ q : ιu,
                let := complexChart q
                ∃ (V : Opens (Lu q)) (b : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Pu V ∞),
                  ∀ u : Pu, (U.leaf q).inclusion (b u).val = (Ψ (u, t)).val) ∧
              (∀ u : Pu, ∃ q : ιs,
                ∃ (V : Opens (Ls q)) (b : Ps ≃ₜ V),
                  ∀ t : Ps, (S.leaf q).inclusion (b t).val = (Ψ (u, t)).val)) by
      obtain ⟨⟨T, c, label, branch, parametrization, hcover, htrans, hincl, hoverlap⟩,
        hlocal⟩ := hboxes
      refine ⟨?_, ?_⟩
      ·
        obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover
          (fun x : M ↦ (c x).source) (fun x ↦ (c x).open_source)
          (show (Set.univ : Set M) ⊆ ⋃ x : M, (c x).source from
            fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hcover x⟩)
        let e := (Fintype.equivFin J).symm
        let ix (i : Fin (Fintype.card J)) : M := (e i).val
        refine ⟨Fintype.card J, (fun i ↦ T (ix i)), (fun i ↦ c (ix i)),
          (fun i ↦ label (ix i)), (fun i ↦ branch (ix i)),
          (fun i ↦ parametrization (ix i)), ?_, ?_, ?_, ?_⟩
        · intro x
          obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp (hJ (Set.mem_univ x))
          refine ⟨e.symm ⟨j, hj⟩, ?_⟩
          simpa only [ix, e.apply_symm_apply] using hx
        · exact fun i ↦ htrans (ix i)
        · exact fun i ↦ hincl (ix i)
        · exact fun i j ↦ hoverlap (ix i) (ix j)
      · intro x
        obtain ⟨qu, qs, Pu, Ps, hPu, hPs, u₀, s₀, O, Ψ, hu₀, hs₀, hx,
          hhorizontal, hvertical, huleaves, hsleaves⟩ := hlocal x
        refine ⟨qu, qs, Pu, Ps, hPu, hPs, u₀, s₀, O, Ψ, hu₀, hs₀, hx,
          hhorizontal, hvertical, huleaves, hsleaves, ?_⟩
        intro hd
        have hdim : 2 * d - 2 = 0 := by omega
        have : DiscreteTopology (Ls qs) := by
          have : Subsingleton (Fin (2 * d - 2) → ℝ) := by rw [hdim]; infer_instance
          have : DiscreteTopology (Fin (2 * d - 2) → ℝ) := inferInstance
          exact ChartedSpace.discreteTopology (Fin (2 * d - 2) → ℝ) (Ls qs)
        have : ConnectedSpace (Ls qs) := (S.leaf qs).connected
        have : Subsingleton (Ls qs) := subsingleton_of_preconnected_totallyDisconnected
        let j : Pu ≃ₜ O := {
          toFun := fun u ↦ Ψ (u, s₀)
          invFun := fun w ↦ (Ψ.symm w).1
          left_inv := fun u ↦ congrArg Prod.fst (Ψ.symm_apply_apply (u, s₀))
          right_inv := fun w ↦ by
            have he : ((Ψ.symm w).1, s₀) = Ψ.symm w :=
              Prod.ext rfl (Subsingleton.elim _ _)
            change Ψ ((Ψ.symm w).1, s₀) = w
            rw [he, Ψ.apply_symm_apply]
          continuous_toFun := Ψ.continuous.comp (continuous_id.prodMk continuous_const)
          continuous_invFun := continuous_fst.comp Ψ.symm.continuous }
        exact ⟨fun t ↦ Subsingleton.elim _ _, j, hhorizontal,
          fun w ↦ Prod.ext rfl (Subsingleton.elim _ _)⟩
    constructor
    · choose T c hcover htrans hg using hNativeBox
      letI : ∀ i, ChartedSpace ℂ (Lu i) := complexChart
      choose label g hsource hhol hholInv hinc using hg
      have he (i : M) (t : T i) :
          ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (scalarSlice (c i) t.val)
            (⟨(g i t).target,(g i t).open_target⟩ : Opens (Lu (label i t))) ∞,
            ∀ z : scalarSlice (c i) t.val, (e z).val = g i t z.val :=
        scalarParameterDiffeomorph (g i t) (scalarSlice (c i) t.val)
          (hsource i t) (hhol i t) (hholInv i t)
      choose e heval using he
      refine ⟨T,c,label,(fun i t ↦ ⟨(g i t).target,(g i t).open_target⟩),e,
        hcover,htrans,?_,?_⟩
      · intro i t z
        rw [heval]
        exact (hinc i t z.val (by rw [hsource]; exact z.property)).symm
      · intro i j Ω h p hp
        let ti : T i := ⟨p.2,htrans i p hp.1⟩
        let tj : T j := ⟨((c j) ((c i).symm p)).2,
          htrans j _ ((c j).map_source hp.2)⟩
        exact scalarBoxOverlapOfPartition (fun i ↦ (U.leaf i).inclusion)
          (fun i ↦ (U.leaf i).injective) U.disjoint
          (c i) (c j) ti.val tj.val (label i ti) (label j tj) (g i ti) (g j tj)
          (hsource i ti) (hsource j tj) (hinc i ti) (hinc j tj)
          (hhol i ti) (hholInv i ti) (hhol j tj) (hholInv j tj)
          p.1 hp.1 hp.2 rfl
    · intro x
      let F := presentation.foliations
      obtain ⟨b,hb⟩ := F.cover x
      let zw := (F.box b).chart.symm ⟨x,hb⟩
      let z₀ := zw.1
      let w₀ := zw.2
      have hcenter : ((F.box b).chart (z₀,w₀)).val = x :=
        congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨x,hb⟩)
      obtain ⟨k,hk,hparams⟩ := native_scalar_box_parameter F pScalar pSmooth pHol b z₀ w₀
      obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp k.open_source (k.symm w₀) (k.map_target hk)
      let A : Opens ℂ := ⟨Metric.ball (k.symm w₀) r,Metric.isOpen_ball⟩
      have hA : (A : Set ℂ) ⊆ k.source := hball
      letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp (Metric.isConnected_ball hr)
      letI : ConnectedSpace (FoliationCoordinateDisk (2*d-2)) :=
        isConnected_iff_connectedSpace.mp (Metric.isConnected_ball (by norm_num : (0:ℝ)<1))
      let v₀ : A := ⟨k.symm w₀,Metric.mem_ball_self hr⟩
      let Q : A × FoliationCoordinateDisk (2*d-2) → M :=
        fun p ↦ ((F.box b).chart (p.2,k p.1.val)).val
      have hkA : IsOpenEmbedding (fun v : A ↦ k v.val) :=
        k.isOpenEmbedding_restrict.comp
          (Topology.IsOpenEmbedding.inclusion hA (A.isOpen.preimage continuous_subtype_val))
      have hQ : IsOpenEmbedding Q :=
        (F.box b).isOpen_image.isOpenEmbedding_subtypeVal.comp
          ((F.box b).chart.isOpenEmbedding.comp
            ((Homeomorph.prodComm (FoliationCoordinateDisk 2)
              (FoliationCoordinateDisk (2*d-2))).isOpenEmbedding.comp
                (hkA.prodMap (Homeomorph.refl _).isOpenEmbedding)))
      letI : ∀ i, ChartedSpace ℂ (Lu i) := complexChart
      have hu (z : FoliationCoordinateDisk (2*d-2)) :
          ∃ i : ιu, ∃ V : Opens (Lu i),
            ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A V ∞,
              ∀ v : A, (U.leaf i).inclusion (e v).val = Q (v,z) := by
        let y := ((F.box b).chart (z,w₀)).val
        let q := Quotient.mk F.unstablePartition y
        letI := pScalar q
        obtain ⟨g,hgsrc,hg,hgi,hgval⟩ := hparams z
        obtain ⟨i,e,he⟩ := hIdentUComplex q
        let gN := g.transHomeomorph e.toHomeomorph
        have hsrc : gN.source = k.source := by
          simpa only [gN, OpenPartialHomeomorph.transHomeomorph_source] using hgsrc
        have hgN : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ gN gN.source :=
          e.contMDiff.comp_contMDiffOn hg
        have hgiN : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ gN.symm gN.target :=
          hgi.comp e.symm.contMDiff.contMDiffOn (fun z hz ↦ hz)
        obtain ⟨V,c,hc⟩ := restrictedScalarParameter gN A (by rw [hsrc]; exact hA) hgN hgiN
        refine ⟨i,V,c,?_⟩
        intro v
        rw [hc]
        change (U.leaf i).inclusion (e (g v.val)) = _
        rw [he]
        exact hgval v.val (hA v.property)
      have hs (v : A) : ∃ i : ιs, ∃ V : Opens (Ls i),
          ∃ e : FoliationCoordinateDisk (2*d-2) ≃ₜ V,
            ∀ z, (S.leaf i).inclusion (e z).val = Q (v,z) := by
        let w := k v.val
        let q := F.stableLabel b w
        letI := F.stableTopology q
        letI := F.stableCharts q
        obtain ⟨i,e,he⟩ := hpresIdentS q
        let j : FoliationCoordinateDisk (2*d-2) → Ls i := fun z ↦
          e.symm ⟨((F.box b).chart (z,w)).val,F.stable_label b z w⟩
        have hj : IsOpenEmbedding j := e.symm.toHomeomorph.isOpenEmbedding.comp
          (F.stable_plaque b w)
        refine ⟨i,⟨Set.range j,hj.isOpen_range⟩,hj.isEmbedding.toHomeomorph,?_⟩
        intro z
        change (S.leaf i).inclusion (e.symm _) = _
        rw [← he, e.apply_symm_apply]
      have hQcenter : Q (v₀,z₀) = x := by
        change ((F.box b).chart (z₀,k (k.symm w₀))).val = x
        rw [k.right_inv hk]
        exact hcenter
      obtain ⟨qu,qs,Pu,Ps,hPu,hPs,u₀,s₀,O,Ψ,hu₀,hs₀,hΨ,hh,hv,hup,hsp⟩ :=
        localProductFromParameters (fun i ↦ (U.leaf i).inclusion)
          (fun i ↦ (S.leaf i).inclusion) A Q hQ v₀ z₀ hu hs
      exact ⟨qu,qs,Pu,Ps,hPu,hPs,u₀,s₀,O,Ψ,
        hu₀.trans hQcenter,hs₀.trans hQcenter,hΨ.trans hQcenter,hh,hv,hup,hsp⟩

end HolomorphicAnosov.Ghys
