import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Paper.Zhang.CompleteStableCoordinates
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import HolomorphicAnosov.Paper.Zhang.UniformLocalStableCoordinates
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.NativeComplexStableLeafDatum
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.MeanValue

/-! Local unstable holonomy is linear in normalized complete stable coordinates. (Zhang, Lemma 2.8,
pp.9–10, equation (19)) -/

open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff

attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
universe u v

namespace HolomorphicAnosov

namespace HolonomyTransverseConstancy

/-- The real manifold derivative of a holomorphic scalar function is the scalar restriction of its
complex derivative. -/
theorem scalar_real_derivative {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] (t : X → ℂ) (z : X)
    (ht : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) t z) :
    MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) t z ∧
      mfderiv (realModel d) 𝓘(ℝ, ℂ) t z =
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z).restrictScalars ℝ := by
  obtain ⟨hc, hd⟩ := ht.hasMFDerivAt
  have hr := hd.restrictScalars ℝ
  have h : HasMFDerivAt (realModel d) 𝓘(ℝ, ℂ) t z
      ((mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z).restrictScalars ℝ) := by
    refine ⟨hc, ?_⟩
    exact hr
  exact ⟨h.mdifferentiableAt, h.mfderiv⟩

/-- A differentiable scalar function with zero real manifold differential on an open set is locally
constant there. (Zhang, Lemma 2.8) -/
theorem zero_mfderiv_locally_constant {r : ℕ} {L : Type*} [TopologicalSpace L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (g : L → ℂ) (W : Set L) (hW : IsOpen W)
    (hg : MDifferentiableOn 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, ℂ) g W)
    (hzero : ∀ z ∈ W, mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, ℂ) g z = 0) :
    IsLocallyConstant (fun z : W ↦ g z.val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  let c := chartAt (Fin r → ℝ) z.val
  let T := c.target ∩ c.symm ⁻¹' W
  have hT : IsOpen T := c.symm.continuousOn.isOpen_inter_preimage c.open_target hW
  have hzT : c z.val ∈ T := ⟨c.map_source (mem_chart_source (Fin r → ℝ) z.val),
    by simpa only [mem_preimage, c.left_inv (mem_chart_source (Fin r → ℝ) z.val)] using z.property⟩
  have hdiff : DifferentiableOn ℝ (g ∘ c.symm) T := by
    intro y hy
    have hgi := hg.mdifferentiableAt (hW.mem_nhds hy.2)
    have hct : MDifferentiableOn 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) c.symm c.target := by
      simpa [c, extChartAt] using (mdifferentiableOn_extChartAt_symm
        (I := 𝓘(ℝ, Fin r → ℝ)) (x := z.val))
    have hci := hct.mdifferentiableAt (c.open_target.mem_nhds hy.1)
    exact (hgi.comp y hci).differentiableAt.differentiableWithinAt
  have hd0 : T.EqOn (fderiv ℝ (g ∘ c.symm)) 0 := by
    intro y hy
    have hgi := hg.mdifferentiableAt (hW.mem_nhds hy.2)
    have hct : MDifferentiableOn 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) c.symm c.target := by
      simpa [c, extChartAt] using (mdifferentiableOn_extChartAt_symm
        (I := 𝓘(ℝ, Fin r → ℝ)) (x := z.val))
    have hci := hct.mdifferentiableAt (c.open_target.mem_nhds hy.1)
    rw [← mfderiv_eq_fderiv, mfderiv_comp y hgi hci, hzero _ hy.2]
    rfl
  have hopen := hT.isOpen_inter_preimage_of_fderiv_eq_zero hdiff hd0
    {g (c.symm (c z.val))}
  have hmem : c z.val ∈ T ∩ (g ∘ c.symm) ⁻¹' {g (c.symm (c z.val))} :=
    ⟨hzT, rfl⟩
  have hc : ContinuousAt (fun q : W ↦ c q.val) z :=
    (continuousAt_extChartAt (I := 𝓘(ℝ, Fin r → ℝ)) z.val).comp
      continuous_subtype_val.continuousAt
  filter_upwards [hc.eventually (hopen.mem_nhds hmem),
    continuous_subtype_val.continuousAt.eventually
      (c.open_source.mem_nhds (mem_chart_source (Fin r → ℝ) z.val))] with q hq hqs
  simpa only [mem_inter_iff, mem_preimage, mem_singleton_iff, Function.comp_apply,
    c.left_inv hqs, c.left_inv (mem_chart_source (Fin r → ℝ) z.val)] using hq.2

/-- A holomorphic transverse function annihilating the unstable distribution is locally constant
along each native unstable leaf in its domain. -/
theorem native_inclusion_transverse_locally_constant
    {d s r : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] [IsManifold (realModel d) ∞ X] [T2Space X] [SecondCountableTopology X]
    (f : X ≃ₜ X) (U : ContinuousComplexTangentSubbundle (complexModel d) X)
    (P : RealTangentDistribution (realModel d) X)
    (A : NativeTransverseAsymptoticIdentification f (complexStableRealDistribution U) P s r)
    (V : TopologicalSpace.Opens X) (t : X → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (hker : ∀ z ∈ V,
      (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t z)).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z)).ker = U.toDistribution z)
    (x : X) :
    letI := A.stableTopology x
    IsLocallyConstant (fun z : (Subtype.val : StableAsymptoticLeaf f x → X) ⁻¹' (V : Set X) ↦
      t z.val.val) := by
  let := A.stableTopology x
  let := A.stableCharts x
  let := (A.nativeS x).smoothAtlas
  let inc := (Subtype.val : StableAsymptoticLeaf f x → X)
  have hi := (A.nativeS x).inclusion_smooth
  have hW : IsOpen (inc ⁻¹' (V : Set X)) := V.isOpen.preimage hi.continuous
  have hmd : MDifferentiableOn 𝓘(ℝ, Fin (A.nativeS x).rank → ℝ) 𝓘(ℝ, ℂ)
      (t ∘ inc) (inc ⁻¹' (V : Set X)) := by
    intro z hz
    have htc := ht.mdifferentiableOn (by simp)
      |>.mdifferentiableAt (V.isOpen.mem_nhds hz)
    exact ((scalar_real_derivative t (inc z) htc).1.comp z
      (hi.mdifferentiable (by simp) z)).mdifferentiableWithinAt
  apply zero_mfderiv_locally_constant (t ∘ inc) _ hW hmd
  intro z hz
  have htc := ht.mdifferentiableOn (by simp)
    |>.mdifferentiableAt (V.isOpen.mem_nhds hz)
  obtain ⟨htr, hdr⟩ := scalar_real_derivative t (inc z) htc
  rw [mfderiv_comp z htr (hi.mdifferentiable (by simp) z), hdr]
  ext v
  have hv : mfderiv 𝓘(ℝ, Fin (A.nativeS x).rank → ℝ) (realModel d) inc z v ∈
      complexStableRealDistribution U (inc z) := by
    rw [← (A.nativeS x).tangent_image z]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  obtain ⟨w, hw, he⟩ := Submodule.mem_map.mp hv
  have ht0 : mfderiv (complexModel d) 𝓘(ℂ, ℂ) t (inc z) w = 0 := by
    have hk : w ∈ (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t (inc z))).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t (inc z))).ker := by
      rw [hker _ hz]
      exact hw
    exact hk
  change mfderiv (complexModel d) 𝓘(ℂ, ℂ) t (inc z)
    (mfderiv 𝓘(ℝ, Fin (A.nativeS x).rank → ℝ) (realModel d) inc z v) = 0
  rw [← he]
  exact ht0

/-- A holomorphic transverse function annihilating the unstable distribution is locally constant on
each intrinsic unstable partition class in its domain. -/
theorem partition_transverse_locally_constant
    {d s r : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] [IsManifold (realModel d) ∞ X]
    [T2Space X] [SecondCountableTopology X]
    (f : X ≃ₜ X) (U : ContinuousComplexTangentSubbundle (complexModel d) X)
    (P : RealTangentDistribution (realModel d) X)
    (A : NativeTransverseAsymptoticIdentification f (complexStableRealDistribution U) P s r)
    (V : TopologicalSpace.Opens X) (t : X → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (hker : ∀ z ∈ V,
      (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t z)).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z)).ker = U.toDistribution z) :
    letI := A.realAmbientCharts
    ∀ q : Quotient A.F.stablePartition,
    letI := A.F.stableTopology q
    IsLocallyConstant (fun z :
      (Subtype.val : IntrinsicFoliationLeaf A.F.stablePartition q → X) ⁻¹' (V : Set X) ↦
      t z.val.val) := by
  let := A.realAmbientCharts
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    let := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
    let := A.stableTopology x
    let E := A.stableClassHomeomorph x
    have he : ∀ z, (E z).val = z.val := A.stable_points x
    let T : ((Subtype.val : IntrinsicFoliationLeaf A.F.stablePartition
        (Quotient.mk A.F.stablePartition x) → X) ⁻¹' (V : Set X)) →
        ((Subtype.val : StableAsymptoticLeaf f x → X) ⁻¹' (V : Set X)) :=
      fun z ↦ ⟨E z.val, by simpa only [mem_preimage, he] using z.property⟩
    have hT : Continuous T :=
      (E.continuous.comp continuous_subtype_val).subtype_mk _
    have hlc := (native_inclusion_transverse_locally_constant f U P A V t ht hker x).comp_continuous hT
    simpa only [Function.comp_def, T, he] using hlc

/-- The scalar transverse coordinate is constant on each connected plaque strip contained in its
domain. -/
theorem connected_strip_transverse_eq
    {d s r : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] [IsManifold (realModel d) ∞ X]
    [T2Space X] [SecondCountableTopology X]
    (f : X ≃ₜ X) (U : ContinuousComplexTangentSubbundle (complexModel d) X)
    (P : RealTangentDistribution (realModel d) X)
    (A : NativeTransverseAsymptoticIdentification f (complexStableRealDistribution U) P s r)
    (V : TopologicalSpace.Opens X) (t : X → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (hker : ∀ z ∈ V,
      (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t z)).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z)).ker = U.toDistribution z) :
    letI := A.realAmbientCharts
    ∀ (i : A.F.boxIndex) (w : FoliationCoordinateDisk r)
      (K : Set (FoliationCoordinateDisk s)),
      IsPreconnected K → (∀ z ∈ K, ((A.F.box i).chart (z, w)).val ∈ V) →
      ∀ a ∈ K, ∀ b ∈ K,
        t ((A.F.box i).chart (a, w)).val = t ((A.F.box i).chart (b, w)).val := by
  let := A.realAmbientCharts
  intro i w K hK hV a ha b hb
  let q := A.F.stableLabel i w
  let := A.F.stableTopology q
  let plaque : FoliationCoordinateDisk s → IntrinsicFoliationLeaf A.F.stablePartition q :=
    fun z ↦ ⟨((A.F.box i).chart (z, w)).val, A.F.stable_label i z w⟩
  have hc : Continuous plaque := (A.F.stable_plaque i w).continuous
  let T : K → (Subtype.val : IntrinsicFoliationLeaf A.F.stablePartition q → X)
      ⁻¹' (V : Set X) := fun z ↦ ⟨plaque z.val, hV z.val z.property⟩
  have hT : Continuous T := (hc.comp continuous_subtype_val).subtype_mk _
  have hlc := (partition_transverse_locally_constant f U P A V t ht hker q).comp_continuous hT
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  exact hlc.apply_eq_of_preconnectedSpace ⟨a, ha⟩ ⟨b, hb⟩

/-- A local plaque transport preserves the scalar coordinate near its source basepoint when the
coordinate agrees on the source and target plaques. -/
theorem plaque_transport_scalar_germ
    {s r : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [ChartedSpace (Fin (s + r) → ℝ) X]
    (F : TransverseContinuousFoliations s r X) (x y : X)
    (e : LocalPlaqueTransport F x y) (t : X → ℂ)
    (O : Set (FoliationCoordinateDisk r)) (hO : IsOpen O)
    (heO : e.transverse ∈ O)
    (ht : ∀ w ∈ O, t ((F.box e.box).chart (e.second, w)).val =
      t ((F.box e.box).chart (e.first, w)).val) :
    t y = t x ∧ ∀ᶠ p in 𝓝 (F.uPoint x),
      p ∈ e.map.source ∧ t (e.map p).val = t p.val := by
  have hxy : t y = t x := by
    simpa only [e.first_point, e.second_point] using ht e.transverse heO
  refine ⟨hxy, ?_⟩
  let B : Set X := Subtype.val '' ((F.box e.box).chart ''
    ((Set.univ : Set (FoliationCoordinateDisk s)) ×ˢ O))
  have hB : IsOpen B := (F.box e.box).isOpen_image.isOpenMap_subtype_val _
    ((F.box e.box).chart.isOpenMap _ (isOpen_univ.prod hO))
  have hxB : x ∈ B := ⟨(F.box e.box).chart (e.first, e.transverse),
    ⟨(e.first, e.transverse), ⟨mem_univ _, heO⟩, rfl⟩, e.first_point⟩
  have hincl := F.unstable_inclusion (Quotient.mk F.unstablePartition x)
  have hnear := hincl.continuousAt (x := F.uPoint x).eventually (hB.mem_nhds hxB)
  filter_upwards [e.map.open_source.mem_nhds e.source_point, hnear] with p hp hpB
  refine ⟨hp, ?_⟩
  obtain ⟨w, hw⟩ := e.source_in_plaque p hp
  obtain ⟨q, ⟨⟨a, b⟩, hab, hq⟩, hqp⟩ := hpB
  have heq : (F.box e.box).chart (a, b) = (F.box e.box).chart (e.first, w) := by
    apply Subtype.ext
    rw [hq, hqp, hw]
  have hb : b = w := congrArg Prod.snd ((F.box e.box).chart.injective heq)
  have hwO : w ∈ O := hb ▸ hab.2
  rw [e.coordinate_map p w hp hw, ← hw]
  exact ht w hwO

/-- A local native plaque transport preserves a holomorphic transverse function near its basepoint,
with both points lying in its domain. (Zhang, Lemma 2.8) -/
theorem native_transport_transverse_constancy
    {d s r : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X] [IsManifold (realModel d) ∞ X]
    [T2Space X] [SecondCountableTopology X]
    (f : X ≃ₜ X) (U : ContinuousComplexTangentSubbundle (complexModel d) X)
    (P : RealTangentDistribution (realModel d) X)
    (A : NativeTransverseAsymptoticIdentification f (complexStableRealDistribution U) P s r)
    (V : TopologicalSpace.Opens X) (t : X → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (hker : ∀ z ∈ V,
      (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t z)).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z)).ker = U.toDistribution z)
    (x y : X) :
    letI := A.realAmbientCharts
    ∀ (e : LocalPlaqueTransport A.F x y)
      (K : Set (FoliationCoordinateDisk s)) (O : Set (FoliationCoordinateDisk r)),
      IsConnected K → e.first ∈ K → e.second ∈ K → IsOpen O → e.transverse ∈ O →
      (∀ z ∈ K, ∀ w ∈ O, ((A.F.box e.box).chart (z, w)).val ∈ V) →
    letI := A.unstableTopology x
    letI := A.unstableTopology y
    let px := A.unstableClassHomeomorph x (A.F.uPoint x)
    let h := A.transportUnstableLocalMap x y e.map
    t y = t x ∧ ∀ᶠ p in 𝓝 px,
      p ∈ h.source ∧ h p ∈ h.target ∧ t (h p).val = t p.val := by
  let := A.realAmbientCharts
  intro e K O hK hfirst hsecond hO heO hstrip
  let := A.unstableTopology x
  let := A.unstableTopology y
  let Ex := A.unstableClassHomeomorph x
  let Ey := A.unstableClassHomeomorph y
  let px := Ex (A.F.uPoint x)
  let h := A.transportUnstableLocalMap x y e.map
  have hstripEq : ∀ w ∈ O, t ((A.F.box e.box).chart (e.second, w)).val =
      t ((A.F.box e.box).chart (e.first, w)).val := by
    intro w hw
    exact connected_strip_transverse_eq f U P A V t ht hker e.box w K
      hK.isPreconnected (fun z hz ↦ hstrip z hz w hw) e.second hsecond e.first hfirst
  obtain ⟨hxy, hnear⟩ := plaque_transport_scalar_germ A.F x y e t O hO heO hstripEq
  refine ⟨hxy, ?_⟩
  have hnear' : ∀ᶠ p in 𝓝 px, Ex.symm p ∈ e.map.source ∧
      t (e.map (Ex.symm p)).val = t (Ex.symm p).val := by
    have hc : Tendsto Ex.symm (𝓝 px) (𝓝 (A.F.uPoint x)) := by
      simpa only [ContinuousAt, px, Ex.symm_apply_apply] using Ex.symm.continuous.continuousAt (x := px)
    exact hc.eventually hnear
  filter_upwards [hnear'] with p hp
  have hps : p ∈ h.source := by
    simpa [h, NativeTransverseAsymptoticIdentification.transportUnstableLocalMap,
      Ex, OpenPartialHomeomorph.trans_source] using hp.1
  refine ⟨hps, h.map_source hps, ?_⟩
  have hex : ∀ z, (Ex z).val = z.val := A.unstable_points x
  have hey : ∀ z, (Ey z).val = z.val := A.unstable_points y
  have hinv : (Ex.symm p).val = p.val := by
    simpa only [Ex.apply_symm_apply] using (hex (Ex.symm p)).symm
  change t (Ey (e.map (Ex.symm p))).val = t p.val
  rw [hey, hp.2, hinv]

end HolonomyTransverseConstancy

namespace LinearHolonomyPreparation

/-- A complex-linear functional with kernel `U` restricts to an isomorphism on a rank-one complement
of `U`. (Zhang, Lemma 2.4, p.7) -/
theorem restricted_differential_invertible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (S U : Submodule ℂ E) (B : E →L[ℂ] ℂ)
    (hS : Module.finrank ℂ S = 1) (hc : IsCompl S U) (hk : B.ker = U) :
    (B.comp S.subtypeL).IsInvertible := by
  have hi : Function.Injective (B.comp S.subtypeL) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro v hv
      have hu : (v : E) ∈ U := by
        rw [← hk]
        exact hv
      have hz : (v : E) = 0 := Submodule.disjoint_def.mp hc.disjoint (v : E) v.property hu
      simpa only [Submodule.mem_bot, Subtype.ext_iff, ZeroMemClass.coe_zero] using hz
    · exact bot_le
  let e := ((B.comp S.subtypeL).toLinearMap.linearEquivOfInjective hi
    (by simpa using hS)).toContinuousLinearEquiv
  exact ⟨e, by ext v; rfl⟩

/-- Normalized coordinate germs conjugate a continuous pointed map preserving transverse functions
to `Bx.trans By.symm`. (Zhang, Lemma 2.8, pp.9–10, equation (19)) -/
theorem normalized_germ_conjugacy
    {P Q E F : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (px : P) (py : Q) (h : P → Q) (hc : ContinuousAt h px) (hp : h px = py)
    (tx : P → ℂ) (ty : Q → ℂ) (c : ℂ)
    (Bx : E ≃L[ℂ] ℂ) (By : F ≃L[ℂ] ℂ)
    (phix : P → E) (phiy : Q → F)
    (hx : ∀ᶠ p in 𝓝 px, phix p = Bx.symm (tx p - c))
    (hy : ∀ᶠ p in 𝓝 py, phiy p = By.symm (ty p - c))
    (ht : ∀ᶠ p in 𝓝 px, ty (h p) = tx p) :
    ∀ᶠ p in 𝓝 px, phiy (h p) = (Bx.trans By.symm) (phix p) := by
  have hy' : ∀ᶠ p in 𝓝 px, phiy (h p) = By.symm (ty (h p) - c) := by
    exact (hp ▸ hc.tendsto).eventually hy
  filter_upwards [hx, hy', ht] with p hxp hyp htp
  rw [hyp, htp, hxp]
  simp

/-- The linear map in a coordinate conjugacy germ equals the derivative of the conjugated map
expressed through the coordinate derivative normalizations. (Zhang, Lemma 2.8, equation (19)) -/
theorem derivative_of_conjugacy_germ
    {HP HQ E F : Type*} [TopologicalSpace HP] [TopologicalSpace HQ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace HP P] [ChartedSpace HQ Q]
    {EP EQ : Type*} [NormedAddCommGroup EP] [NormedSpace ℂ EP]
    [NormedAddCommGroup EQ] [NormedSpace ℂ EQ]
    (IP : ModelWithCorners ℂ EP HP) (IQ : ModelWithCorners ℂ EQ HQ)
    [IsManifold IP ∞ P] [IsManifold IQ ∞ Q]
    (px : P) (py : Q) (h : P → Q) (hp : h px = py)
    (hh : MDifferentiableAt IP IQ h px)
    (phix : Diffeomorph IP 𝓘(ℂ, E) P E ∞)
    (phiy : Diffeomorph IQ 𝓘(ℂ, F) Q F ∞)
    (Jx : TangentSpace IP px ≃L[ℂ] E)
    (Jy : TangentSpace IQ py ≃L[ℂ] F)
    (hx : (tangentSpaceCastModel 𝓘(ℂ, E) (phix px)).toContinuousLinearMap.comp
      (mfderiv IP 𝓘(ℂ, E) phix px) = Jx.toContinuousLinearMap)
    (hy : (tangentSpaceCastModel 𝓘(ℂ, F) (phiy py)).toContinuousLinearMap.comp
      (mfderiv IQ 𝓘(ℂ, F) phiy py) = Jy.toContinuousLinearMap)
    (D : E ≃L[ℂ] F)
    (hg : ∀ᶠ p in 𝓝 px, phiy (h p) = D (phix p)) :
    D.toContinuousLinearMap = Jy.toContinuousLinearMap.comp
      ((mfderiv IP IQ h px).comp Jx.symm.toContinuousLinearMap) := by
  have hx' : mfderiv IP 𝓘(ℂ, E) phix px = Jx.toContinuousLinearMap := by
    ext v
    exact congrArg (fun L ↦ L v) hx
  have hy' : mfderiv IQ 𝓘(ℂ, F) phiy py = Jy.toContinuousLinearMap := by
    ext v
    exact congrArg (fun L ↦ L v) hy
  have hg' : (fun p ↦ phiy (h p)) =ᶠ[𝓝 px] (fun p ↦ D (phix p)) := hg
  have heq := hg'.mfderiv_eq (I := IP) (I' := 𝓘(ℂ, F))
  have hD : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) D (phix px) :=
    D.toContinuousLinearMap.differentiableAt.mdifferentiableAt
  have hycomp := mfderiv_comp px ((phiy.mdifferentiable (by simp)) (h px)) hh
  have hxcomp := mfderiv_comp px hD ((phix.mdifferentiable (by simp)) px)
  dsimp only [Function.comp_def] at hycomp hxcomp
  rw [hycomp, hxcomp] at heq
  have hd : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) D (phix px) = D.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact D.toContinuousLinearMap.fderiv
  rw [hp, hy', hx', hd] at heq
  have heq' : Jy.toContinuousLinearMap.comp (mfderiv IP IQ h px) =
      D.toContinuousLinearMap.comp Jx.toContinuousLinearMap := by
    ext v
    exact congrArg (fun L ↦ L v) heq
  ext v
  have hv := congrArg (fun L ↦ L (Jx.symm v)) heq'
  change D v = Jy (mfderiv IP IQ h px (Jx.symm v))
  change Jy (mfderiv IP IQ h px (Jx.symm v)) = D (Jx (Jx.symm v)) at hv
  rw [Jx.apply_symm_apply] at hv
  exact hv.symm

/-- A map locally conjugate to a complex-linear equivalence through smooth coordinates is complex
differentiable at the basepoint. (Zhang, Lemma 2.8, p.10) -/
theorem differentiable_of_conjugacy_germ
    {HP HQ E F : Type*} [TopologicalSpace HP] [TopologicalSpace HQ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace HP P] [ChartedSpace HQ Q]
    {EP EQ : Type*} [NormedAddCommGroup EP] [NormedSpace ℂ EP]
    [NormedAddCommGroup EQ] [NormedSpace ℂ EQ]
    (IP : ModelWithCorners ℂ EP HP) (IQ : ModelWithCorners ℂ EQ HQ)
    [IsManifold IP ∞ P] [IsManifold IQ ∞ Q]
    (px : P) (h : P → Q)
    (phix : Diffeomorph IP 𝓘(ℂ, E) P E ∞)
    (phiy : Diffeomorph IQ 𝓘(ℂ, F) Q F ∞) (D : E ≃L[ℂ] F)
    (hg : ∀ᶠ p in 𝓝 px, phiy (h p) = D (phix p)) :
    MDifferentiableAt IP IQ h px := by
  have he : h =ᶠ[𝓝 px] (fun p ↦ phiy.symm (D (phix p))) := by
    filter_upwards [hg] with p hp
    rw [← hp, phiy.symm_apply_apply]
  have hD : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) D (phix px) :=
    D.toContinuousLinearMap.differentiableAt.mdifferentiableAt
  exact (((phiy.symm.mdifferentiable (by simp)) _).comp px
    (hD.comp px ((phix.mdifferentiable (by simp)) px))).congr_of_eventuallyEq he

/-- A coordinate conjugacy germ for a local holonomy map gives an open neighborhood of zero on which
the coordinate conjugacy holds and the inverse coordinate lies in the holonomy source. (Zhang,
equation (19)) -/
theorem coordinate_neighborhood_of_germ
    {P Q E F : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (px : P) (h : OpenPartialHomeomorph P Q)
    (phix : P ≃ₜ E) (phiy : Q → F) (D : E ≃L[ℂ] F)
    (hx : phix px = 0) (hs : px ∈ h.source)
    (hg : ∀ᶠ p in 𝓝 px, phiy (h p) = D (phix p)) :
    ∃ N : Set E, IsOpen N ∧ 0 ∈ N ∧
      ∀ v ∈ N, phix.symm v ∈ h.source ∧ phiy (h (phix.symm v)) = D v := by
  have hp : phix.symm 0 = px := by rw [← hx, phix.symm_apply_apply]
  have ht : Tendsto phix.symm (𝓝 0) (𝓝 px) := hp ▸ phix.symm.continuous.tendsto 0
  have hn : ∀ᶠ v in 𝓝 (0 : E), phix.symm v ∈ h.source ∧
      phiy (h (phix.symm v)) = D v := by
    filter_upwards [ht.eventually (h.open_source.mem_nhds hs), ht.eventually hg] with v hv he
    exact ⟨hv, by simpa only [phix.apply_symm_apply] using he⟩
  obtain ⟨N, hN, ho, hz⟩ := mem_nhds_iff.mp hn
  exact ⟨N, ho, hz, fun v hv ↦ hN hv⟩

end LinearHolonomyPreparation

/-- Local unstable holonomy is complex differentiable and is conjugate near the basepoint to its
derivative by the normalized complete stable coordinates. (Zhang, Lemma 2.8, pp.9–10, equation
(19); equation (14), p.7; Lemma 2.7, p.9) -/
theorem linearUnstableHolonomy
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X] (_hd : 3 ≤ d)
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (S U : ContinuousComplexTangentSubbundle (complexModel d) X)
    (hS : ∀ z, Module.finrank ℂ (S.toDistribution z) = 1)
    (hsplit : ∀ z, IsCompl (S.toDistribution z) (U.toDistribution z)) :
    letI : MetrizableSpace X := Manifold.metrizableSpace (realModel d) X
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    ∀ (_hSr : complexStableRealDistribution S = a.splitting.stable.toDistribution)
    (_hUr : complexStableRealDistribution U = a.splitting.unstable.toDistribution)
    (A : NativeTransverseAsymptoticIdentification.{u, v}
      f.toHomeomorph.symm (complexStableRealDistribution U)
      (complexStableRealDistribution S) (2 * (d - 1)) 2)
    (nabla : QuotientLineConnection.Connection U.toDistribution)
    (V : TopologicalSpace.Opens X)
    (sigma : (z : X) → QuotientLineConnection.Fibre U.toDistribution z)
    (t : X → ℂ)
    (_hsigma : QuotientLineConnection.IsHolomorphicSection U.toDistribution V sigma)
    (_hsigma0 : ∀ z ∈ V, sigma z ≠ 0)
    (_hparallel : QuotientLineConnection.IsParallelOn nabla V sigma)
    (_ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (_hpi : ∀ z ∈ V, ∀ w : TangentSpace (complexModel d) z,
      QuotientLineConnection.projection U.toDistribution z w =
        ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t z)).toContinuousLinearMap
          (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z w)) • sigma z)
    (_hker : ∀ z ∈ V,
      (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t z)).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t z)).ker = U.toDistribution z)
    (x y : X),
    letI : ∀ z : X, NormedAddCommGroup (TangentSpace (complexModel d) z) :=
      fun _ ↦ inferInstanceAs (NormedAddCommGroup (ComplexModel d))
    letI : ∀ z : X, NormedSpace ℂ (TangentSpace (complexModel d) z) :=
      fun _ ↦ inferInstanceAs (NormedSpace ℂ (ComplexModel d))
    letI := A.realAmbientCharts
    ∀ e : LocalPlaqueTransport A.F x y,
    ∀ (K : Set (FoliationCoordinateDisk (2 * (d - 1))))
      (O : Set (FoliationCoordinateDisk 2)),
      IsConnected K → e.first ∈ K → e.second ∈ K → IsOpen O → e.transverse ∈ O →
      (∀ z ∈ K, ∀ w ∈ O, ((A.F.box e.box).chart (z, w)).val ∈ V) →
    letI := A.unstableTopology x
    letI := A.unstableTopology y
    letI := A.unstableCharts x
    letI := A.unstableCharts y
    letI := (A.complexU1 x).charts
    letI := (A.complexU1 y).charts
    let px := A.unstableClassHomeomorph x (A.F.uPoint x)
    let py := A.unstableClassHomeomorph y (A.F.uPoint y)
    let h := A.transportUnstableLocalMap x y e.map
    ∀ (Jx : TangentSpace (complexModel 1) px ≃L[ℂ] S.toDistribution x)
      (Jy : TangentSpace (complexModel 1) py ≃L[ℂ] S.toDistribution y),
      (S.toDistribution x).subtypeL.comp Jx.toContinuousLinearMap =
        mfderiv (complexModel 1) (complexModel d)
          (Subtype.val : UnstableAsymptoticLeaf f.toHomeomorph.symm x → X) px →
      (S.toDistribution y).subtypeL.comp Jy.toContinuousLinearMap =
        mfderiv (complexModel 1) (complexModel d)
          (Subtype.val : UnstableAsymptoticLeaf f.toHomeomorph.symm y → X) py →
    ∀ (phix : Diffeomorph (complexModel 1) 𝓘(ℂ, S.toDistribution x)
        (UnstableAsymptoticLeaf f.toHomeomorph.symm x) (S.toDistribution x) ∞)
      (phiy : Diffeomorph (complexModel 1) 𝓘(ℂ, S.toDistribution y)
        (UnstableAsymptoticLeaf f.toHomeomorph.symm y) (S.toDistribution y) ∞),
      phix px = 0 → phiy py = 0 →
      (tangentSpaceCastModel 𝓘(ℂ, S.toDistribution x) (phix px)).toContinuousLinearMap.comp
        (mfderiv (complexModel 1) 𝓘(ℂ, S.toDistribution x) phix px) =
          Jx.toContinuousLinearMap →
      (tangentSpaceCastModel 𝓘(ℂ, S.toDistribution y) (phiy py)).toContinuousLinearMap.comp
        (mfderiv (complexModel 1) 𝓘(ℂ, S.toDistribution y) phiy py) =
          Jy.toContinuousLinearMap →
      (∀ᶠ p in 𝓝 px, phix p = normalizedLocalStableCoordinate S.toDistribution t x p.val) →
      (∀ᶠ p in 𝓝 py, phiy p = normalizedLocalStableCoordinate S.toDistribution t y p.val) →
    ∃ D : S.toDistribution x ≃L[ℂ] S.toDistribution y,
      D.toContinuousLinearMap = Jy.toContinuousLinearMap.comp
        ((mfderiv (complexModel 1) (complexModel 1) h px).comp
          Jx.symm.toContinuousLinearMap) ∧
      ∃ N : Set (S.toDistribution x), IsOpen N ∧ 0 ∈ N ∧
        ∀ v ∈ N, phix.symm v ∈ h.source ∧ phiy (h (phix.symm v)) = D v := by
  let : MetrizableSpace X := Manifold.metrizableSpace (realModel d) X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  intro hSr hUr A nabla V sigma t hsigma hsigma0 hparallel ht hpi hker x y
  let : ∀ z : X, NormedAddCommGroup (TangentSpace (complexModel d) z) :=
    fun _ ↦ inferInstanceAs (NormedAddCommGroup (ComplexModel d))
  let : ∀ z : X, NormedSpace ℂ (TangentSpace (complexModel d) z) :=
    fun _ ↦ inferInstanceAs (NormedSpace ℂ (ComplexModel d))
  let := A.realAmbientCharts
  intro e K O hK hxK hyK hO hwO hstrip
  let := A.unstableTopology x
  let := A.unstableTopology y
  let := A.unstableCharts x
  let := A.unstableCharts y
  let := (A.complexU1 x).charts
  let := (A.complexU1 y).charts
  let := (A.complexU1 x).complex_manifold
  let := (A.complexU1 y).complex_manifold
  dsimp only
  let gx : NormedAddCommGroup (S.toDistribution x) := inferInstance
  let sx : NormedSpace ℂ (S.toDistribution x) := inferInstance
  let gy : NormedAddCommGroup (S.toDistribution y) := inferInstance
  let sy : NormedSpace ℂ (S.toDistribution y) := inferInstance
  let px := A.unstableClassHomeomorph x (A.F.uPoint x)
  let py := A.unstableClassHomeomorph y (A.F.uPoint y)
  let h := A.transportUnstableLocalMap x y e.map
  intro Jx Jy hJx hJy phix phiy hpx hpy hDx hDy hgx hgy
  have hsource : px ∈ h.source := by
    simpa [h, px, NativeTransverseAsymptoticIdentification.transportUnstableLocalMap,
      OpenPartialHomeomorph.trans_source] using e.source_point
  have hpoint : h px = py := by
    simp [h, px, py, NativeTransverseAsymptoticIdentification.transportUnstableLocalMap,
      OpenPartialHomeomorph.trans_apply, e.map_point]
  have hcontinuous : ContinuousAt h px := h.continuousAt hsource
  have hxV : x ∈ V := by simpa only [e.first_point] using hstrip e.first hxK e.transverse hwO
  have hyV : y ∈ V := by simpa only [e.second_point] using hstrip e.second hyK e.transverse hwO
  have hinvx : (localStableCoordinateDerivative S.toDistribution t x).IsInvertible :=
    LinearHolonomyPreparation.restricted_differential_invertible
      (S.toDistribution x) (U.toDistribution x)
      (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t x)).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t x))
      (hS x) (hsplit x) (hker x hxV)
  have hinvy : (localStableCoordinateDerivative S.toDistribution t y).IsInvertible :=
    LinearHolonomyPreparation.restricted_differential_invertible
      (S.toDistribution y) (U.toDistribution y)
      (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t y)).toContinuousLinearMap).comp
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t y))
      (hS y) (hsplit y) (hker y hyV)
  obtain ⟨Bx, hBx⟩ := hinvx
  obtain ⟨By, hBy⟩ := hinvy
  have hconst : t y = t x ∧
      ∀ᶠ p in 𝓝 px, t (h p).val = t p.val := by
    obtain ⟨hxy, hn⟩ := HolonomyTransverseConstancy.native_transport_transverse_constancy
      f.toHomeomorph.symm U (complexStableRealDistribution S) A V t ht hker
      x y e K O hK hxK hyK hO hwO hstrip
    exact ⟨hxy, hn.mono fun _ hp ↦ hp.2.2⟩
  have hxg : ∀ᶠ p in 𝓝 px, phix p = Bx.symm (t p.val - t x) := by
    filter_upwards [hgx] with p hp
    simpa only [normalizedLocalStableCoordinate, ← hBx,
      ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe] using hp
  have hyg : ∀ᶠ p in 𝓝 py, phiy p = By.symm (t p.val - t x) := by
    filter_upwards [hgy] with p hp
    simpa only [normalizedLocalStableCoordinate, ← hBy, hconst.1,
      ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe] using hp
  let D := Bx.trans By.symm
  have hconj : ∀ᶠ p in 𝓝 px, phiy (h p) = D (phix p) :=
    LinearHolonomyPreparation.normalized_germ_conjugacy px py h hcontinuous hpoint
      (fun p ↦ t p.val) (fun p ↦ t p.val) (t x) Bx By phix phiy hxg hyg hconst.2
  have hdiff : MDifferentiableAt (complexModel 1) (complexModel 1) h px :=
    LinearHolonomyPreparation.differentiable_of_conjugacy_germ
      (E := S.toDistribution x) (F := S.toDistribution y)
      (complexModel 1) (complexModel 1) px h phix phiy D hconj
  refine ⟨D, ?_, ?_⟩
  · exact @LinearHolonomyPreparation.derivative_of_conjugacy_germ
      _ _ _ _ _ _ gx sx gy sy _ _ _ _ _ _ _ _ _ _ _ _
      (complexModel 1) (complexModel 1) _ _ px py h hpoint hdiff phix phiy
      Jx Jy hDx hDy D hconj
  · exact @LinearHolonomyPreparation.coordinate_neighborhood_of_germ
      _ _ _ _ _ _ gx sx gy sy px h
      (@Diffeomorph.toHomeomorph _ _ _ _ _ _ gx sx _ _ _ _ _ _ _ _ _ _ _ _ _ phix)
      phiy D hpx hsource hconj

end HolomorphicAnosov
