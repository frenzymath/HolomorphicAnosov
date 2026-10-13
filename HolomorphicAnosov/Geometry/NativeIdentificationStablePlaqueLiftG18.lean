import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.Holonomy.ImmersedLeafLiftLocalDiffeomorph

noncomputable section
open Set Manifold TopologicalSpace _root_.Topology
open scoped ContDiff _root_.Topology
namespace HolomorphicAnosov
universe u v
attribute [local instance] complex_isManifold_real

/-- A smooth embedded plaque tangent to the stable distribution lifts to an open embedding into its
stable partition class under a point-preserving identification with the intrinsic asymptotic
leaf. (Hirsch–Pugh–Shub, §7, pp. 115–116) -/
theorem native_identification_stable_plaque_open_lift_g18
    {d s t r : ℕ} {M : Type u} {X : Type*}
    [MetricSpace M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ X]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t)
    (j : X → M) (hj : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ j)
    (hinj : Function.Injective j)
    (hji : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j z))
    (hT : ∀ z, (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j z).range = Ps (j z)) :
    letI := A.realAmbientCharts
    ∀ x : M, (∀ z, A.F.stablePartition x (j z)) →
      letI := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
      ∃ g : X → IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x),
        (∀ z, (g z).val = j z) ∧ IsOpenEmbedding g := by
  let := A.realAmbientCharts
  intro x hclass
  let := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
  let := A.stableTopology x
  let := A.stableCharts x
  let := (A.nativeS x).smoothAtlas
  let := (A.nativeS x).secondCountable
  let e := A.stableClassHomeomorph x
  let : SecondCountableTopology
      (IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x)) :=
    e.secondCountableTopology
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace (Fin r → ℝ) X
  let g₀ : X → IntrinsicFoliationLeaf A.F.stablePartition
      (Quotient.mk A.F.stablePartition x) :=
    fun z ↦ ⟨j z, Quotient.sound (A.F.stablePartition.symm (hclass z))⟩
  have hc₀ : Continuous g₀ := continuous_stable_leaf_lift_g9 A.F _
    inferInstance g₀ hj.continuous
  let g : X → StableAsymptoticLeaf f x := e ∘ g₀
  have hc : Continuous g := e.continuous.comp hc₀
  have he : (Subtype.val : StableAsymptoticLeaf f x → M) ∘ g = j := by
    funext z
    exact A.stable_points x (g₀ z)
  have hr (z : X) : (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j z).range =
      (mfderiv 𝓘(ℝ, Fin (A.nativeS x).rank → ℝ) (realModel d)
        (Subtype.val : StableAsymptoticLeaf f x → M) (g z)).range := by
    rw [hT z, (A.nativeS x).tangent_image]
    rw [show (g z).val = j z from congrFun he z]
  obtain ⟨_, hopen⟩ := immersed_leaf_lift_local_diffeomorph j
    (Subtype.val : StableAsymptoticLeaf f x → M) g hj (A.nativeS x).inclusion_smooth
    hji (A.nativeS x).inclusion_immersion hc he hr
  refine ⟨g₀, fun _ ↦ rfl, ?_⟩
  have ho := e.symm.isOpenEmbedding.comp (hopen hinj)
  simpa only [g, Function.comp_def, Homeomorph.symm_apply_apply] using ho


/-- An embedded stable plaque restricted to its open parameter domain lifts to an open embedding
into its identified stable partition class. -/
theorem native_identification_embedded_stable_plaque_open_lift_g18
    {d s t r : ℕ} {M : Type u}
    [MetricSpace M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t) {center : M}
    (F : NativeEmbeddedPlaque (realModel d) (V := Fin r → ℝ) Ps center) :
    letI := A.realAmbientCharts
    ∀ x : M, (∀ v ∈ F.domain, A.F.stablePartition x (F.param v)) →
      letI := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
      let U : Opens (Fin r → ℝ) := ⟨F.domain,F.domain_open⟩
      ∃ g : U → IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition x),
        (∀ v, (g v).val = F.param v) ∧ IsOpenEmbedding g := by
  let := A.realAmbientCharts
  intro x hclass
  let := A.F.stableTopology (Quotient.mk A.F.stablePartition x)
  let U : Opens (Fin r → ℝ) := ⟨F.domain,F.domain_open⟩
  let j : U → M := fun v ↦ F.param v
  have hj : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ j := by
    intro v
    exact contMDiffAt_subtype_iff.mpr
      ((F.smooth v.val v.property).contMDiffAt (F.domain_open.mem_nhds v.property))
  have hd (v : U) : mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j v =
      (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) F.param v.val).comp
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) (Subtype.val : U → (Fin r → ℝ)) v) :=
    mfderiv_comp v
      (((F.smooth v.val v.property).contMDiffAt
        (F.domain_open.mem_nhds v.property)).mdifferentiableAt (by simp))
      (contMDiff_subtype_val.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  have hji (v : U) : Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j v) := by
    rw [hd]
    exact (F.immersed v.val v.property).comp
      (openSubsetInclusion_mfderiv_bijective 𝓘(ℝ, Fin r → ℝ) U v).injective
  have hT (v : U) : (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j v).range =
      Ps (j v) := by
    rw [hd, ← F.tangent v.val v.property]
    apply LinearMap.range_comp_of_range_eq_top
    exact LinearMap.range_eq_top.mpr
      (openSubsetInclusion_mfderiv_bijective 𝓘(ℝ, Fin r → ℝ) U v).surjective
  exact native_identification_stable_plaque_open_lift_g18 A j hj F.embedded.injective hji hT x
    (fun v ↦ hclass v.val v.property)

end HolomorphicAnosov
