import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import Mathlib.Topology.VectorBundle.Constructions

/-!
# Restriction of a continuous tangent subbundle

Source: Hatcher, Vector Bundles and K-Theory, Proposition 1.5, pp.18–19:
restriction is the pullback along the subset inclusion. The topology here is
exactly the topology induced by the original tangent-bundle inclusion.
-/

namespace HolomorphicAnosov
open scoped ContDiff Bundle Manifold

/-- Restrict a continuous real tangent subbundle to any subset, including
empty or nonopen subsets. Pull back each finite linear trivialization along
the continuous subtype inclusion. The pullback topology is the infimum of
the topology induced by its base projection and the topology induced by its
map to the original subbundle. The latter is precisely the specified tangent
inclusion topology. The base projection is already continuous for this
specified topology, since the tangent-bundle projection is continuous and
the subset carries the induced topology. Thus the infimum equals the
specified topology, and the pulled-back chart remains linear. -/
theorem continuous_tangent_subbundle_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (V : ContinuousRealTangentSubbundle 𝓘(ℝ, E) M) (A : Set M) :
    BowenBasicSetCoding.IsContinuousDistributionOn A V.toDistribution := by
  intro x
  obtain ⟨r,e,hxe,he⟩ := V.locally_trivial x.val
  refine ⟨r,?_⟩
  let F := Fin r → ℝ
  let W := fun y : M ↦ ↥(V.toDistribution y)
  let inclusion : Bundle.TotalSpace F W → TangentBundle 𝓘(ℝ,E) M :=
    fun z ↦ ⟨z.proj,z.snd.val⟩
  let tW : TopologicalSpace (Bundle.TotalSpace F W) :=
    TopologicalSpace.induced inclusion inferInstance
  let _ := tW
  let f : C(A,M) := ⟨Subtype.val,continuous_subtype_val⟩
  let tA : TopologicalSpace (Bundle.TotalSpace F (fun y : A ↦ W y.val)) :=
    TopologicalSpace.induced (fun z ↦ (⟨z.proj.val,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M))
      inferInstance
  have htop : pullbackTopology F W (f : A → M) = tA := by
    rw [pullbackTopology_def]
    change TopologicalSpace.induced Bundle.TotalSpace.proj inferInstance ⊓
      TopologicalSpace.induced (Bundle.Pullback.lift (f : A → M))
        (TopologicalSpace.induced inclusion inferInstance) = tA
    rw [induced_compose]
    change TopologicalSpace.induced Bundle.TotalSpace.proj inferInstance ⊓ tA = tA
    apply inf_eq_right.mpr
    apply continuous_iff_le_induced.mp
    let _ := tA
    apply Continuous.subtype_mk
    have hinc : Continuous (fun z : Bundle.TotalSpace F (fun y : A ↦ W y.val) ↦
        (⟨z.proj.val,z.snd.val⟩ : TangentBundle 𝓘(ℝ,E) M)) := continuous_induced_dom
    exact ((FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ,E))).comp hinc)
  have he' : e.IsLinear ℝ := he
  let _ := he'
  let hp := e.pullback f
  have hpl : hp.IsLinear ℝ := Bundle.Trivialization.pullback_linear ℝ e f
  change ∃ e : @Bundle.Trivialization A F
    (Bundle.TotalSpace F (fun y : A ↦ W y.val)) _ _ tA Bundle.TotalSpace.proj,
      x ∈ e.baseSet ∧ e.IsLinear ℝ
  rw [← htop]
  exact ⟨hp,hxe,hpl⟩

end HolomorphicAnosov
