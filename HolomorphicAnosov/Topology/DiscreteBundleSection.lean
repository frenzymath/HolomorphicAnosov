import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting

open Set Filter _root_.Topology

namespace HolomorphicAnosov

/-- A bundle with discrete fibre over a simply connected, locally path connected
base has a continuous section, and that section has locally constant coordinates
in every bundle chart. Source: Hatcher, *Algebraic Topology*, Proposition 1.33,
p.61, the covering lifting criterion. Apply the criterion to the identity of the
base and any chosen point in the fibre; simple connectedness makes the lifting
condition automatic. The resulting lift is a section. In each trivialization,
its fibre coordinate is continuous into a discrete space and hence is constant
on a neighborhood of each point in the chart domain. -/
theorem discrete_bundleCore_section
    {ι B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [DiscreteTopology F] [Nonempty F]
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (Z : FiberBundleCore ι B F) :
    ∃ s : C(B, Z.TotalSpace),
      (∀ x, (s x).proj = x) ∧
      ∀ i x, x ∈ Z.baseSet i →
        ∀ᶠ y in 𝓝 x, ((Z.localTriv i) (s y)).2 = ((Z.localTriv i) (s x)).2 := by
  classical
  have hcov : IsCoveringMap Z.proj := FiberBundle.isCoveringMap
  let x₀ : B := Classical.choice inferInstance
  let e₀ : Z.TotalSpace := ⟨x₀, (Classical.choice inferInstance : F)⟩
  obtain ⟨s, hs, _⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id B) x₀ e₀ rfl
  have hproj (x : B) : (s x).proj = x := congrFun hs.2 x
  refine ⟨s, hproj, ?_⟩
  intro i x hx
  have hsource : s x ∈ (Z.localTriv i).source := by
    change (s x).proj ∈ Z.baseSet i
    simpa only [hproj x] using hx
  have hct : ContinuousAt (fun y ↦ ((Z.localTriv i) (s y)).2) x :=
    (((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hsource).comp
      s.continuous.continuousAt).snd
  simpa only [ContinuousAt, nhds_discrete, tendsto_pure] using hct

end HolomorphicAnosov
