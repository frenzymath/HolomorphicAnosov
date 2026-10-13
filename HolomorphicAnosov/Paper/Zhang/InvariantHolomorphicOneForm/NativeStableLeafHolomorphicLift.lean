import HolomorphicAnosov.Geometry.NativeComplexStableLeafDatum
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacy
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- The holomorphic stable-leaf inclusion has a based injective holomorphic lift through the
covering, whose range is exactly the lifted intrinsic stable leaf. (Zhang, Lemma 2.7, p.9, Lemma
4.2, pp.14–15; Hatcher, Props. 1.30 and 1.34) -/
theorem native_stable_leaf_holomorphic_lift
    {d : ℕ} {X Y : Type u} [MetricSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
    (f : X ≃ₜ X) (S : ContinuousComplexTangentSubbundle (complexModel d) X)
    (ι : Type u) (L : ι → Type u) [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L)
    (p : Y → X) (hp : IsCoveringMap p)
    (hsheets : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target)
    (i : ι) (z : L i) (y : Y) (hy : p y = (F.partition.leaf i).inclusion z)
    (hEuclidean : Nonempty ((Fin 2 → ℝ) ≃ₜ L i)) :
    letI := (F.complexUpgrade i).charts
    ∃ ℓ : L i → Y,
      ContMDiff (complexModel 1) (complexModel d) ∞ ℓ ∧
      Function.Injective ℓ ∧ ℓ z = y ∧
      (∀ w, p (ℓ w) = (F.partition.leaf i).inclusion w) ∧
      Set.range ℓ = liftedIntrinsicLeafRange p (F.partition.leaf i).inclusion z y := by
  let := (F.complexUpgrade i).charts
  obtain ⟨e⟩ := hEuclidean
  let j := (F.partition.leaf i).inclusion
  have hj : ContMDiff (complexModel 1) (complexModel d) ∞ j :=
    (F.complexUpgrade i).inclusion_holomorphic
  have : SimplyConnectedSpace (L i) := e.symm.toHomotopyEquiv.simplyConnectedSpace
  have : LocallyPathConnectedSpace (L i) :=
    ChartedSpace.locallyPathConnectedSpace (ComplexModel 1) (L i)
  obtain ⟨ℓ, ⟨hbase, hproj⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts ⟨j, hj.continuous⟩ z y hy
  have hproj' : ∀ w, p (ℓ w) = j w := fun w ↦ congrFun hproj w
  have hhol : ContMDiff (complexModel 1) (complexModel d) ∞ ℓ := by
    intro w
    obtain ⟨e, hw, he, _, hei⟩ := hsheets (ℓ w)
    have hew : j w ∈ e.target := by
      rw [← hproj' w, ← he hw]
      exact e.map_source hw
    have hcomp := (hei (j w) hew).contMDiffAt (e.open_target.mem_nhds hew)
      |>.comp w (hj w)
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [ℓ.continuous.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hw)] with w' hw'
    change ℓ w' = e.symm (j w')
    rw [← hproj' w', ← he hw', e.left_inv hw']
  refine ⟨ℓ, hhol, ?_, hbase, hproj', ?_⟩
  · intro v w hvw
    apply (F.partition.leaf i).injective
    exact (hproj' v).symm.trans ((congrArg p hvw).trans (hproj' w))
  · apply Set.Subset.antisymm
    · rintro _ ⟨w, rfl⟩
      let γ := PathConnectedSpace.somePath z w
      refine ⟨w, γ, (γ.map ℓ.continuous).cast hbase.symm rfl, ?_⟩
      intro t
      exact hproj' (γ t)
    · rintro w ⟨b, γ, η, hη⟩
      have heq : (fun t ↦ ℓ (γ t)) = η := hp.eq_of_comp_eq
        (ℓ.continuous.comp γ.continuous) η.continuous (by
          funext t
          exact (hproj' (γ t)).trans (hη t).symm)
        0 (by simpa only [Path.source] using hbase)
      exact ⟨b, by simpa only [Path.target] using congrFun heq 1⟩


end HolomorphicAnosov.Paper.Zhang
