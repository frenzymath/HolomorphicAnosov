import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeStableLeafHolomorphicLift

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- A complete holomorphic stable-leaf coordinate gives an injective holomorphic parametrization of
the lifted stable leaf, normalized at its chosen basepoint and projecting to the original leaf
inclusion. (Zhang, Lemmas 2.7 and 4.2) -/
theorem native_stable_leaf_coordinate_lift
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
    (hEuclidean : Nonempty ((Fin 2 → ℝ) ≃ₜ L i))
    (E : Type*) [nE : NormedAddCommGroup E] [sE : NormedSpace ℂ E] :
    letI := (F.complexUpgrade i).charts
    ∀ φ : Diffeomorph (complexModel 1) 𝓘(ℂ, E) (L i) E ∞,
    φ z = 0 → ∃ e : E → Y,
      ContMDiff 𝓘(ℂ, E) (complexModel d) ∞ e ∧
      Function.Injective e ∧ e 0 = y ∧
      (∀ v, p (e v) = (F.partition.leaf i).inclusion (φ.symm v)) ∧
      Set.range e = liftedIntrinsicLeafRange p (F.partition.leaf i).inclusion z y := by
  let := (F.complexUpgrade i).charts
  intro φ hφ
  obtain ⟨ℓ, hhol, hinj, hbase, hproj, hrange⟩ :=
    native_stable_leaf_holomorphic_lift f S ι L F p hp hsheets i z y hy hEuclidean
  refine ⟨ℓ ∘ φ.symm, hhol.comp φ.symm.contMDiff, hinj.comp φ.symm.injective,
    ?_, fun v ↦ hproj (φ.symm v), ?_⟩
  · change ℓ (φ.symm 0) = y
    rw [← hφ, φ.symm_apply_apply, hbase]
  · have hsurj : Function.Surjective (φ.symm : E → L i) := φ.symm.surjective
    exact (hsurj.range_comp ℓ).trans hrange


end HolomorphicAnosov.Paper.Zhang
