import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.LiftContMDiff
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.TopologicalPair
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.LabelledDeck

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- C3--C6 assembled on the original chosen cover. -/
theorem covering_conjugacy_holomorphic_cover_g15
    {d : ℕ} {X V Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (f : Biholomorph d d X X) (A : V ≃L[ℝ] V)
    (h : X ≃ₜ V ⧸ Γ.toAddSubgroup)
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = QuotientAddGroup.mk (A v))
    (p : Y → X) (hp : IsCoveringMap p) (hps : Function.Surjective p) :
    ∃ atlasY : ChartedSpace (ComplexModel d) Y,
      letI : ChartedSpace (ComplexModel d) Y := atlasY
      IsManifold (complexModel d) ∞ Y ∧
      (∀ c : OpenPartialHomeomorph Y (ComplexModel d),
        c ∈ atlas (ComplexModel d) Y ↔
          ∃ (e : OpenPartialHomeomorph Y X) (z : OpenPartialHomeomorph X (ComplexModel d)),
            Set.EqOn e p e.source ∧ z ∈ atlas (ComplexModel d) X ∧ c = e.trans z) ∧
      ContMDiff (complexModel d) (complexModel d) ∞ p ∧
      (∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
        y ∈ e.source ∧ Set.EqOn e p e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) ∧
      ∃ (H : Y ≃ₜ V) (F : Biholomorph d d Y Y) (δ : Γ → Biholomorph d d Y Y),
        (∀ y, (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) = h (p y)) ∧
        (∀ y, p (F y) = f (p y)) ∧
        (∀ y, p (F.symm y) = f.symm (p y)) ∧
        (∀ y, H (F y) = A (H y)) ∧
        (∀ γ y, H (δ γ y) = H y + (γ : V)) ∧
        (∀ γ y, p (δ γ y) = p y) ∧
        (∀ D : Y ≃ₜ Y, (∀ y, p (D y) = p y) ↔ ∃! γ : Γ, ∀ y, D y = δ γ y) ∧
        (∀ γ γ' : Γ, (γ' : V) = A (γ : V) → ∀ y, F (δ γ y) = δ γ' (F y)) := by
  classical
  obtain ⟨H, L, hH, hL, hLi, hHL⟩ :=
    covering_conjugacy_topological_pair_g15 Γ f A h hc p hp hps
  obtain ⟨atlasY, hman, hatlas, hpSmooth, hsheets, _, hdeckb, _⟩ :=
    complex_cover_pullback_atlas (d := d) p hp hps
  let : ChartedSpace (ComplexModel d) Y := atlasY
  let : IsManifold (complexModel d) ∞ Y := hman
  have hLs := covering_conjugacy_lift_contMDiff_g15 p hpSmooth hsheets L f hL
  have hLis := covering_conjugacy_lift_contMDiff_g15 p hpSmooth hsheets L.symm f.symm hLi
  let F : Biholomorph d d Y Y :=
    ⟨L.toEquiv, hLs, hLis⟩
  obtain ⟨δh, hδH, hδp, hδall, hδF⟩ :=
    covering_conjugacy_labelled_deck_g15 Γ p h H hH A L hHL
  let δ : Γ → Biholomorph d d Y Y := fun γ ↦
    Classical.choose (hdeckb (δh γ) (hδp γ))
  have hδeq (γ : Γ) (y : Y) : δ γ y = δh γ y :=
    congrArg (fun E : Y ≃ₜ Y ↦ E y)
      (Classical.choose_spec (hdeckb (δh γ) (hδp γ)))
  refine ⟨atlasY, hman, hatlas, hpSmooth, hsheets, H, F, δ,
    hH, hL, hLi, hHL, ?_, ?_, ?_, ?_⟩
  · intro γ y
    rw [hδeq]
    exact hδH γ y
  · intro γ y
    rw [hδeq]
    exact hδp γ y
  · intro D
    simpa only [hδeq] using hδall D
  · intro γ γ' hγ' y
    change L (δ γ y) = δ γ' (L y)
    rw [hδeq, hδeq]
    exact hδF γ γ' hγ' y


end HolomorphicAnosov
