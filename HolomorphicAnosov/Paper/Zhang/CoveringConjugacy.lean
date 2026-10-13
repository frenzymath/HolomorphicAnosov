import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.TensorBounds
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.LinearDecay
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.VectorCover
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.InverseConjugacy
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.HolomorphicCover
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeMetric
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacyInverseLattice
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacyDeckLeaf
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacyNativePaths
import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.IntrinsicAffine

/-! Universal covering conjugacy, biholomorphic lifted dynamics, and deck actions on intrinsic
lifted Anosov leaves. (Zhang, pp. 11–14, eqs. (20), (21)) -/

open scoped ContDiff Manifold Topology Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- A conjugacy to a hyperbolic lattice quotient lifts to universal covers with biholomorphic
dynamics and a full lattice-labelled biholomorphic deck action. The lifted stable and unstable
leaves map to affine spectral subspaces and are preserved by deck transformations. (Zhang, eqs.
(20), (21), Lemmas 3.2, 4.2, pp. 11–14; Hatcher, Props. 1.33, 1.34, 1.37, 1.40; Franks, §1,
Prop. (1.1), Cor. (1.3); HPS, Thm 3.1; Gallier–Quaintance, Prop. 18.5; Petersen, §5.3, Thm
5.3.8) -/
theorem covering_conjugacy
    {d : ℕ} {X V : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (anosov : AnosovDatum f)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (_hDim : Module.finrank ℝ V = 2 * d)
    (Γ : Submodule ℤ V) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    [CompactSpace (V ⧸ Γ.toAddSubgroup)]
    (A : V ≃L[ℝ] V)
    (hHyperbolic : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearEquiv.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1)
    (hΓ : A '' (Γ : Set V) = (Γ : Set V))
    (h : X ≃ₜ V ⧸ Γ.toAddSubgroup)
    (hConjugacy : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = (QuotientAddGroup.mk (A v) : V ⧸ Γ.toAddSubgroup)) :
    ∃ bounds : TensorAnosovBounds f.toReal anosov.splitting anosov.metric,
      1 ≤ bounds.C ∧
    (∃ m : MetricSpace X,
      ∃ hm : ‹TopologicalSpace X› = m.toUniformSpace.toTopologicalSpace,
      letI : MetricSpace X := m.replaceTopology hm
      ∃ native : ∀ (σ : Bool) (x : X),
        NativeAsymptoticLeafDatum (realModel d)
          (if σ then f.toHomeomorph.symm else f.toHomeomorph)
          (if σ then anosov.splitting.unstable.toDistribution
            else anosov.splitting.stable.toDistribution) x,
      let q : V → V ⧸ Γ.toAddSubgroup := QuotientAddGroup.mk
    let decay : Bool → Set V := fun σ ↦ {v | Tendsto
      (fun n : ℕ ↦ ((if σ then A.symm else A) : V → V)^[n] v) atTop (𝓝 0)}
    let liftConclusion : (Y : Type u) → (t : TopologicalSpace Y) → (Y → X) → Prop :=
      fun Y t p ↦
        letI : TopologicalSpace Y := t
        ∃ atlasY : ChartedSpace (ComplexModel d) Y,
          letI : ChartedSpace (ComplexModel d) Y := atlasY
          IsManifold (complexModel d) ∞ Y ∧
          (∀ c : OpenPartialHomeomorph Y (ComplexModel d),
            c ∈ atlas (ComplexModel d) Y ↔
              ∃ (e : OpenPartialHomeomorph Y X)
                (z : OpenPartialHomeomorph X (ComplexModel d)),
                Set.EqOn e p e.source ∧ z ∈ atlas (ComplexModel d) X ∧ c = e.trans z) ∧
          ContMDiff (complexModel d) (complexModel d) ∞ p ∧
          (∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
            y ∈ e.source ∧ Set.EqOn e p e.source ∧
              ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
              ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) ∧
          ∃ (H : Y ≃ₜ V) (F : Biholomorph d d Y Y) (δ : Γ → Biholomorph d d Y Y),
            (∀ y, q (H y) = h (p y)) ∧
            (∀ y, p (F y) = f (p y)) ∧
            (∀ y, p (F.symm y) = f.symm (p y)) ∧
            (∀ y, H (F y) = A (H y)) ∧
            (∀ γ y, H (δ γ y) = H y + (γ : V)) ∧
            (∀ γ y, p (δ γ y) = p y) ∧
            (∀ D : Y ≃ₜ Y, (∀ y, p (D y) = p y) ↔
              ∃! γ : Γ, ∀ y, D y = δ γ y) ∧
            (∀ γ γ' : Γ, (γ' : V) = A (γ : V) →
              ∀ y, F (δ γ y) = δ γ' (F y)) ∧
            (∀ (σ : Bool) (y : Y),
              let x := p y
              let leafHomeomorph := if σ then f.toHomeomorph.symm else f.toHomeomorph
              letI : TopologicalSpace (StableAsymptoticLeaf leafHomeomorph x) :=
                (native σ x).topology
              ∀ a : StableAsymptoticLeaf leafHomeomorph x, a.val = p y →
                let leafRange : Y → Set Y := fun y₀ ↦
                  liftedIntrinsicLeafRange p Subtype.val a y₀
                H '' leafRange y = (fun v : V ↦ H y + v) '' decay σ ∧
                  ∀ γ : Γ, δ γ '' leafRange y = leafRange (δ γ y))
    IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace V ∧
      (∀ D : V ≃ₜ V, (∀ v, q (D v) = q v) ↔
        ∃! γ : Γ, ∀ v, D v = v + (γ : V)) ∧
      (∃ Vs Vu : Submodule ℝ V,
        (Vs : Set V) = decay false ∧ (Vu : Set V) = decay true ∧ IsCompl Vs Vu) ∧
      (∃ p : V → X, IsCoveringMap p ∧ Function.Surjective p ∧
        liftConclusion V inferInstance p) ∧
      (∀ (Y : Type u) (t : TopologicalSpace Y),
        letI : TopologicalSpace Y := t
        T2Space Y → SecondCountableTopology Y → SimplyConnectedSpace Y →
          LocallyPathConnectedSpace Y → ∀ p : Y → X,
            IsCoveringMap p → Function.Surjective p → liftConclusion Y t p)) := by
  classical
  obtain ⟨bounds, hC⟩ := covering_conjugacy_tensor_bounds_g15 f anosov
  refine ⟨bounds, hC, ?_⟩
  obtain ⟨m, hm, hn⟩ := covering_conjugacy_native_metric_g15 f anosov bounds
  refine ⟨m, hm, ?_⟩
  let : MetricSpace X := m.replaceTopology hm
  obtain ⟨native⟩ := hn
  refine ⟨native, ?_⟩
  extract_lets q decay liftConclusion
  obtain ⟨hq, hqs, hsimply, hdeck⟩ := covering_conjugacy_vector_cover_g15 Γ
  refine ⟨hq, hqs, hsimply, hdeck, ?_⟩
  obtain ⟨Vs, Vu, hs, hu, hc⟩ := covering_conjugacy_linear_decay_g15 A hHyperbolic
  refine ⟨⟨Vs, Vu, hs, hu, hc⟩, ?_⟩
  
  have hAffine : ∀ (Y : Type u) (t : TopologicalSpace Y),
      letI := t
      ∀ (p : Y → X), IsCoveringMap p → ∀ H : Y ≃ₜ V,
        (∀ y, q (H y) = h (p y)) → ∀ (σ : Bool) (y : Y),
        let leafHomeomorph := if σ then f.toHomeomorph.symm else f.toHomeomorph
        letI := (native σ (p y)).topology
        ∀ a : StableAsymptoticLeaf leafHomeomorph (p y), a.val = p y →
          H '' liftedIntrinsicLeafRange p Subtype.val a y =
            (fun v : V ↦ H y + v) '' decay σ := by
    intro Y t p hp H hH σ y
    dsimp only
    intro a ha
    let : TopologicalSpace Y := t
    let leafHomeomorph := if σ then f.toHomeomorph.symm else f.toHomeomorph
    let D := if σ then anosov.splitting.unstable.toDistribution
      else anosov.splitting.stable.toDistribution
    let leaf := native σ (p y)
    let : TopologicalSpace (StableAsymptoticLeaf leafHomeomorph (p y)) := leaf.topology
    obtain ⟨hpaths, hj⟩ := covering_conjugacy_native_paths_g15 leafHomeomorph D (p y) leaf
    let : PathConnectedSpace (StableAsymptoticLeaf leafHomeomorph (p y)) := hpaths
    have hpres : ⇑(if σ then A.symm else A) '' (Γ : Set V) = (Γ : Set V) := by
      cases σ with
      | false => exact hΓ
      | true => exact covering_conjugacy_inverse_lattice_g15 Γ A hΓ
    have hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
        h (leafHomeomorph x) =
          (QuotientAddGroup.mk ((if σ then A.symm else A) v) : V ⧸ Γ.toAddSubgroup) := by
      cases σ with
      | false => exact hConjugacy
      | true => exact covering_conjugacy_inverse_conjugacy_g15 Γ f A h hConjugacy
    have hcarrier : ∀ b : StableAsymptoticLeaf leafHomeomorph (p y),
        ForwardAsymptotic leafHomeomorph (p y) b.val := fun b ↦ b.property
    have hfull : ∀ x, ForwardAsymptotic leafHomeomorph (p y) x →
        ∃ b : StableAsymptoticLeaf leafHomeomorph (p y), b.val = x :=
      fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
    have hresult := intrinsic_affine Γ (if σ then A.symm else A) hpres
      leafHomeomorph h hc p hp H hH y Subtype.val hj a ha hcarrier hfull
    cases σ <;> exact hresult.1
  have hLift : ∀ (Y : Type u) (t : TopologicalSpace Y),
      letI := t
      T2Space Y → SecondCountableTopology Y → SimplyConnectedSpace Y →
        LocallyPathConnectedSpace Y → ∀ p : Y → X,
          IsCoveringMap p → Function.Surjective p → liftConclusion Y t p := by
    intro Y t hT hSC hSimply hLPC p hp hps
    let : TopologicalSpace Y := t
    let : T2Space Y := hT
    let : SecondCountableTopology Y := hSC
    let : SimplyConnectedSpace Y := hSimply
    let : LocallyPathConnectedSpace Y := hLPC
    obtain ⟨atlasY, hman, hatlas, hpSmooth, hsheets, H, F, δ,
      hH, hF, hFi, hHF, hδH, hδp, hδall, hδF⟩ :=
      covering_conjugacy_holomorphic_cover_g15 Γ f A h hConjugacy p hp hps
    let : ChartedSpace (ComplexModel d) Y := atlasY
    let : IsManifold (complexModel d) ∞ Y := hman
    refine ⟨atlasY, hman, hatlas, hpSmooth, hsheets, H, F, δ,
      hH, hF, hFi, hHF, hδH, hδp, hδall, hδF, ?_⟩
    intro σ y
    dsimp only
    intro a ha
    let : TopologicalSpace (StableAsymptoticLeaf
        (if σ then f.toHomeomorph.symm else f.toHomeomorph) (p y)) :=
      (native σ (p y)).topology
    refine ⟨hAffine Y t p hp H hH σ y a ha, ?_⟩
    intro γ
    exact covering_conjugacy_deck_leaf_g15 p Subtype.val a y
      (δ γ).toHomeomorph (hδp γ)
  refine ⟨?_, hLift⟩
  let : SimplyConnectedSpace V := hsimply
  let p : V → X := h.symm ∘ q
  have hp : IsCoveringMap p := hq.homeomorph_comp h.symm
  have hps : Function.Surjective p := h.symm.surjective.comp hqs
  exact ⟨p, hp, hps, hLift V inferInstance inferInstance inferInstance
    inferInstance inferInstance p hp hps⟩


end HolomorphicAnosov
