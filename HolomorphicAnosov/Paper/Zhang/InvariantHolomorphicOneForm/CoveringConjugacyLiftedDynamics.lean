import HolomorphicAnosov.Paper.Zhang.CoveringConjugacy

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- A toral conjugacy lifts to a holomorphic covering with compatible lifted dynamics and a fixed
basepoint. The lattice acts by biholomorphic deck transformations, freely and transitively on
each fibre. (Zhang, §4, p.14, Lemma 4.2, (21)–(23)) -/
theorem covering_conjugacy_lifted_dynamics
    {d : ℕ} {X V : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hDim : Module.finrank ℝ V = 2 * d)
    (Γ : Submodule ℤ V) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    [CompactSpace (V ⧸ Γ.toAddSubgroup)]
    (A : V ≃L[ℝ] V)
    (hHyperbolic : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearEquiv.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1)
    (hΓ : A '' (Γ : Set V) = (Γ : Set V))
    (h : X ≃ₜ V ⧸ Γ.toAddSubgroup)
    (hConjugacy : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = (QuotientAddGroup.mk (A v) : V ⧸ Γ.toAddSubgroup)) :
    ∃ (p : V → X), IsCoveringMap p ∧ Function.Surjective p ∧
      ∃ atlasV : ChartedSpace (ComplexModel d) V,
        letI := atlasV
        IsManifold (complexModel d) ∞ V ∧
        ContMDiff (complexModel d) (complexModel d) ∞ p ∧
        (∀ y : V, ∃ e : OpenPartialHomeomorph V X,
          y ∈ e.source ∧ Set.EqOn e p e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
          ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) ∧
        ∃ (H : V ≃ₜ V) (F : Biholomorph d d V V) (δ : Γ → Biholomorph d d V V),
          (∀ y, (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) = h (p y)) ∧
          (∀ y, p (F y) = f (p y)) ∧
          (∀ y, H (F y) = A (H y)) ∧
          (∀ γ y, H (δ γ y) = H y + (γ : V)) ∧
          (∀ γ y, p (δ γ y) = p y) ∧
          F (H.symm 0) = H.symm 0 ∧ f (p (H.symm 0)) = p (H.symm 0) ∧
          (∀ y z, p y = p z ↔ H z - H y ∈ Γ) ∧
          (∀ y z, p y = p z → ∃! γ : Γ, δ γ y = z) := by
  rcases covering_conjugacy f a hDim Γ A hHyperbolic hΓ h hConjugacy with
    ⟨bounds, hbound, m, hm, native, hq, hqSurj, hSimply, hdeck, hsplit, hp, hAll⟩
  rcases hp with ⟨p, hpCover, hpSurj, hLift⟩
  rcases hLift with ⟨atlasY, hman, hatlas, hpSmooth, hSheets, hDynamics⟩
  rcases hDynamics with ⟨H, F, δ, hHp, hFp, hFinv, hHF, hDelta, hDeltaP, hDeck, hFDelta, hLeaf⟩
  let : ChartedSpace (ComplexModel d) V := atlasY
  have hfixed : F (H.symm 0) = H.symm 0 := by
    apply H.injective
    rw [hHF, H.apply_symm_apply, map_zero]
  have hfibre (y z : V) : p y = p z ↔ H z - H y ∈ Γ := by
    constructor
    · intro hyz
      have hq : (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) =
          QuotientAddGroup.mk (H z) := (hHp y).trans ((congrArg h hyz).trans (hHp z).symm)
      simpa only [sub_eq_add_neg, add_comm, Submodule.mem_toAddSubgroup] using
        (QuotientAddGroup.eq.mp hq)
    · intro hmem
      apply h.injective
      rw [← hHp y, ← hHp z]
      apply QuotientAddGroup.eq.mpr
      simpa only [sub_eq_add_neg, add_comm, Submodule.mem_toAddSubgroup] using hmem
  refine ⟨p, hpCover, hpSurj, atlasY, hman, hpSmooth, hSheets,
    H, F, δ, hHp, hFp, hHF, hDelta, hDeltaP, hfixed, ?_, hfibre, ?_⟩
  · rw [← hFp, hfixed]
  · intro y z hyz
    let γ : Γ := ⟨H z - H y, (hfibre y z).mp hyz⟩
    refine ⟨γ, ?_, ?_⟩
    · apply H.injective
      rw [hDelta]
      change H y + (H z - H y) = H z
      abel
    · intro γ' hγ'
      apply Subtype.ext
      have heq := hDelta γ' y
      rw [hγ'] at heq
      change (γ' : V) = H z - H y
      rw [heq]
      exact (add_sub_cancel_left (H y) (γ' : V)).symm


end HolomorphicAnosov.Paper.Zhang
