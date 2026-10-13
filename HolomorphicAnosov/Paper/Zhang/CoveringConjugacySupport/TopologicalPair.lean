import HolomorphicAnosov.Paper.Zhang.CompatibleUniversalLifts
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.VectorCover
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.QuotientDynamics

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- Hatcher pointed universal lifting and Zhang equation (20), with the actual quotient model and original conjugacy. -/
theorem covering_conjugacy_topological_pair_g15
    {d : ℕ} {X V Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] [Nonempty X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace Y] [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (f : Biholomorph d d X X) (A : V ≃L[ℝ] V)
    (h : X ≃ₜ V ⧸ Γ.toAddSubgroup)
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = QuotientAddGroup.mk (A v))
    (p : Y → X) (hp : IsCoveringMap p) (hps : Function.Surjective p) :
    ∃ (H : Y ≃ₜ V) (F : Y ≃ₜ Y),
      (∀ y, (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) = h (p y)) ∧
      (∀ y, p (F y) = f (p y)) ∧
      (∀ y, p (F.symm y) = f.symm (p y)) ∧
      (∀ y, H (F y) = A (H y)) := by
  obtain ⟨hq, hqs, hsimply, _⟩ := covering_conjugacy_vector_cover_g15 Γ
  let : SimplyConnectedSpace V := hsimply
  obtain ⟨α, hA, hf⟩ := covering_conjugacy_quotient_dynamics_g15 Γ f A h hc
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y₀, _⟩ := hps x
  obtain ⟨v₀, hv₀⟩ := hqs (h (p y₀))
  obtain ⟨⟨HF, hHF, _⟩, hmore⟩ := compatible_universal_lifts
    p (QuotientAddGroup.mk : V → V ⧸ Γ.toAddSubgroup) hp hq hps hqs
      h f.toHomeomorph α A.toHomeomorph hA hf y₀ v₀ hv₀
  obtain ⟨_, _, _, hinverse⟩ := hmore HF hHF
  refine ⟨HF.1, HF.2, ?_, ?_, ?_, ?_⟩
  · intro y
    exact congrFun hHF.2.1 y
  · intro y
    exact congrFun hHF.2.2.1 y
  · intro y
    exact congrFun hinverse y
  · intro y
    exact congrFun hHF.2.2.2 y


end HolomorphicAnosov
