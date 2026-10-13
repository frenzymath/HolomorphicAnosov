import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.PathDecay
import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.LatticeDecayZero
import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRange
import Mathlib.Topology.Homotopy.Lifting

open scoped Topology _root_.Topology
open Filter Set
universe u
namespace HolomorphicAnosov
noncomputable section

/-- Native path connectivity and covering path lifting turn the forward path inclusion into the
entire affine image and its bijection; the only same-fibre decay difference is zero. -/
theorem intrinsic_affine
    {V M Y L : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MetricSpace M] [CompactSpace M] [TopologicalSpace Y] [TopologicalSpace L]
    [PathConnectedSpace L]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (A : V ≃L[ℝ] V) (hΓ : A '' (Γ : Set V) = (Γ : Set V))
    (f : M ≃ₜ M) (h : M ≃ₜ V ⧸ Γ.toAddSubgroup)
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = (QuotientAddGroup.mk (A v) : V ⧸ Γ.toAddSubgroup))
    (p : Y → M) (hp : IsCoveringMap p) (H : Y ≃ₜ V)
    (hH : ∀ y, (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) = h (p y))
    (y : Y) (j : L → M) (hj : Continuous j) (a : L) (ha : j a = p y)
    (hcarrier : ∀ b, ForwardAsymptotic f (p y) (j b))
    (hfull : ∀ x, ForwardAsymptotic f (p y) x → ∃ b, j b = x) :
    H '' liftedIntrinsicLeafRange p j a y = (fun v ↦ H y + v) '' (fullDecaySubmodule A : Set V) ∧
      Set.BijOn H (liftedIntrinsicLeafRange p j a y)
        ((fun v ↦ H y + v) '' (fullDecaySubmodule A : Set V)) := by
  classical
  let S := fullDecaySubmodule A
  have hfwd : ∀ z ∈ liftedIntrinsicLeafRange p j a y, H z - H y ∈ S := by
    rintro z ⟨b, γ, η, he⟩
    exact path_decay Γ A hΓ f h hc p H hH y z η (fun t ↦ by
      rw [he t]
      exact hcarrier (γ t))
  have hback : ∀ v ∈ S, H.symm (H y + v) ∈ liftedIntrinsicLeafRange p j a y := by
    intro v hv
    let z := H.symm (H y + v)
    have hdec : Tendsto (fun n : ℕ ↦ (A : V → V)^[n] (H z - H y)) atTop (𝓝 0) := by
      simpa [z, S, fullDecaySubmodule] using hv
    have hq : Tendsto (fun n : ℕ ↦ (QuotientAddGroup.mk ((A : V → V)^[n] (H z - H y)) :
        V ⧸ Γ.toAddSubgroup)) atTop (𝓝 0) := by
      exact (QuotientAddGroup.continuous_mk.tendsto 0 |>.comp hdec)
    have hasyp := (asymptotic_quotient_iff Γ A f h hc (p y) (p z) (H y) (H z)
      (hH y) (hH z)).mpr hq
    obtain ⟨b, hb⟩ := hfull (p z) hasyp
    let γ := PathConnectedSpace.somePath a b
    let δ : C(unitInterval, M) := ⟨fun t ↦ j (γ t), hj.comp γ.continuous⟩
    obtain ⟨η, he, hzero⟩ := hp.exists_path_lifts δ y (by simpa [δ] using ha)
    let z' := η 1
    let η' : Path y z' := { toContinuousMap := η, source' := hzero, target' := rfl }
    have hlift : ∀ t, p (η' t) = j (γ t) := fun t ↦ congrFun he t
    have hz'mem : z' ∈ liftedIntrinsicLeafRange p j a y := ⟨b, γ, η', hlift⟩
    have hsz' := hfwd z' hz'mem
    have hpz : p z' = p z := by simpa [z', δ, hb] using congrFun he (1 : unitInterval)
    have hg : H z' - H z ∈ Γ := QuotientAddGroup.eq_iff_sub_mem.mp (by
      exact (hH z').trans ((congrArg h hpz).trans (hH z).symm))
    have hsz : H z - H y ∈ S := hdec
    have hs : H z' - H z ∈ S := by
      convert S.sub_mem hsz' hsz using 1; abel_nf
    have hz'eq : z' = z := H.injective (sub_eq_zero.mp
      (lattice_decay_zero Γ A hΓ (H z' - H z) hg hs))
    change z ∈ liftedIntrinsicLeafRange p j a y
    rw [← hz'eq]
    exact hz'mem
  have heq : H '' liftedIntrinsicLeafRange p j a y = (fun v ↦ H y + v) '' (S : Set V) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨H z - H y, hfwd z hz, by abel⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨H.symm (H y + v), hback v hv, H.apply_symm_apply _⟩
  refine ⟨heq, ?_⟩
  exact ⟨fun z hz ↦ heq ▸ Set.mem_image_of_mem H hz, H.injective.injOn,
    fun w hw ↦ by rw [← heq] at hw; exact hw⟩

end
end HolomorphicAnosov
