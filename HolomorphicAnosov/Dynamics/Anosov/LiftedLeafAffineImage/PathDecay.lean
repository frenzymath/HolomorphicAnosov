import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.LatticeCapture
import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.AsymptoticQuotientIff
import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.FullDecaySubmodule
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Path

open scoped Topology _root_.Topology
open Filter Set
universe u
namespace HolomorphicAnosov
noncomputable section

/-- A lifted intrinsic path has constant class modulo the full decay submodule, because its class
image lies in the countable projected lattice. -/
theorem path_decay
    {V M Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MetricSpace M] [CompactSpace M] [TopologicalSpace Y]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (A : V ≃L[ℝ] V) (hΓ : A '' (Γ : Set V) = (Γ : Set V))
    (f : M ≃ₜ M) (h : M ≃ₜ V ⧸ Γ.toAddSubgroup)
    (hc : ∀ x v, (QuotientAddGroup.mk v : V ⧸ Γ.toAddSubgroup) = h x →
      h (f x) = (QuotientAddGroup.mk (A v) : V ⧸ Γ.toAddSubgroup))
    (p : Y → M) (H : Y ≃ₜ V)
    (hH : ∀ y, (QuotientAddGroup.mk (H y) : V ⧸ Γ.toAddSubgroup) = h (p y))
    (y z : Y) (η : Path y z) (hη : ∀ t, ForwardAsymptotic f (p y) (p (η t))) :
    H z - H y ∈ fullDecaySubmodule A := by
  classical
  let S := fullDecaySubmodule A
  let : IsClosed (S : Set V) := S.closed_of_finiteDimensional
  let k : unitInterval → V ⧸ S := fun t ↦ S.mkQ (H (η t) - H y)
  have hk : Continuous k :=
    S.continuous_mkQ.comp ((H.continuous.comp η.continuous).sub continuous_const)
  have hcount : (Set.range (fun g : Γ ↦ S.mkQ (g : V))).Countable := Set.countable_range _
  have hrange : Set.range k ⊆ Set.range (fun g : Γ ↦ S.mkQ (g : V)) := by
    rintro _ ⟨t, rfl⟩
    have hq := (asymptotic_quotient_iff Γ A f h hc (p y) (p (η t))
      (H y) (H (η t)) (hH y) (hH (η t))).mp (hη t)
    obtain ⟨g, hg⟩ := lattice_capture Γ A hΓ (H (η t) - H y) hq
    refine ⟨g, ?_⟩
    have hm : H (η t) - H y - (g : V) ∈ S := hg
    have hz : S.mkQ (H (η t) - H y - (g : V)) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hm
    exact sub_eq_zero.mp (by simpa only [k, map_sub] using hz) |>.symm
  have hs : (Set.range k).Subsingleton := hcount.isTotallyDisconnected _ hrange
    (isPreconnected_range hk)
  have he := hs (Set.mem_range_self (0 : unitInterval)) (Set.mem_range_self (1 : unitInterval))
  have hz : S.mkQ (H z - H y) = 0 := by
    simpa [k] using he.symm
  exact (Submodule.Quotient.mk_eq_zero S).mp hz

end
end HolomorphicAnosov
