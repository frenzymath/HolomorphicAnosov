import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology _root_.Topology
open Filter Set

namespace HolomorphicAnosov

noncomputable section

/-- Agent quotient-capture argument: an orbit converging to zero modulo a discrete invariant
subgroup differs by a single subgroup element from an orbit converging to zero in V. -/
theorem lattice_capture
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (A : V ≃L[ℝ] V) (hΓ : A '' (Γ : Set V) = (Γ : Set V))
    (v : V)
    (hv : Tendsto (fun n : ℕ ↦ (QuotientAddGroup.mk ((A : V → V)^[n] v) :
      V ⧸ Γ.toAddSubgroup)) atTop (𝓝 0)) :
    ∃ g : Γ, Tendsto (fun n : ℕ ↦ (A : V → V)^[n] (v - g)) atTop (𝓝 0) := by
  classical
  let : IsClosed (Γ.toAddSubgroup : Set V) := AddSubgroup.isClosed_of_discreteTopology
  let u : ℕ → V := fun n ↦ (A : V → V)^[n] v
  have herr : ∀ n : ℕ, ∃ r : V,
      (QuotientAddGroup.mk r : V ⧸ Γ.toAddSubgroup) = QuotientAddGroup.mk (u n) ∧
      ‖r‖ < ‖(QuotientAddGroup.mk (u n) : V ⧸ Γ.toAddSubgroup)‖ + 1 / ((n : ℝ) + 1) :=
    fun n ↦ QuotientAddGroup.exists_norm_mk_lt _ (by positivity)
  choose r hr hnorm using herr
  have hrzero : Tendsto r atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ le_of_lt (hnorm n))
    simpa [u] using
      (hv.norm.add (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0)))
  have hmem : ∀ n, u n - r n ∈ Γ := fun n ↦
    QuotientAddGroup.eq_iff_sub_mem.mp (hr n).symm
  have hAmem : ∀ w ∈ Γ, A w ∈ Γ := by
    intro w hw
    change A w ∈ (Γ : Set V)
    rw [← hΓ]
    exact ⟨w, hw, rfl⟩
  have hrecMem : ∀ n, r (n + 1) - A (r n) ∈ Γ := by
    intro n
    have h := Γ.sub_mem (hAmem _ (hmem n)) (hmem (n + 1))
    have hu : u (n + 1) = A (u n) := Function.iterate_succ_apply' _ _ _
    rw [hu, map_sub] at h
    convert h using 1; abel_nf
  let d : ℕ → Γ := fun n ↦ ⟨r (n + 1) - A (r n), hrecMem n⟩
  have hdzero : Tendsto d atTop (𝓝 (0 : Γ)) := by
    apply tendsto_subtype_rng.mpr
    simpa [d] using (hrzero.comp (tendsto_add_atTop_nat 1)).sub
      (A.continuous.tendsto 0 |>.comp hrzero)
  have hevent : ∀ᶠ n in atTop, d n = 0 := by
    apply tendsto_pure.mp
    simpa only [nhds_discrete] using hdzero
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hrec : ∀ n ≥ N, r (n + 1) = A (r n) := by
    intro n hn
    have h := congrArg Subtype.val (hN n hn)
    exact sub_eq_zero.mp h
  have hiter : ∀ k : ℕ, (A : V → V)^[k] (r N) = r (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      exact (hrec (N + k) (Nat.le_add_right N k)).symm
  let gval := (A.symm.toLinearEquiv ^ N) (u N - r N)
  have hInvmem : ∀ w ∈ Γ, A.symm w ∈ Γ := by
    intro w hw
    have hw : w ∈ A '' (Γ : Set V) := hΓ.symm ▸ hw
    rcases hw with ⟨z, hz, he⟩
    change A.symm w ∈ (Γ : Set V)
    simpa only [← he, A.symm_apply_apply] using hz
  have hgmem : gval ∈ Γ := by
    dsimp [gval]
    rw [LinearEquiv.pow_apply]
    have hi : ∀ k : ℕ, (A.symm : V → V)^[k] (u N - r N) ∈ Γ := by
      intro k
      induction k with
      | zero => exact hmem N
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hInvmem _ ih
    exact hi N
  refine ⟨⟨gval, hgmem⟩, ?_⟩
  let e : V ≃ₗ[ℝ] V := A.toLinearEquiv
  have hforward : ∀ k : ℕ, (A : V → V)^[k] = ⇑(e ^ k) := by
    intro k
    exact (LinearEquiv.coe_pow e k).symm
  have hbackward : ∀ k : ℕ, (A.symm : V → V)^[k] = ⇑(e⁻¹ ^ k) := by
    intro k
    exact (LinearEquiv.coe_pow e⁻¹ k).symm
  have hg : v - gval = (e⁻¹ ^ N) (r N) := by
    change v - (e⁻¹ ^ N) (u N - r N) = _
    rw [map_sub]
    have hcancel : (e⁻¹ ^ N) (u N) = v := by
      dsimp [u]
      rw [hforward]
      rw [inv_pow]
      exact (e ^ N).symm_apply_apply v
    rw [hcancel]
    abel
  have hcomm : ∀ k : ℕ, (A : V → V)^[k] ((e⁻¹ ^ N) (r N)) =
      (e⁻¹ ^ N) ((A : V → V)^[k] (r N)) := by
    intro k
    rw [hforward]
    change ((e ^ k) * (e⁻¹ ^ N)) (r N) = ((e⁻¹ ^ N) * (e ^ k)) (r N)
    rw [(Commute.refl e).inv_right.pow_pow k N |>.eq]
  have hc : Continuous ⇑(e⁻¹ ^ N) := by
    rw [← hbackward]
    exact A.symm.continuous.iterate N
  have hz : (e⁻¹ ^ N) (0 : V) = 0 := map_zero _
  have hlim := hc.tendsto 0 |>.comp (hrzero.comp (tendsto_add_atTop_nat N))
  have hi : ∀ n, (A : V → V)^[n] (v - gval) = (e⁻¹ ^ N) (r (n + N)) := by
    intro n
    rw [hg, hcomm, hiter, Nat.add_comm]
  change Tendsto (fun n ↦ (e⁻¹ ^ N) (r (n + N))) atTop (𝓝 ((e⁻¹ ^ N) 0)) at hlim
  rw [hz] at hlim
  convert hlim using 1
  funext n
  exact hi n


end
end HolomorphicAnosov
