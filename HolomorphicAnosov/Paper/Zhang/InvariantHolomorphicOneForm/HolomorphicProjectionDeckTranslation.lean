import HolomorphicAnosov.Paper.Zhang.FixedPointFreeEntireTranslation
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.StableProjectionDeckPreservesFibres
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NonzeroDeckFactorFixedPointFree

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- A deck transformation preserving the fibres of a holomorphic projection acts on that projection
by a scalar translation, given a holomorphic section and the discrete inverse-orbit hypotheses.
(Zhang, Lemma 4.2) -/
theorem holomorphic_projection_deck_translation
    {d : ℕ} {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel d) Y] [IsManifold (complexModel d) ∞ Y]
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    (U : Submodule ℝ V) (Z : Set V) (T : V → V)
    (hTi : Function.Injective T) (hZd : IsDiscrete Z)
    (hTZ : Set.MapsTo T Z Z) (hzero : (0 : V) ∈ Z) (hTzero : T 0 = 0)
    (H : Y → V) (q : Y → ℂ) (i : ℂ → Y)
    (hq : ContMDiff (complexModel d) 𝓘(ℂ, ℂ) ∞ q)
    (hiHol : ContMDiff 𝓘(ℂ, ℂ) (complexModel d) ∞ i)
    (hi : ∀ z, q (i z) = z)
    (hfibre : ∀ y z, q y = q z ↔ H y - H z ∈ U)
    (D : Biholomorph d d Y Y) (gamma : V) (hgamma : gamma ∈ Z)
    (hgamma0 : gamma ≠ 0)
    (hdecay : gamma ∈ U → Filter.Tendsto (fun n : ℕ ↦ T^[n] gamma)
      Filter.atTop (𝓝 0))
    (hD : ∀ y, H (D y) = H y + gamma)
    (hDi : ∀ y, H (D.symm y) = H y - gamma) :
    ∃ c : ℂ, ∀ y, q (D y) = q y + c := by
  have hpres := stable_projection_deck_preserves_fibres U H q hfibre D gamma hD
  have hpresi := stable_projection_deck_preserves_fibres U H q hfibre D.symm
    (-gamma) (fun y ↦ by simpa only [sub_eq_add_neg] using hDi y)
  let G : ℂ → ℂ := fun z ↦ q (D (i z))
  let J : ℂ → ℂ := fun z ↦ q (D.symm (i z))
  have hG : ∀ y, G (q y) = q (D y) :=
    fun y ↦ hpres (i (q y)) y (hi (q y))
  have hJ : ∀ y, J (q y) = q (D.symm y) :=
    fun y ↦ hpresi (i (q y)) y (hi (q y))
  have hJG : ∀ z, J (G z) = z := by
    intro z
    change J (q (D (i z))) = z
    rw [hJ, D.symm_apply_apply, hi]
  have hGJ : ∀ z, G (J z) = z := by
    intro z
    change G (q (D.symm (i z))) = z
    rw [hG, D.apply_symm_apply, hi]
  have hg : Differentiable ℂ G := by
    apply mdifferentiable_iff_differentiable.mp
    exact (hq.comp (D.contMDiff_toFun.comp hiHol)).mdifferentiable (by simp)
  have hj : Differentiable ℂ J := by
    apply mdifferentiable_iff_differentiable.mp
    exact (hq.comp (D.contMDiff_invFun.comp hiHol)).mdifferentiable (by simp)
  have hfree := nonzero_deck_factor_fixed_point_free U Z T hTi hZd hTZ hzero hTzero
    H q (fun z ↦ ⟨i z, hi z⟩) hfibre gamma hgamma hgamma0 hdecay D hD G
    (fun y ↦ (hG y).symm)
  obtain ⟨c, hc⟩ := fixed_point_free_entire_translation G J hg hj hJG hGJ hfree
  exact ⟨c, fun y ↦ (hG y).symm.trans (hc (q y))⟩


end HolomorphicAnosov.Paper.Zhang
