import HolomorphicAnosov.Geometry.AdaptedNativeProductRealBoxes
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.StablePlaqueUniformTail
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphZpowNegCoe

/-! Original receiving product plaques retain their literal orbit-core bounds.
These adapters use the existing native product and its given bracket, rather
than constructing a second lamination or requiring a conjugacy. -/
namespace HolomorphicAnosov.FranksOriginalCover
open scoped ContDiff Manifold _root_.Topology
open Ghys

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Two nearby points on a raw product row lie in one another's closed stable
orbit core. Source: the receiving-core property of the native product in
Shub, Proposition 10.10, followed by the orbit-core recentering identity.
Both points are in the core of the same unstable central coordinate. Their
orbit distance is at most twice the core radius, strictly inside the wider
plaque; their initial distance then invokes the exact closed-core equation. -/
theorem native_product_row_core
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (Ds Du : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ,E) x))
    (m : MetricSpace M) {β γ ε : ℝ}
    (S : NativeInvariantLeafSystem 𝓘(ℝ,E) Ds f)
    (U : NativeInvariantLeafSystem 𝓘(ℝ,E) Du f.symm)
    (PS : AdaptedNativeOrbitPlaques 𝓘(ℝ,E) f Ds m β γ S)
    (hβ : 2 * γ < β)
    (bracket : adaptedClosePairDomain (M := M) m ε → M)
    (hbracket : ∀ p : adaptedClosePairDomain (M := M) m ε,
      adaptedClosedOrbitCore 𝓘(ℝ,E) f m γ p.1.1 ∩
        adaptedClosedOrbitCore 𝓘(ℝ,E) f.symm m γ p.1.2 = {bracket p})
    (x : M) (P : AdaptedNativeProduct 𝓘(ℝ,E) f Ds Du m γ ε S U bracket x)
    (s s' : P.stableDomain) (u : P.unstableDomain)
    (hd : m.dist (P.product (s',u)).val (P.product (s,u)).val ≤ γ) :
    (P.product (s',u)).val ∈
      adaptedClosedOrbitCore 𝓘(ℝ,E) f m γ (P.product (s,u)).val := by
  have hc (t : P.stableDomain) : (P.product (t,u)).val ∈
      adaptedClosedOrbitCore 𝓘(ℝ,E) f m γ ((U.leaf x).inclusion u.val) := by
    have hh : (P.product (t,u)).val ∈
        adaptedClosedOrbitCore 𝓘(ℝ,E) f m γ ((U.leaf x).inclusion u.val) ∩
          adaptedClosedOrbitCore 𝓘(ℝ,E) f.symm m γ ((S.leaf x).inclusion t.val) := by
      rw [hbracket ⟨(_, _), P.caller t u⟩]
      exact Set.mem_singleton_iff.mpr (P.product_eq t u)
    exact hh.1
  exact orbitCore_recenter f Ds m S PS hβ (hc s') (hc s) hd

/-- The inverse-time counterpart for two points of one original product column. -/
theorem native_product_column_core
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (Ds Du : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ,E) x))
    (m : MetricSpace M) {β γ ε : ℝ}
    (S : NativeInvariantLeafSystem 𝓘(ℝ,E) Ds f)
    (U : NativeInvariantLeafSystem 𝓘(ℝ,E) Du f.symm)
    (PU : AdaptedNativeOrbitPlaques 𝓘(ℝ,E) f.symm Du m β γ U)
    (hβ : 2 * γ < β)
    (bracket : adaptedClosePairDomain (M := M) m ε → M)
    (hbracket : ∀ p : adaptedClosePairDomain (M := M) m ε,
      adaptedClosedOrbitCore 𝓘(ℝ,E) f m γ p.1.1 ∩
        adaptedClosedOrbitCore 𝓘(ℝ,E) f.symm m γ p.1.2 = {bracket p})
    (x : M) (P : AdaptedNativeProduct 𝓘(ℝ,E) f Ds Du m γ ε S U bracket x)
    (s : P.stableDomain) (u u' : P.unstableDomain)
    (hd : m.dist (P.product (s,u')).val (P.product (s,u)).val ≤ γ) :
    (P.product (s,u')).val ∈
      adaptedClosedOrbitCore 𝓘(ℝ,E) f.symm m γ (P.product (s,u)).val := by
  exact orbitCore_recenter f.symm Du m U PU hβ
    (adaptedProduct_mem_unstable f Ds Du m S U bracket hbracket x P s u')
    (adaptedProduct_mem_unstable f Ds Du m S U bracket hbracket x P s u) hd

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Literal native closed stable cores have a uniform forward tail.
The diagonal bracket identity proves expansivity at the same core radius.
The compact finite-window theorem then shifts its finite window into positive
time. This uses no exponential estimate and no intrinsic distance. -/
theorem native_core_uniform_tail [CompactSpace M]
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (m : MetricSpace M) {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
    (htop : m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M))
    (bracket : adaptedClosePairDomain (M := M) m ε → M)
    (hbracket : ∀ p : adaptedClosePairDomain (M := M) m ε,
      adaptedClosedOrbitCore 𝓘(ℝ,E) f m γ p.1.1 ∩
        adaptedClosedOrbitCore 𝓘(ℝ,E) f.symm m γ p.1.2 = {bracket p})
    (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∀ x y : M, y ∈ adaptedClosedOrbitCore 𝓘(ℝ,E) f m γ x →
      ∀ n : ℕ, N ≤ n → m.dist ((f : M → M)^[n] x) ((f : M → M)^[n] y) < r := by
  let : MetricSpace M := m.replaceTopology htop.symm
  have hexp : ∀ x y : M,
      (∀ j : ℤ, dist ((f.toHomeomorph ^ j) x) ((f.toHomeomorph ^ j) y) ≤ γ) → x = y := by
    intro x y hxy
    apply (orbitCore_diagonal_unique f m hγ hε bracket hbracket ?_ ?_).symm
    · intro n
      simpa only [zpow_natCast,
        Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe,
        Diffeomorph.coe_toHomeomorph, m.dist_comm] using hxy (n : ℤ)
    · intro n
      simpa only [Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_zpow_neg_coe,
        Diffeomorph.coe_toHomeomorph_symm, m.dist_comm] using hxy (-(n : ℤ))
  obtain ⟨N,hN⟩ :=
    Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.stable_plaque_uniform_tail
      f.toHomeomorph hexp hr
  refine ⟨N, fun x y hxy n hn ↦ ?_⟩
  have hh : ∀ k : ℕ, dist ((f.toHomeomorph ^ (k : ℤ)) x)
      ((f.toHomeomorph ^ (k : ℤ)) y) ≤ γ := by
    intro k
    simpa only [zpow_natCast,
      Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe,
      Diffeomorph.coe_toHomeomorph, m.dist_comm] using hxy k
  simpa only [zpow_natCast,
    Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe,
    Diffeomorph.coe_toHomeomorph] using hN x y hh n hn

end HolomorphicAnosov.FranksOriginalCover
