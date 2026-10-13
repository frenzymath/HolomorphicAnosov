import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]

/--
Reverse the explicit native leaf lift along the genuine inverse diffeomorphism.

Source: Hirsch--Pugh--Shub, *Invariant Manifolds* (1977), §6B pp.111--114
and §7 pp.127--129.  Given a native invariant leaf system for `g`, write
`p = g q`, use the inverse of the supplied transport map at `q`, and verify the
ambient inclusion equation by injectivity of `g`.  The leaf and rebase data are
reused unchanged.  This is the reusable inverse-reindexing step from the
adapted orbit-plaque construction.
-/
noncomputable def nativeInvariantLeafSystemInverse
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (T : NativeInvariantLeafSystem 𝓘(ℝ, E) D g) :
    NativeInvariantLeafSystem 𝓘(ℝ, E) D g.symm := by
  have hadvance (p : M) : ∃ a : Diffeomorph 𝓘(ℝ, Fin (T.leaf p).rank → ℝ)
      𝓘(ℝ, Fin (T.leaf (g.symm p)).rank → ℝ) (T.leaf p).Carrier
      (T.leaf (g.symm p)).Carrier ∞,
      ∀ y, (T.leaf (g.symm p)).inclusion (a y) =
        g.symm ((T.leaf p).inclusion y) := by
    obtain ⟨q, rfl⟩ := g.surjective p
    change ∃ a : Diffeomorph 𝓘(ℝ, Fin (T.leaf (g q)).rank → ℝ)
        𝓘(ℝ, Fin (T.leaf (g.symm (g q))).rank → ℝ) (T.leaf (g q)).Carrier
        (T.leaf (g.symm (g q))).Carrier ∞,
      ∀ y, (T.leaf (g.symm (g q))).inclusion (a y) =
        g.symm ((T.leaf (g q)).inclusion y)
    rw [g.symm_apply_apply]
    refine ⟨(T.advance q).symm, ?_⟩
    intro y
    apply g.injective
    simp only [Diffeomorph.coe_toEquiv, g.apply_symm_apply]
    simpa using (T.inclusion_advance q ((T.advance q).symm y)).symm
  choose advance inclusion_advance using hadvance
  exact { leaf := T.leaf
          advance := advance
          inclusion_advance := inclusion_advance
          rebase := T.rebase
          inclusion_rebase := T.inclusion_rebase }

theorem nativeInvariantLeafSystem_inverse_reindex
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (T : NativeInvariantLeafSystem 𝓘(ℝ, E) D g) :
    Nonempty (NativeInvariantLeafSystem 𝓘(ℝ, E) D g.symm) :=
  ⟨nativeInvariantLeafSystemInverse D g T⟩




end HolomorphicAnosov
