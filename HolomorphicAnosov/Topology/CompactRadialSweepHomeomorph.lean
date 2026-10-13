import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval

open Set
namespace HolomorphicAnosov

/-- A homeomorphism between compact fronts extends by the same radial parameter to
an explicit homeomorphism of their closed radial sweeps. Neither front contains its
center, and nonzero radial coordinates are unique on both sides.

Agent-written implementation of the radial extension step omitted in Cairns,
An Elementary Proof of the Jordan-Schoenflies Theorem (1951), §4 equations(4.1)–(4.2),
pp.863–864, and parent `topo.cairns_convex_star_sector_extension_g10`, step5.
The quotient-map proof here is not attributed to the source's polar/norm argument.
On the compact parameter space L×[0,1], the two radial maps have exactly the same
fibres: all pairs of zero radius agree, and every nonzero-radius fibre is a singleton.
The center-exclusion hypotheses ensure that zero and nonzero fibres cannot meet.
Both maps onto their image subspaces are continuous surjections from a compact space
to a Hausdorff space, hence quotient maps. Descend each along the other; their defining
triangles make the descents inverse continuous maps. The forward triangle is exactly
the asserted radial formula. This includes continuity at the center without deleting
it. Empty fronts yield the homeomorphism between empty sweeps. No smoothness, convexity,
finite dimension, or angular order is assumed. DAG node:
`topo.compact_radial_sweep_homeomorph_g19`. -/
theorem compact_radial_sweep_homeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Set E) (T : Set F) (hL : IsCompact L) (M : E) (N : F)
    (hM : ∀ Q ∈ L, Q ≠ M) (hN : ∀ Q ∈ T, Q ≠ N)
    (h : L ≃ₜ T)
    (hLs : ∀ (Q R : L) (t u : unitInterval), t ≠ 0 →
      (1 - (t : ℝ)) • M + (t : ℝ) • (Q : E) =
        (1 - (u : ℝ)) • M + (u : ℝ) • (R : E) → Q = R ∧ t = u)
    (hTs : ∀ (Q R : T) (t u : unitInterval), t ≠ 0 →
      (1 - (t : ℝ)) • N + (t : ℝ) • (Q : F) =
        (1 - (u : ℝ)) • N + (u : ℝ) • (R : F) → Q = R ∧ t = u) :
    let S := range (fun w : L × unitInterval ↦
      (1 - (w.2 : ℝ)) • M + (w.2 : ℝ) • (w.1 : E))
    let U := range (fun w : T × unitInterval ↦
      (1 - (w.2 : ℝ)) • N + (w.2 : ℝ) • (w.1 : F))
    ∃ H : S ≃ₜ U, ∀ (Q : L) (t : unitInterval),
      (H ⟨(1 - (t : ℝ)) • M + (t : ℝ) • (Q : E), ⟨(Q, t), rfl⟩⟩ : F) =
        (1 - (t : ℝ)) • N + (t : ℝ) • (h Q : F) := by
  intro S U
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let f : C(L × unitInterval, S) :=
    ⟨fun w ↦ ⟨(1 - (w.2 : ℝ)) • M + (w.2 : ℝ) • (w.1 : E), ⟨w, rfl⟩⟩,
      by continuity⟩
  let g : C(L × unitInterval, U) :=
    ⟨fun w ↦ ⟨(1 - (w.2 : ℝ)) • N + (w.2 : ℝ) • (h w.1 : F), ⟨(h w.1,w.2), rfl⟩⟩,
      by fun_prop⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, w, rfl⟩
    exact ⟨w, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨z, ⟨Q,t⟩, rfl⟩
    refine ⟨(h.symm Q,t), ?_⟩
    apply Subtype.ext
    simp [g]
  have hzeroM (Q : L) (t : unitInterval) :
      (1 - (t : ℝ)) • M + (t : ℝ) • (Q : E) = M ↔ t = 0 := by
    have he : (1 - (t : ℝ)) • M + (t : ℝ) • (Q : E) - M =
        (t : ℝ) • ((Q : E) - M) := by module
    rw [← sub_eq_zero, he, smul_eq_zero]
    simp only [sub_eq_zero, hM _ Q.property, or_false]
    exact Iff.symm (Subtype.ext_iff (a1 := t) (a2 := (0 : unitInterval)))
  have hzeroN (Q : T) (t : unitInterval) :
      (1 - (t : ℝ)) • N + (t : ℝ) • (Q : F) = N ↔ t = 0 := by
    have he : (1 - (t : ℝ)) • N + (t : ℝ) • (Q : F) - N =
        (t : ℝ) • ((Q : F) - N) := by module
    rw [← sub_eq_zero, he, smul_eq_zero]
    simp only [sub_eq_zero, hN _ Q.property, or_false]
    exact Iff.symm (Subtype.ext_iff (a1 := t) (a2 := (0 : unitInterval)))
  have hfg : Function.FactorsThrough g f := by
    intro x y he
    have he' := congrArg Subtype.val he
    change (1 - (x.2 : ℝ)) • M + (x.2 : ℝ) • (x.1 : E) =
      (1 - (y.2 : ℝ)) • M + (y.2 : ℝ) • (y.1 : E) at he'
    by_cases hx : x.2 = 0
    · have hy : y.2 = 0 := (hzeroM y.1 y.2).mp
        (by simpa [hx] using he'.symm)
      apply Subtype.ext
      simp [g, hx, hy]
    · obtain ⟨hQ,ht⟩ := hLs x.1 y.1 x.2 y.2 hx he'
      exact congrArg g (Prod.ext hQ ht)
  have hgf : Function.FactorsThrough f g := by
    intro x y he
    have he' := congrArg Subtype.val he
    change (1 - (x.2 : ℝ)) • N + (x.2 : ℝ) • (h x.1 : F) =
      (1 - (y.2 : ℝ)) • N + (y.2 : ℝ) • (h y.1 : F) at he'
    by_cases hx : x.2 = 0
    · have hy : y.2 = 0 := (hzeroN (h y.1) y.2).mp
        (by simpa [hx] using he'.symm)
      apply Subtype.ext
      simp [f, hx, hy]
    · obtain ⟨hQ,ht⟩ := hTs (h x.1) (h y.1) x.2 y.2 hx he'
      exact congrArg f (Prod.ext (h.injective hQ) ht)
  have hfq : Topology.IsQuotientMap f := f.continuous.isClosedMap.isQuotientMap f.continuous hf
  have hgq : Topology.IsQuotientMap g := g.continuous.isClosedMap.isQuotientMap g.continuous hg
  let H := hfq.lift g hfg
  let G := hgq.lift f hgf
  have hH (w : L × unitInterval) : H (f w) = g w :=
    congrArg (fun k : C(L × unitInterval,U) ↦ k w) (hfq.lift_comp g hfg)
  have hG (w : L × unitInterval) : G (g w) = f w :=
    congrArg (fun k : C(L × unitInterval,S) ↦ k w) (hgq.lift_comp f hgf)
  refine ⟨{ toFun := H
            invFun := G
            continuous_toFun := H.continuous
            continuous_invFun := G.continuous
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · intro x
    obtain ⟨w,rfl⟩ := hf x
    rw [hH,hG]
  · intro y
    obtain ⟨w,rfl⟩ := hg y
    rw [hG,hH]
  · intro Q t
    exact congrArg Subtype.val (hH (Q,t))

end HolomorphicAnosov
