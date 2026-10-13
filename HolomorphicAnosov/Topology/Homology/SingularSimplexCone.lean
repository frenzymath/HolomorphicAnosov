import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real

/-!
# The apex cone of a singular simplex into a simplex or product

Bredon, *Topology and Geometry* (1993), IV Theorem 15.5, pp.219–220,
constructs the cone of a singular simplex using a contraction to a base point.
Here the contraction is straight-line interpolation inside a standard closed
real simplex, or coordinatewise inside a product of two such simplices.
The source prints the formula; the normalized-coordinate validity and full
apex continuity calculations below are agent-expanded well-definedness steps
for these bounded models, rather than a claim about arbitrary contractions.
The function data are explicit, including the apex. Their well-definedness
and continuity certificates are proved below; there is no chain-contraction theorem
in this definition module.
-/

open scoped Topology _root_.Topology

noncomputable section

namespace HolomorphicAnosov
namespace SingularConvexCone

/-- Bredon's standard closed real simplex, in its native weights topology. -/
abbrev Simplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

/-- The models used by the acyclic-models cone argument in Bredon IV15.5/VI1.1. -/
inductive Model where
  | simplex (r : ℕ)
  | product (r s : ℕ)

/-- The actual simplex or product space, with the native topology, not a proxy. -/
def Model.space (M : Model) : TopCat := match M with
  | .simplex r => TopCat.of (Simplex r)
  | .product r s => TopCat.of (Simplex r × Simplex s)

/-- Validity of the normalized remaining coordinates in Bredon's cone formula.

Source: Bredon IV15.5, p.219, with the finite coordinate check expanded here.
Proof: each remaining weight is nonnegative and the positive denominator
is `1-t₀`. Splitting the sum of all weights into its zeroth and successor
coordinates gives sum of remaining weights `1-t₀`. Division by that nonzero
denominator gives total one. `Finsupp.equivFunOnFinite` preserves the weights
and the finite sum, so the same calculation proves the two structure fields.
This includes n=0 and does not require positive model dimension. -/
theorem normalizedRest_valid {n : ℕ} (t : Simplex (n + 1))
    (h : t.weights 0 < 1) :
    (0 ≤ Finsupp.equivFunOnFinite.symm
      (fun i : Fin (n + 1) => t.weights i.succ / (1 - t.weights 0))) ∧
    (Finsupp.equivFunOnFinite.symm
      (fun i : Fin (n + 1) => t.weights i.succ / (1 - t.weights 0))).sum
      (fun _ x => x) = 1 := by
  have hden : 0 < 1 - t.weights 0 := sub_pos.mpr h
  constructor
  · intro i
    exact div_nonneg (t.weights_nonneg i.succ) hden.le
  · rw [Finsupp.sum_fintype]
    · change (∑ i : Fin (n + 1), t.weights i.succ / (1 - t.weights 0)) = 1
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [← div_eq_mul_inv]
      apply (div_eq_one_iff_eq hden.ne').mpr
      have ht := t.total
      rw [Finsupp.sum_fintype] at ht
      · rw [Fin.sum_univ_succ] at ht
        linarith
      · intro i
        rfl
    · intro i
      rfl

/-- The literal normalized remainder of Bredon's cone weights. -/
def normalizedRest {n : ℕ} (t : Simplex (n + 1)) (h : t.weights 0 < 1) :
    Simplex n where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i : Fin (n + 1) => t.weights i.succ / (1 - t.weights 0))
  nonneg := (normalizedRest_valid t h).1
  total := (normalizedRest_valid t h).2

/-- Bredon's simplex-valued cone, with its explicit apex clause. The native
convex combination has weights `t₀ o+(1-t₀)σ(normalizedRest t)`. -/
def simplexConeRaw {n r : ℕ} (o : Simplex r) (σ : C(Simplex n, Simplex r))
    (t : Simplex (n + 1)) : Simplex r :=
  if h : t.weights 0 < 1 then
    Convexity.convexCombPair (t.weights 0) (1 - t.weights 0)
      (t.weights_nonneg 0) (sub_nonneg.mpr (t.weights_apply_le_one 0))
      (add_sub_cancel _ _) o (σ (normalizedRest t h))
  else o

/-- Literal product cone: both factors use the same normalized input weights. -/
def productConeRaw {n r s : ℕ} (o : Simplex r × Simplex s)
    (σ : C(Simplex n, Simplex r × Simplex s)) (t : Simplex (n + 1)) :
    Simplex r × Simplex s :=
  (simplexConeRaw o.1 (ContinuousMap.fst.comp σ) t,
    simplexConeRaw o.2 (ContinuousMap.snd.comp σ) t)

/-- Bredon's explicit cone on either actual model. -/
def coneRaw (M : Model) {n : ℕ} (o : M.space) (σ : C(Simplex n, M.space)) :
    Simplex (n + 1) → M.space :=
  match M with
  | .simplex _ => simplexConeRaw o σ
  | .product _ _ => productConeRaw o σ

/-- Continuity of the explicit cone, including the full apex neighbourhood.

Source: Bredon IV15.5 pp.219–220. The source's general contractible-space
argument is specialized to the bounded simplex models. Proof: the weights
embedding identifies the native simplex topology with its finite-coordinate
topology. Off `t₀=1`, division by positive `1-t₀` makes normalizedRest
continuous; composing σ and taking the displayed convex combination is
continuous in every output coordinate. At the apex, both σ's output and o
have every weight in [0,1]. Thus each output-coordinate difference from o
has absolute value at most `1-t₀`, including at the apex itself. The latter
continuous nonnegative function tends to zero. Squeeze on the full apex
neighbourhood filter gives convergence to o in each coordinate. The weights
embedding reflects this continuity. Pair the two coordinatewise proofs for
the product model. No punctured-only limit, compactness of an open simplex,
normalization of chains, or positive-dimensional assumption is used. -/
theorem coneRaw_continuous (M : Model) {n : ℕ} (o : M.space)
    (σ : C(Simplex n, M.space)) : Continuous (coneRaw M o σ) := by
  have hs {n r : ℕ} (o : Simplex r) (σ : C(Simplex n, Simplex r)) :
      Continuous (simplexConeRaw o σ) := by
    let U : Set (Simplex (n + 1)) := {t | t.weights 0 < 1}
    have hw (i : Fin (n + 2)) : Continuous (fun t : Simplex (n + 1) ↦ t.weights i) :=
      Convexity.StdSimplex.continuous_weights_apply ℝ i
    have hU : IsOpen U := isOpen_lt (hw 0) continuous_const
    have hr : Continuous (fun t : U ↦ normalizedRest t.val t.property) := by
      rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
      apply continuous_pi
      intro i
      change Continuous (fun t : U ↦ t.val.weights i.succ / (1 - t.val.weights 0))
      exact ((hw i.succ).comp continuous_subtype_val).div
        (continuous_const.sub ((hw 0).comp continuous_subtype_val))
        (fun t ↦ (sub_pos.mpr t.property).ne')
    have ha : ContinuousOn (simplexConeRaw o σ) U := by
      rw [continuousOn_iff_continuous_domRestrict,
        (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (r + 1))).continuous_iff]
      apply continuous_pi
      intro j
      change Continuous (fun t : U ↦ (simplexConeRaw o σ t.val).weights j)
      have heq : (fun t : U ↦ (simplexConeRaw o σ t.val).weights j) =
          (fun t : U ↦ t.val.weights 0 * o.weights j +
            (1 - t.val.weights 0) * (σ (normalizedRest t.val t.property)).weights j) := by
        funext t
        have ht : t.val.weights 0 < 1 := t.property
        simp [simplexConeRaw, ht, Convexity.StdSimplex.weights_convexCombPair]
      rw [heq]
      exact (((hw 0).comp continuous_subtype_val).mul continuous_const).add
        ((continuous_const.sub ((hw 0).comp continuous_subtype_val)).mul
          ((Convexity.StdSimplex.continuous_weights_apply ℝ j).comp (σ.continuous.comp hr)))
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (r + 1))).continuous_iff]
    apply continuous_pi
    intro j
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases ht : t.weights 0 < 1
    · exact (Convexity.StdSimplex.continuous_weights_apply ℝ j).continuousAt.comp
        (ha.continuousAt (hU.mem_nhds ht))
    · have ht1 : t.weights 0 = 1 := le_antisymm (t.weights_apply_le_one 0) (not_lt.mp ht)
      have hbound (s : Simplex (n + 1)) :
          ‖(simplexConeRaw o σ s).weights j - o.weights j‖ ≤ 1 - s.weights 0 := by
        by_cases hs : s.weights 0 < 1
        · have hnon : 0 ≤ 1 - s.weights 0 := sub_nonneg.mpr (s.weights_apply_le_one 0)
          let v := σ (normalizedRest s hs)
          have hv : |v.weights j - o.weights j| ≤ 1 := abs_le.mpr
            ⟨by linarith [v.weights_nonneg j, o.weights_apply_le_one j],
              by linarith [o.weights_nonneg j, v.weights_apply_le_one j]⟩
          have heq : (simplexConeRaw o σ s).weights j - o.weights j =
              (1 - s.weights 0) * (v.weights j - o.weights j) := by
            simp [simplexConeRaw, hs, Convexity.StdSimplex.weights_convexCombPair, v]
            ring
          rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg hnon]
          exact mul_le_of_le_one_right hnon hv
        · simp only [simplexConeRaw, dite_eq_right hs, sub_self, norm_zero]
          exact sub_nonneg.mpr (s.weights_apply_le_one 0)
      change Filter.Tendsto (fun s ↦ (simplexConeRaw o σ s).weights j) (nhds t)
        (nhds ((simplexConeRaw o σ t).weights j))
      have heq : (simplexConeRaw o σ t).weights j = o.weights j := by
        simp [simplexConeRaw, ht]
      rw [heq]
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero (fun s ↦ norm_nonneg _) hbound
      have hlim : Filter.Tendsto (fun s : Simplex (n + 1) ↦ 1 - s.weights 0)
          (𝓝 t) (𝓝 (1 - t.weights 0)) :=
        (continuous_const.sub (hw 0)).continuousAt.tendsto
      simpa only [ht1, sub_self] using hlim
  cases M with
  | simplex r => exact hs o σ
  | product r s =>
    exact (hs o.1 (ContinuousMap.fst.comp σ)).prodMk
      (hs o.2 (ContinuousMap.snd.comp σ))

/-- The actual continuous singular simplex produced by Bredon's cone. -/
def cone (M : Model) {n : ℕ} (o : M.space) (σ : C(Simplex n, M.space)) :
    C(Simplex (n + 1), M.space) :=
  ⟨coneRaw M o σ, coneRaw_continuous M o σ⟩

end SingularConvexCone
end HolomorphicAnosov
