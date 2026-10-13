import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section
open scoped ContDiff ENNReal Topology
namespace HolomorphicAnosov

/-- A chart-level implicit inverse step for a preimage graph.  The equation is
written on the full product chart.  A `ContDiff` equation, an invertible
horizontal derivative, and local uniqueness of its zero solve imply the same
finite regularity for the graph. Uniqueness is local in the vertical variable
and holds for every horizontal zero above those nearby vertical points, as
supplied by full preimage graph equality.

Proof: interchange the product factors, so that Mathlib's solved second
variable is the horizontal variable X. At each graph point the invertible
horizontal derivative gives a local C^r implicit solution ψ. Its equation
reads F(ψ(z),z)=F(t(y),y)=0 near y. The assumed zero uniqueness gives ψ(z)=t(z)
there. Eventual equality transfers ContDiffAt from ψ to t. Since the anchor
y was arbitrary, t is ContDiff globally. This is the fibrewise inverse step
of HPS pp.56–58; it asserts neither regularity in a parameter nor the
higher-jet induction for an invariant fixed graph. -/
theorem parameter_graph_preimage_implicit_regularity
    {X Y U : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (r : ℕ) (hr : 1 ≤ r)
    (F : X × Y → U) (t : Y → X)
    (hF : ContDiff ℝ (r : ℕ∞ω) F)
    (hzero : ∀ y, F (t y, y) = 0)
    (hinv : ∀ y,
      (fderiv ℝ (fun z : Y × X ↦ F (z.2, z.1)) (y, t y) ∘L
        (ContinuousLinearMap.inr ℝ Y X)).IsInvertible)
    (huniq : ∀ y, ∀ᶠ z in 𝓝 y, ∀ x, F (x, z) = 0 → x = t z) :
    ContDiff ℝ (r : ℕ∞ω) t := by
  have hrpos : 0 < r := lt_of_lt_of_le (by decide) hr
  have hr0 : (r : ℕ∞ω) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hrpos)
  let F' : Y × X → U := fun z ↦ F (z.2, z.1)
  have hF' : ContDiff ℝ (r : ℕ∞ω) F' := by
    change ContDiff ℝ (r : ℕ∞ω) (F ∘ (fun z : Y × X ↦ (z.2, z.1)))
    exact hF.comp (contDiff_snd.prodMk contDiff_fst)
  rw [contDiff_iff_contDiffAt]
  intro y
  let cdf : ContDiffAt ℝ (r : ℕ∞ω) F' (y, t y) := hF'.contDiffAt
  let ψ : Y → X := cdf.implicitFunction hr0 (hinv y)
  have hψ : ContDiffAt ℝ (r : ℕ∞ω) ψ y :=
    cdf.contDiffAt_implicitFunction hr0 (hinv y)
  have heqψ : ∀ᶠ z in 𝓝 y, F (ψ z, z) = 0 := by
    have he := cdf.eventually_apply_implicitFunction hr0 (hinv y)
    simpa [F', cdf, hzero y] using he
  have heq : t =ᶠ[𝓝 y] ψ := by
    filter_upwards [heqψ, huniq y] with z hz hzu
    exact (hzu (ψ z) hz).symm
  exact hψ.congr_of_eventuallyEq heq

/-- Local preimage graph regularity, for the outward germ propagation in
ParameterGraphConstruction §12b–e (HPS pp.56–58). Swap the factors to solve
for the horizontal state. The implicit-function theorem produces a C^r
solution and identifies all nearby solutions of the equation with it.
Continuity of the original graph puts its values in that same neighborhood;
its exact local zero equation therefore identifies it with the smooth
implicit solution as a germ. No global smooth extension or global zero
uniqueness is assumed. -/
theorem parameter_graph_preimage_implicit_regularity_at
    {X Y U : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (r : ℕ) (hr : 1 ≤ r)
    (F : X × Y → U) (t : Y → X) (y : Y)
    (hF : ContDiffAt ℝ (r : ℕ∞ω) F (t y, y))
    (ht : ContinuousAt t y)
    (hzero : ∀ᶠ z in 𝓝 y, F (t z, z) = 0)
    (hinv : (fderiv ℝ (fun z : Y × X ↦ F (z.2, z.1)) (y, t y) ∘L
        (ContinuousLinearMap.inr ℝ Y X)).IsInvertible) :
    ContDiffAt ℝ (r : ℕ∞ω) t y := by
  have hrpos : 0 < r := lt_of_lt_of_le (by decide) hr
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hrpos)
  let F' : Y × X → U := fun z ↦ F (z.2, z.1)
  have hc : ContDiffAt ℝ (r : ℕ∞ω) F' (y, t y) :=
    hF.comp (y, t y) (contDiffAt_snd.prodMk contDiffAt_fst)
  let ψ : Y → X := hc.implicitFunction hr0 hinv
  have hψ : ContDiffAt ℝ (r : ℕ∞ω) ψ y :=
    hc.contDiffAt_implicitFunction hr0 hinv
  have hloc := hc.eventually_apply_eq_iff_implicitFunction hr0 hinv
  have hgraph : Filter.Tendsto (fun z ↦ (z, t z)) (𝓝 y) (𝓝 (y, t y)) :=
    (continuousAt_id.prodMk ht).tendsto
  have heq : t =ᶠ[𝓝 y] ψ := by
    filter_upwards [hgraph.eventually hloc, hzero] with z hz hzz
    have hzy : F' (z, t z) = F' (y, t y) := by
      change F (t z, z) = F (t y, y)
      rw [hzz, hzero.self_of_nhds]
    exact (hz.mp hzy).symm
  exact hψ.congr_of_eventuallyEq heq


end HolomorphicAnosov
