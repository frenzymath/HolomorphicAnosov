import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Bounded continuous invariant sections

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977), Banach-bundle
conventions p. 8, Theorem (3.1)/(3.1′) and its proof p. 25, the disc-subbundle
remark p. 36, and the unit-disc application p. 58. Local source:
`literature/Invariant Manifolds.pdf` (PDF pages 12, 29, 40, 62).
This is DAG node `hps.theorem_3_1_bounded_continuous_sections_g4`.

The total space is the dependent sum of the actual fibres, with its given topology.
The chart model `F x₀` may vary with the chart centre. A local trivialization and
its fibrewise Banach isomorphisms retain both the original total-space topology
and the original norm topology of each fibre. No fixed global model, compactness,
separation condition on the base, or global trivialization is imposed.
The two uniform inverse-norm bounds are the node's explicit compatibility guard;
they are not inferred from pointwise continuity of the total norm.
-/

namespace HolomorphicAnosov

universe u v w

open Bundle
open Set Filter
open scoped Topology _root_.Topology

variable {X : Type u} [TopologicalSpace X]
variable (E : X → Type v) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)] [∀ x, CompleteSpace (E x)]
variable (F : X → Type w) [∀ x, NormedAddCommGroup (F x)]
  [∀ x, NormedSpace ℝ (F x)] [∀ x, CompleteSpace (F x)]
variable [TopologicalSpace (Sigma E)]

set_option linter.unusedSectionVars false in
/-- The actual local Banach charts make a supremum-metric limit of continuous bounded
sections continuous. The proof uses the chart's given lower inverse-norm bound, uniformly
on its actual open base set; no compactness of the base is used. -/
private theorem continuous_section_of_lp_tendsto
    (hcharts : ∀ x₀ : X, ∃ e : Trivialization (F x₀) (Sigma.fst (β := E)),
      x₀ ∈ e.baseSet ∧ ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ x ∈ e.baseSet, ∃ L : E x ≃L[ℝ] F x₀,
          (∀ v : E x, e ⟨x, v⟩ = (x, L v)) ∧
          ∀ u : F x₀, c * ‖u‖ ≤ ‖L.symm u‖ ∧ ‖L.symm u‖ ≤ C * ‖u‖)
    (s : lp E ⊤) (sₙ : ℕ → lp E ⊤)
    (hsₙ : ∀ n, Continuous (fun x ↦ (⟨x, sₙ n x⟩ : Sigma E)))
    (hlim : Tendsto sₙ atTop (𝓝 s)) :
    Continuous (fun x ↦ (⟨x, s x⟩ : Sigma E)) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  obtain ⟨e, hx₀, c, C, hc, _, hL⟩ := hcharts x₀
  let a : ℕ → X → F x₀ := fun n x ↦ (e ⟨x, sₙ n x⟩).2
  let b : X → F x₀ := fun x ↦ (e ⟨x, s x⟩).2
  have hbound : ∀ n, ∀ x ∈ e.baseSet, dist (a n x) (b x) ≤ c⁻¹ * ‖sₙ n - s‖ := by
    intro n x hx
    obtain ⟨L, hcoord, hnorm⟩ := hL x hx
    have hlower := (hnorm (L (sₙ n x - s x))).1
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hlower
    have hcoordbound : ‖sₙ n x - s x‖ ≤ ‖sₙ n - s‖ :=
      lp.norm_apply_le_norm ENNReal.top_ne_zero (sₙ n - s) x
    have hh : ‖L (sₙ n x - s x)‖ ≤ c⁻¹ * ‖sₙ n - s‖ := by
      calc
        ‖L (sₙ n x - s x)‖ ≤ ‖sₙ n - s‖ / c := by
          apply (le_div_iff₀ hc).mpr
          simpa only [mul_comm] using hlower.trans hcoordbound
        _ = c⁻¹ * ‖sₙ n - s‖ := by ring
    simpa only [a, b, hcoord, Prod.snd, dist_eq_norm, ← map_sub] using hh
  have huniform : TendstoUniformlyOn a b atTop e.baseSet := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have ht : Tendsto (fun n ↦ c⁻¹ * ‖sₙ n - s‖) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul ((hlim.sub_const s).norm))
    filter_upwards [ht.eventually_lt_const hε] with n hn x hx
    simpa only [dist_comm] using (hbound n x hx).trans_lt hn
  have hcont : ContinuousOn b e.baseSet := huniform.continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n ↦ by
      have ht := e.toOpenPartialHomeomorph.continuousOn.comp (hsₙ n).continuousOn
        (fun x hx ↦ show (⟨x, sₙ n x⟩ : Sigma E) ∈ e.source from e.mem_source.mpr hx)
      exact ht.snd)))
  apply e.continuousAt_of_comp_left (show ContinuousAt (fun x : X ↦ (⟨x, s x⟩ : Sigma E).1) x₀ from continuousAt_id) hx₀
  have heq : ∀ x ∈ e.baseSet, e (⟨x, s x⟩ : Sigma E) = (x, b x) := by
    intro x hx
    exact (e.mk_proj_snd' hx).symm
  exact (continuousAt_id.prodMk (hcont.continuousAt (e.open_baseSet.mem_nhds hx₀))).congr_of_eventuallyEq
    (by filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx; exact heq x hx)

set_option linter.unusedSectionVars false in
private theorem continuous_zero_section
    (hcharts : ∀ x₀ : X, ∃ e : Trivialization (F x₀) (Sigma.fst (β := E)),
      x₀ ∈ e.baseSet ∧ ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ x ∈ e.baseSet, ∃ L : E x ≃L[ℝ] F x₀,
          (∀ v : E x, e ⟨x, v⟩ = (x, L v)) ∧
          ∀ u : F x₀, c * ‖u‖ ≤ ‖L.symm u‖ ∧ ‖L.symm u‖ ≤ C * ‖u‖) :
    Continuous (fun x ↦ (⟨x, (0 : E x)⟩ : Sigma E)) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  obtain ⟨e, hx₀, c, C, hc, hC, hL⟩ := hcharts x₀
  apply (e.continuousAt_symm_prodMk_left (v := (0 : F x₀)) hx₀).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx
  obtain ⟨L, hcoord, _⟩ := hL x hx
  have he : e (⟨x, (0 : E x)⟩ : Sigma E) = (x, 0) := by simpa using hcoord 0
  rw [← he]
  exact (e.toOpenPartialHomeomorph.left_inv
    (show (⟨x, (0 : E x)⟩ : Sigma E) ∈ e.source from e.mem_source.mpr hx)).symm

/-- **HPS (3.1), bounded invariant sections over any topological base.**

Source: HPS, *Invariant Manifolds* (1977), p. 8 and Theorem (3.1)/(3.1′), p. 25.
The explicit local uniform norm-comparability hypothesis is the compatibility
guard of the DAG statement; p. 8 does not prove it from norm continuity alone.

Proof following the node and the printed bounded-section contraction argument:

1. Identify sections with dependent functions into the given fibres. Bounded
   sections form the dependent `lp` space with exponent infinity. With the
   supremum norm it is complete, because each actual fibre is complete.
   Its metric bounds each coordinate difference, and a uniform coordinate
   bound bounds that metric. The zero section is an element of this space.
2. Define the graph transform by T(s)(x) = f(h⁻¹(x), s(h⁻¹(x))). If B bounds
   the zero images and R bounds s, the fibre triangle inequality and contraction
   give the bound qR+B on T(s). Thus it is a self-map of bounded sections.
   Its distance on two sections is at most q times their supremum distance.
   Evaluating at h(x) identifies its fixed points exactly with the displayed
   invariance equation, using the actual inverse of the homeomorphism.
3. Continuous bounded sections form a closed subset. Indeed, for a sequence
   converging in the supremum metric, use any given chart with lower constant
   c>0. Its coordinate differences are bounded uniformly by c⁻¹ times that
   metric difference. The coordinate functions therefore converge uniformly
   on the chart's base set; the uniform-limit theorem, on that subspace and
   the nontrivial filter Nat.atTop, makes the limit continuous. The chart
   inverse gives continuity of the section locally, and these open sets cover
   X. The metric sequential criterion gives closedness. The zero section is
   continuous because each chart is fibrewise linear. Continuity of f and h⁻¹
   makes the graph transform preserve this closed subset.
4. The strict-contraction fixed-point theorem on the complete bounded-section
   space gives a fixed section and convergence of the iterates of zero.
   Those iterates are continuous; closedness gives continuity of their limit.
   Any other bounded invariant section is another fixed point and hence equal
   to it, even when continuity was not assumed for that competitor.
5. If X is empty, the dependent function space has just the empty section,
   its bound can be zero, and continuity and invariance are vacuous. Zero
   fibres cause no exception; no nonzero vector or positive inverse norm is
   used. No differentiability, holomorphicity, or foliation is concluded.
-/
theorem bounded_continuous_invariant_section
    (hnorm : Continuous (fun z : Sigma E ↦ ‖z.2‖))
    (hcharts : ∀ x₀ : X, ∃ e : Trivialization (F x₀) (Sigma.fst (β := E)),
      x₀ ∈ e.baseSet ∧ ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ x ∈ e.baseSet, ∃ L : E x ≃L[ℝ] F x₀,
          (∀ v : E x, e ⟨x, v⟩ = (x, L v)) ∧
          ∀ u : F x₀, c * ‖u‖ ≤ ‖L.symm u‖ ∧ ‖L.symm u‖ ≤ C * ‖u‖)
    (h : X ≃ₜ X) (f : ∀ x : X, E x → E (h x))
    (hf : Continuous (fun z : Sigma E ↦ (⟨h z.1, f z.1 z.2⟩ : Sigma E)))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ (x : X) (v w : E x), ‖f x v - f x w‖ ≤ q * ‖v - w‖)
    (hzero : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : X, ‖f x 0‖ ≤ B) :
    ∃ s : ∀ x : X, E x,
      (∃ R : ℝ, 0 ≤ R ∧ ∀ x : X, ‖s x‖ ≤ R) ∧
      (∀ x : X, f x (s x) = s (h x)) ∧
      Continuous (fun x : X ↦ (⟨x, s x⟩ : Sigma E)) ∧
      ∀ t : ∀ x : X, E x,
        (∃ R : ℝ, 0 ≤ R ∧ ∀ x : X, ‖t x‖ ≤ R) →
        (∀ x : X, f x (t x) = t (h x)) → t = s := by
  classical
  have _hnorm := hnorm
  obtain ⟨B, hB, hzero⟩ := hzero
  let g (s : lp E ⊤) : ∀ x, E x :=
    Equiv.piCongrLeft E h.toEquiv (fun x ↦ f x (s x))
  have hg (s : lp E ⊤) (x : X) : g s (h x) = f x (s x) := by
    exact Equiv.piCongrLeft_apply_apply E h.toEquiv (fun x ↦ f x (s x)) x
  have hgbound (s : lp E ⊤) : ∀ x, ‖g s x‖ ≤ q * ‖s‖ + B := by
    intro y
    obtain ⟨x, rfl⟩ := h.surjective y
    rw [hg]
    calc
      ‖f x (s x)‖ ≤ ‖f x (s x) - f x 0‖ + ‖f x 0‖ := norm_le_norm_sub_add _ _
      _ ≤ q * ‖s x - 0‖ + B := add_le_add (hcontract x _ _) (hzero x)
      _ ≤ q * ‖s‖ + B := by
        simp only [sub_zero]
        gcongr
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero s x
  let T : lp E ⊤ → lp E ⊤ := fun s ↦ ⟨g s, memℓp_infty_iff.mpr
    ⟨q * ‖s‖ + B, by rintro _ ⟨x, rfl⟩; exact hgbound s x⟩⟩
  have hT (s : lp E ⊤) (x : X) : T s (h x) = f x (s x) := hg s x
  have hTc : ContractingWith ⟨q, hq0⟩ T := by
    refine ⟨hq1, LipschitzWith.of_dist_le_mul ?_⟩
    intro s t
    rw [dist_eq_norm, dist_eq_norm]
    apply lp.norm_le_of_forall_le (mul_nonneg hq0 (norm_nonneg _))
    intro y
    obtain ⟨x, rfl⟩ := h.surjective y
    change ‖T s (h x) - T t (h x)‖ ≤ q * ‖s - t‖
    rw [hT, hT]
    exact (hcontract x _ _).trans (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero (s - t) x) hq0)
  have hTcontinuous (s : lp E ⊤)
      (hs : Continuous (fun x ↦ (⟨x, s x⟩ : Sigma E))) :
      Continuous (fun x ↦ (⟨x, T s x⟩ : Sigma E)) := by
    have hc := (hf.comp hs).comp h.symm.continuous
    apply hc.congr
    intro y
    obtain ⟨x, rfl⟩ := h.surjective y
    dsimp only [Function.comp_def]
    rw [h.symm_apply_apply]
    congr 1
    exact (hT s x).symm
  let s := hTc.fixedPoint T
  have hfix : T s = s := hTc.fixedPoint_isFixedPt
  have hiter : ∀ n, Continuous (fun x ↦ (⟨x, T^[n] 0 x⟩ : Sigma E)) := by
    intro n
    induction n with
    | zero => simpa using continuous_zero_section E F hcharts
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hTcontinuous _ ih
  refine ⟨s, ⟨‖s‖, norm_nonneg _, fun x ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero s x⟩,
    ?_, continuous_section_of_lp_tendsto E F hcharts s (fun n ↦ T^[n] 0)
      hiter (hTc.tendsto_iterate_fixedPoint 0), ?_⟩
  · intro x
    rw [← hT, hfix]
  · intro t ht hinv
    obtain ⟨R, hR, ht⟩ := ht
    let t' : lp E ⊤ := ⟨t, memℓp_infty_iff.mpr ⟨R, by rintro _ ⟨x, rfl⟩; exact ht x⟩⟩
    have htfix : T t' = t' := by
      apply Subtype.ext
      funext y
      obtain ⟨x, rfl⟩ := h.surjective y
      exact (hT t' x).trans (hinv x)
    have heq := hTc.fixedPoint_unique htfix
    exact congrArg (fun r : lp E ⊤ ↦ (r : ∀ x, E x)) heq


/-- **HPS closed-unit-disc invariant section theorem, with no ambient extension.**

Source: HPS, *Invariant Manifolds* (1977), the bounded-section proof p. 25,
the disc-subbundle remark p. 36 and the unit-disc application p. 58, under
the same Banach-bundle conventions p. 8 and explicit chart compatibility.
The map is defined only on the displayed closed fibre discs and its continuity
uses their actual total-space subspace topology.

Proof following all the disc steps of the current node:

1. As for HPS (3.1), the dependent space of bounded sections, with the given
   fibre norms and supremum metric, is complete. The sections with norm at
   most one at every coordinate form a nonempty closed subset: zero belongs,
   and convergence in supremum metric implies convergence in every fibre.
   Continuity of the fibre norm preserves the closed inequality in the limit.
   The metric sequential closedness criterion and the closed-subtype
   completeness theorem give a complete induced metric on this subset.
2. On that subset define T(s)(x) = f(h⁻¹(x), s(h⁻¹(x))). Its output remains
   in the closed unit disc by the codomain of f. The contraction inequality
   on pairs in each disc gives supremum distance at most q times the input
   distance. No value of f on any vector outside its disc is used. Its zero
   image is automatically bounded by one, without a separate assumption.
3. Continuous sections into the total disc are preserved by composition with
   f and h⁻¹. Continuity into the disc is equivalent to continuity into the
   total bundle for a disc-valued section, by the induced subtype topology.
   The local chart estimate with its positive lower constant proves that a
   uniform limit of these continuous sections is continuous: model-coordinate
   error is bounded by c⁻¹ times the supremum-metric error. Apply uniform-limit
   continuity on each open chart base, then the inverse chart and the cover.
4. The strict-contraction theorem gives a fixed point and convergence of the
   iterates of zero within the complete unit-disc section carrier. Every
   iterate is continuous, so the preceding local limit argument makes the
   fixed section continuous. Its fixed-point equation is exactly invariance
   after evaluation at h(x). Every invariant disc section is bounded by one
   and is a fixed point of this same self-map; strict-contraction uniqueness
   identifies it with the chosen section without assuming it continuous.
5. The empty base and zero fibres are included. Neither completeness of an
   open disc nor an extension of f off the closed unit disc is asserted.
-/
theorem closed_unit_disc_continuous_invariant_section
    (hnorm : Continuous (fun z : Sigma E ↦ ‖z.2‖))
    (hcharts : ∀ x₀ : X, ∃ e : Trivialization (F x₀) (Sigma.fst (β := E)),
      x₀ ∈ e.baseSet ∧ ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ x ∈ e.baseSet, ∃ L : E x ≃L[ℝ] F x₀,
          (∀ v : E x, e ⟨x, v⟩ = (x, L v)) ∧
          ∀ u : F x₀, c * ‖u‖ ≤ ‖L.symm u‖ ∧ ‖L.symm u‖ ≤ C * ‖u‖)
    (h : X ≃ₜ X)
    (f : ∀ x : X, {v : E x // ‖v‖ ≤ 1} → {v : E (h x) // ‖v‖ ≤ 1})
    (hf : Continuous
      (fun z : {z : Sigma E // ‖z.2‖ ≤ 1} ↦
        (⟨⟨h z.1.1, (f z.1.1 ⟨z.1.2, z.2⟩).1⟩,
          (f z.1.1 ⟨z.1.2, z.2⟩).2⟩ : {z : Sigma E // ‖z.2‖ ≤ 1})))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ (x : X) (v w : {v : E x // ‖v‖ ≤ 1}),
      ‖(f x v).1 - (f x w).1‖ ≤ q * ‖v.1 - w.1‖) :
    ∃ s : ∀ x : X, {v : E x // ‖v‖ ≤ 1},
      (∀ x : X, f x (s x) = s (h x)) ∧
      Continuous (fun x : X ↦ (⟨x, (s x).1⟩ : Sigma E)) ∧
      ∀ t : ∀ x : X, {v : E x // ‖v‖ ≤ 1},
        (∀ x : X, f x (t x) = t (h x)) → t = s := by
  classical
  have _hnorm := hnorm
  let S := {s : lp E ⊤ // ∀ x, ‖s x‖ ≤ 1}
  have hclosed : IsClosed {s : lp E ⊤ | ∀ x, ‖s x‖ ≤ 1} := by
    have heq : {s : lp E ⊤ | ∀ x, ‖s x‖ ≤ 1} =
        ⋂ x, {s : lp E ⊤ | ‖s x‖ ≤ 1} := by ext s; simp
    rw [heq]
    exact isClosed_iInter (fun x ↦ isClosed_le (lp.evalCLM ℝ E ⊤ x).continuous.norm continuous_const)
  let : CompleteSpace S := hclosed.completeSpace_coe
  let z : S := ⟨0, by intro x; simp⟩
  let : Nonempty S := ⟨z⟩
  let disc := fun x ↦ {v : E x // ‖v‖ ≤ 1}
  let g (s : S) : ∀ x, disc x :=
    Equiv.piCongrLeft disc h.toEquiv (fun x ↦ f x ⟨s.1 x, s.2 x⟩)
  have hg (s : S) (x : X) : g s (h x) = f x ⟨s.1 x, s.2 x⟩ := by
    exact Equiv.piCongrLeft_apply_apply disc h.toEquiv _ x
  let T : S → S := fun s ↦
    ⟨⟨fun x ↦ (g s x).1, memℓp_infty_iff.mpr
      ⟨1, by rintro _ ⟨x, rfl⟩; exact (g s x).2⟩⟩, fun x ↦ (g s x).2⟩
  have hT (s : S) (x : X) : (T s).1 (h x) = (f x ⟨s.1 x, s.2 x⟩).1 := by
    change (g s (h x)).1 = _
    rw [hg]
  have hTc : ContractingWith ⟨q, hq0⟩ T := by
    refine ⟨hq1, LipschitzWith.of_dist_le_mul ?_⟩
    intro s t
    change dist (T s).1 (T t).1 ≤ q * dist s.1 t.1
    rw [dist_eq_norm, dist_eq_norm]
    apply lp.norm_le_of_forall_le (mul_nonneg hq0 (norm_nonneg _))
    intro y
    obtain ⟨x, rfl⟩ := h.surjective y
    change ‖(T s).1 (h x) - (T t).1 (h x)‖ ≤ q * ‖s.1 - t.1‖
    rw [hT, hT]
    exact (hcontract x _ _).trans (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero (s.1 - t.1) x) hq0)
  have hTcontinuous (s : S)
      (hs : Continuous (fun x ↦ (⟨x, s.1 x⟩ : Sigma E))) :
      Continuous (fun x ↦ (⟨x, (T s).1 x⟩ : Sigma E)) := by
    have hsd : Continuous (fun x ↦ (⟨⟨x, s.1 x⟩, s.2 x⟩ :
        {z : Sigma E // ‖z.2‖ ≤ 1})) := hs.subtype_mk _
    have hc := (continuous_subtype_val.comp (hf.comp hsd)).comp h.symm.continuous
    apply hc.congr
    intro y
    obtain ⟨x, rfl⟩ := h.surjective y
    dsimp only [Function.comp_def]
    rw [h.symm_apply_apply]
    congr 1
    exact (hT s x).symm
  let s := hTc.fixedPoint T
  have hfix : T s = s := hTc.fixedPoint_isFixedPt
  have hiter : ∀ n, Continuous (fun x ↦ (⟨x, (T^[n] z).1 x⟩ : Sigma E)) := by
    intro n
    induction n with
    | zero =>
      change Continuous (fun x ↦ (⟨x, (0 : E x)⟩ : Sigma E))
      exact continuous_zero_section E F hcharts
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hTcontinuous _ ih
  have hlim : Tendsto (fun n ↦ (T^[n] z).1) atTop (𝓝 s.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp (hTc.tendsto_iterate_fixedPoint z)
  refine ⟨(fun x ↦ ⟨s.1 x, s.2 x⟩), ?_,
    continuous_section_of_lp_tendsto E F hcharts s.1 (fun n ↦ (T^[n] z).1) hiter hlim, ?_⟩
  · intro x
    apply Subtype.ext
    rw [← hT, hfix]
  · intro t hinv
    let t' : S := ⟨⟨fun x ↦ (t x).1, memℓp_infty_iff.mpr
      ⟨1, by rintro _ ⟨x, rfl⟩; exact (t x).2⟩⟩, fun x ↦ (t x).2⟩
    have htfix : T t' = t' := by
      apply Subtype.ext
      apply Subtype.ext
      funext y
      obtain ⟨x, rfl⟩ := h.surjective y
      exact (hT t' x).trans (congrArg Subtype.val (hinv x))
    have heq := hTc.fixedPoint_unique htfix
    funext x
    apply Subtype.ext
    exact congrArg (fun r : S ↦ r.1 x) heq



end HolomorphicAnosov
