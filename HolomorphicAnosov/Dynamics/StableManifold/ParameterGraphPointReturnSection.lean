import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Invariant unit sections for a point-valued return

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977), bounded-section
contraction p.25, closed-disc restriction p.36, image representatives pp.55–56,
preimage action pp.57–58, and parameter insertion p.62. This is the explicit
point-return assembly in `hps.parameter_graph_point_return_section_g12`.
-/

namespace HolomorphicAnosov

universe u v w
open Bundle Set Filter
open scoped Topology _root_.Topology

variable {X : Type u} [TopologicalSpace X]
variable (E : X → Type v) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)] [∀ x, CompleteSpace (E x)]
variable (F : X → Type w) [∀ x, NormedAddCommGroup (F x)]
  [∀ x, NormedSpace ℝ (F x)]
variable [TopologicalSpace (Sigma E)]

/-- HPS's bounded-section contraction for an arbitrary point-valued return.
Source: HPS pp.25,36,55–58,62, with the original local Banach-chart compatibility
and the explicit continuity-preservation guard displayed below.

Proof. Bounded sections in the original fibre norms form the complete dependent
`lp E ⊤` space. The unit-section carrier is closed by continuous coordinate
norms and contains zero. The operator T(s)(x)=f_x(s(Rx)) preserves that carrier
and contracts its supremum metric by q. Banach's theorem gives its fixed point
and convergence of the iterates of zero. The given linear local charts make
zero continuous; the continuity-preservation guard makes every iterate continuous.
On any chart with lower inverse-norm constant c>0, coordinate errors are bounded
by c⁻¹ times the supremum error. Thus these coordinates converge uniformly on the
chart base. Uniform-limit continuity and the inverse chart give continuity of the
fixed section in the original total-space topology. Every invariant unit section
belongs to this same carrier and is a fixed point, so contraction uniqueness
identifies it with the constructed section without assuming continuity of the
competitor. The empty base, zero fibres, and noninjective or nonsurjective R are
included. No ambient extension of the closed-disc maps is used. -/
theorem parameter_graph_point_return_section
    (hcharts : ∀ x₀ : X, ∃ e : Trivialization (F x₀) (Sigma.fst (β := E)),
      x₀ ∈ e.baseSet ∧ ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ x ∈ e.baseSet, ∃ L : E x ≃L[ℝ] F x₀,
          (∀ v : E x, e ⟨x, v⟩ = (x, L v)) ∧
          ∀ u : F x₀, c * ‖u‖ ≤ ‖L.symm u‖ ∧ ‖L.symm u‖ ≤ C * ‖u‖)
    (R : X → X)
    (f : ∀ x : X, {v : E (R x) // ‖v‖ ≤ 1} → {v : E x // ‖v‖ ≤ 1})
    (hpreserve : ∀ s : ∀ x : X, {v : E x // ‖v‖ ≤ 1},
      Continuous (fun x ↦ (⟨x, (s x).1⟩ : Sigma E)) →
      Continuous (fun x ↦ (⟨x, (f x (s (R x))).1⟩ : Sigma E)))
    (q : NNReal) (hq : (q : ℝ) < 1)
    (hcontract : ∀ (x : X) (v w : {v : E (R x) // ‖v‖ ≤ 1}),
      ‖(f x v).1 - (f x w).1‖ ≤ (q : ℝ) * ‖v.1 - w.1‖) :
    ∃ s : ∀ x : X, {v : E x // ‖v‖ ≤ 1},
      (∀ x, f x (s (R x)) = s x) ∧
      Continuous (fun x ↦ (⟨x, (s x).1⟩ : Sigma E)) ∧
      ∀ t : ∀ x : X, {v : E x // ‖v‖ ≤ 1},
        (∀ x, f x (t (R x)) = t x) → t = s := by
  classical
  let S := {s : lp E ⊤ // ∀ x, ‖s x‖ ≤ 1}
  have hclosed : IsClosed {s : lp E ⊤ | ∀ x, ‖s x‖ ≤ 1} := by
    have heq : {s : lp E ⊤ | ∀ x, ‖s x‖ ≤ 1} =
        ⋂ x, {s : lp E ⊤ | ‖s x‖ ≤ 1} := by ext s; simp
    rw [heq]
    exact isClosed_iInter (fun x ↦
      isClosed_le (lp.evalCLM ℝ E ⊤ x).continuous.norm continuous_const)
  let : CompleteSpace S := hclosed.completeSpace_coe
  let z : S := ⟨0, by intro x; simp⟩
  let : Nonempty S := ⟨z⟩
  let T : S → S := fun s ↦
    ⟨⟨fun x ↦ (f x ⟨s.1 (R x), s.2 (R x)⟩).1, memℓp_infty_iff.mpr
      ⟨1, by rintro _ ⟨x, rfl⟩; exact (f x ⟨s.1 (R x), s.2 (R x)⟩).2⟩⟩,
      fun x ↦ (f x ⟨s.1 (R x), s.2 (R x)⟩).2⟩
  have hTc : ContractingWith q T := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul ?_⟩
    intro s t
    change dist (T s).1 (T t).1 ≤ (q : ℝ) * dist s.1 t.1
    rw [dist_eq_norm, dist_eq_norm]
    apply lp.norm_le_of_forall_le (mul_nonneg q.2 (norm_nonneg _))
    intro x
    exact (hcontract x _ _).trans (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero (s.1 - t.1) (R x)) q.2)
  let s := hTc.fixedPoint T
  have hfix : T s = s := hTc.fixedPoint_isFixedPt
  have hiter : ∀ n, Continuous (fun x ↦ (⟨x, (T^[n] z).1 x⟩ : Sigma E)) := by
    intro n
    induction n with
    | zero =>
      change Continuous (fun x ↦ (⟨x, (0 : E x)⟩ : Sigma E))
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
    | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        hpreserve (fun x ↦ ⟨(T^[n] z).1 x, (T^[n] z).2 x⟩) ih
  have hlim : Tendsto (fun n ↦ (T^[n] z).1) atTop (𝓝 s.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp (hTc.tendsto_iterate_fixedPoint z)
  refine ⟨(fun x ↦ ⟨s.1 x, s.2 x⟩), ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    exact congrArg (fun r : S ↦ r.1 x) hfix
  ·
    apply continuous_iff_continuousAt.mpr
    intro x₀
    obtain ⟨e, hx₀, c, C, hc, _, hL⟩ := hcharts x₀
    let a : ℕ → X → F x₀ := fun n x ↦ (e ⟨x, (T^[n] z).1 x⟩).2
    let b : X → F x₀ := fun x ↦ (e ⟨x, s.1 x⟩).2
    have hbound : ∀ n, ∀ x ∈ e.baseSet, dist (a n x) (b x) ≤ c⁻¹ * ‖(T^[n] z).1 - s.1‖ := by
      intro n x hx
      obtain ⟨L, hcoord, hnorm⟩ := hL x hx
      have hlower := (hnorm (L ((T^[n] z).1 x - s.1 x))).1
      simp only [ContinuousLinearEquiv.symm_apply_apply] at hlower
      have hcoordbound : ‖(T^[n] z).1 x - s.1 x‖ ≤ ‖(T^[n] z).1 - s.1‖ :=
        lp.norm_apply_le_norm ENNReal.top_ne_zero ((T^[n] z).1 - s.1) x
      have hh : ‖L ((T^[n] z).1 x - s.1 x)‖ ≤ c⁻¹ * ‖(T^[n] z).1 - s.1‖ := by
        calc
          ‖L ((T^[n] z).1 x - s.1 x)‖ ≤ ‖(T^[n] z).1 - s.1‖ / c := by
            apply (le_div_iff₀ hc).mpr
            simpa only [mul_comm] using hlower.trans hcoordbound
          _ = c⁻¹ * ‖(T^[n] z).1 - s.1‖ := by ring
      simpa only [a, b, hcoord, Prod.snd, dist_eq_norm, ← map_sub] using hh
    have huniform : TendstoUniformlyOn a b atTop e.baseSet := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      have ht : Tendsto (fun n ↦ c⁻¹ * ‖(T^[n] z).1 - s.1‖) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul ((hlim.sub_const s.1).norm))
      filter_upwards [ht.eventually_lt_const hε] with n hn x hx
      rw [dist_comm]
      exact (hbound n x hx).trans_lt hn
    have hcont : ContinuousOn b e.baseSet := huniform.continuousOn
      (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n ↦ by
        have ht := e.toOpenPartialHomeomorph.continuousOn.comp (hiter n).continuousOn
          (fun x hx ↦ show (⟨x, (T^[n] z).1 x⟩ : Sigma E) ∈ e.source from e.mem_source.mpr hx)
        exact ht.snd)))
    apply e.continuousAt_of_comp_left (show ContinuousAt (fun x : X ↦ (⟨x, s.1 x⟩ : Sigma E).1) x₀ from continuousAt_id) hx₀
    have heq : ∀ x ∈ e.baseSet, e (⟨x, s.1 x⟩ : Sigma E) = (x, b x) := by
      intro x hx
      exact (e.mk_proj_snd' hx).symm
    exact (continuousAt_id.prodMk (hcont.continuousAt (e.open_baseSet.mem_nhds hx₀))).congr_of_eventuallyEq
      (by filter_upwards [e.open_baseSet.mem_nhds hx₀] with x hx; exact heq x hx)
  · intro t hinv
    let t' : S := ⟨⟨fun x ↦ (t x).1, memℓp_infty_iff.mpr
      ⟨1, by rintro _ ⟨x, rfl⟩; exact (t x).2⟩⟩, fun x ↦ (t x).2⟩
    have htfix : T t' = t' := by
      apply Subtype.ext
      apply Subtype.ext
      funext x
      exact congrArg Subtype.val (hinv x)
    have heq := hTc.fixedPoint_unique htfix
    funext x
    apply Subtype.ext
    exact congrArg (fun r : S ↦ r.1 x) heq

end HolomorphicAnosov
