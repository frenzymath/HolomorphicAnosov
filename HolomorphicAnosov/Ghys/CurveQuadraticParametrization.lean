import Mathlib.Analysis.Calculus.Deriv.Pow
import HolomorphicAnosov.Ghys.ScalarLocalBiholomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Realization of normalized complex two-jet coefficients in a curve chart. (Michor, §1.3 p.2;
Ghys, §3 p.591) -/
open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u

/-- Every coefficient triple with base in a holomorphic chart target and nonzero linear coefficient
is realized by a local holomorphic parametrization into the chart source. (Michor, §1.3 p.2; Ghys,
§3 p.591) -/
theorem curve_quadratic_parametrization
    {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
    (c : OpenPartialHomeomorph L ℂ)
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L)
    (z a b : ℂ) (hz : z ∈ c.target) (ha : a ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ L, 0 ∈ e.source ∧
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ e e.source ∧
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        ∞ e.symm e.target ∧
      e 0 = c.symm z ∧ deriv (c ∘ e) 0 = a ∧ iteratedDeriv 2 (c ∘ e) 0 / 2 = b := by
  let p : ℂ → ℂ := fun t ↦ z + a * t + b * t ^ 2
  have hp : ContDiff ℂ ∞ p := by dsimp [p]; fun_prop
  have hp' (t : ℂ) : HasDerivAt p (a + 2 * b * t) t := by
    convert ((hasDerivAt_const t z).add ((hasDerivAt_id t).const_mul a)).add
      (((hasDerivAt_id t).pow 2).const_mul b) using 1 <;>
    all_goals (try funext w)
    all_goals dsimp [p]
    all_goals norm_num [id]
    all_goals ring
  have hder : deriv p = fun t ↦ a + 2 * b * t := funext fun t ↦ (hp' t).deriv
  have hp0 : p 0 = z := by simp [p]
  have hd0 : deriv p 0 = a := by rw [hder]; simp
  have hdd0 : iteratedDeriv 2 p 0 / 2 = b := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hder]
    have h := ((hasDerivAt_const (0 : ℂ) a).add ((hasDerivAt_id 0).const_mul (2 * b))).deriv
    change deriv (fun t : ℂ ↦ a + 2 * b * t) 0 = 0 + 2 * b * 1 at h
    rw [h]
    ring
  obtain ⟨e₀, h₀, he₀, hf, hi⟩ := scalar_local_biholomorph p hp (by rwa [hd0])
  let e := e₀.trans c.symm
  have he0 : 0 ∈ e.source := by
    change 0 ∈ e₀.source ∧ e₀ 0 ∈ c.target
    exact ⟨h₀, by simpa only [he₀, hp0] using hz⟩
  refine ⟨e, he0, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contMDiffOn_symm_of_mem_maximalAtlas hc).comp' hf.contMDiffOn
  · exact hi.contMDiffOn.comp' (contMDiffOn_of_mem_maximalAtlas hc)
  · change c.symm (e₀ 0) = c.symm z
    rw [he₀, hp0]
  all_goals
    have heq : (c ∘ e) =ᶠ[𝓝 (0 : ℂ)] p := by
      filter_upwards [e.open_source.mem_nhds he0] with t ht
      change c (c.symm (e₀ t)) = p t
      have hct : e₀ t ∈ c.target := ht.2
      rw [c.right_inv hct, he₀]
    first | exact heq.deriv_eq.trans hd0 |
      exact (congrArg (fun v : ℂ ↦ v / 2) (heq.iteratedDeriv_eq 2)).trans hdd0

end HolomorphicAnosov.Ghys
