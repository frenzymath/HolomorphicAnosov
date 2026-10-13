import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Set Filter Topology _root_.Topology Metric

namespace HolomorphicAnosov.Analysis.Complex

/-- A locally uniform polynomial limit on an open connected plane set has a primitive.

Source: Conway, Functions of One Complex Variable I, VIII Theorem 2.2, (d) to (f),
pp. 202–204. The implementation uses the equivalent derivative-limit argument:
choose entire primitives of the approximating polynomials and normalize them to zero
at one point. Their derivatives converge uniformly on every compact disk in the domain.
The mean-value estimate propagates the Cauchy property of the primitives across each
such disk. The set of points with Cauchy values is open and relatively closed, so
connectedness makes it the whole domain. Completeness gives pointwise limits; the
locally uniform derivative-limit theorem identifies their derivative with the given
function. This also handles the whole plane without a boundedness assumption. -/
theorem primitive_of_polynomial_approximation_g2
    {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) (f : ℂ → ℂ)
    (p : ℕ → Polynomial ℂ)
    (hp : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n z ↦ (p n).eval z) f atTop K) :
    ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (f z) z := by
  classical
  obtain ⟨a, ha⟩ := hc.nonempty
  have hex (n : ℕ) : ∃ Q : ℂ → ℂ, ∀ z : ℂ, HasDerivAt Q ((p n).eval z) z := by
    obtain ⟨Q, hQ⟩ := (p n).differentiable.isExactOn_univ
    exact ⟨Q, fun z ↦ hQ z (mem_univ z)⟩
  choose Q hQ using hex
  let P : ℕ → ℂ → ℂ := fun n z ↦ Q n z - Q n a
  have hP (n : ℕ) (z : ℂ) : HasDerivAt (P n) ((p n).eval z) z :=
    (hQ n z).sub_const _
  let T := {z : ℂ | z ∈ U ∧ Cauchy (map (fun n ↦ P n z) atTop)}
  have propagate {x : ℂ} {r : ℝ} (hK : closedBall x r ⊆ U)
      (hx : x ∈ T) : ball x r ⊆ T := by
    have hd := (hp (closedBall x r) (isCompact_closedBall x r) hK).uniformCauchySeqOn
    have hC := uniformCauchySeqOn_ball_of_deriv (hd.mono ball_subset_closedBall)
      (fun n z _ ↦ hP n z) hx.2
    exact fun z hz ↦ ⟨hK (ball_subset_closedBall hz), hC.cauchy_map hz⟩
  have hopen : IsOpen T := by
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨r, hr, hK⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx.1)
    refine ⟨r / 2, half_pos hr, propagate ?_ hx⟩
    exact fun z hz ↦ hK (lt_of_le_of_lt hz (half_lt_self hr))
  have hTa : a ∈ T := by
    refine ⟨ha, ?_⟩
    exact cauchy_map_iff_exists_tendsto.mpr ⟨0, by simp [P]⟩
  have hclosed : closure T ∩ U ⊆ T := by
    rintro x ⟨hx, hxU⟩
    obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (r / 4) (by positivity)
    have hK : closedBall y (r / 2) ⊆ U := by
      intro z hz
      apply hB
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ < r := by rw [dist_comm y x]; linarith [mem_closedBall.mp hz]
    exact propagate hK hy (by change dist x y < r / 2; linarith)
  have hUT : U ⊆ T := hc.isPreconnected.subset_of_closure_inter_subset hopen
    ⟨a, ha, hTa⟩ hclosed
  have hlim : ∀ z ∈ U, ∃ v : ℂ, Tendsto (fun n ↦ P n z) atTop (𝓝 v) := by
    intro z hz
    exact cauchy_map_iff_exists_tendsto.mp (hUT hz).2
  let F : ℂ → ℂ := fun z ↦ if hz : z ∈ U then (hlim z hz).choose else 0
  have hF (z : ℂ) (hz : z ∈ U) : Tendsto (fun n ↦ P n z) atTop (𝓝 (F z)) := by
    simpa [F, hz] using (hlim z hz).choose_spec
  refine ⟨F, fun z hz ↦ ?_⟩
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  have hK : closedBall z (r / 2) ⊆ U :=
    fun w hw ↦ hB (lt_of_le_of_lt hw (half_lt_self hr))
  apply hasDerivAt_of_tendstoUniformlyOnFilter
    ((hp _ (isCompact_closedBall z (r / 2)) hK).tendstoUniformlyOnFilter.mono_right
      (le_principal_iff.mpr (closedBall_mem_nhds z (half_pos hr))))
    (Eventually.of_forall fun nz ↦ hP nz.1 nz.2)
  exact eventually_of_mem (hU.mem_nhds hz) hF

end HolomorphicAnosov.Analysis.Complex

