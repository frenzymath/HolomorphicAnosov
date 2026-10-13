import HolomorphicAnosov.Analysis.DistributionSmoothFixedSupportFamily
import HolomorphicAnosov.Analysis.Distribution.ScaledMollifierTest
import HolomorphicAnosov.Analysis.Distribution.MollifierDerivativeIdentity
import HolomorphicAnosov.Analysis.Distribution.MollifierWeakConvergence
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Local distributional mollifier regularization

Source: Demailly, *Complex Analytic and Differential Geometry*, June 21, 2012,
I §2.D.3 (2.23), printed p.19, with I §2.A (2.3), p.14 and distributional
derivative transposition (2.6), p.15. This module states the local regularization,
derivative commutation, fixed-test weak convergence and ∂̄ consequence for the
native LF space of complex test functions. No evenness of the kernel is assumed.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology
attribute [local instance] Classical.propDecidable

namespace HolomorphicAnosov.Analysis.Distribution

/-- The strict interior on which an ε-ball remains in the open set.  The
extended distance makes the complement of the whole space have distance ∞.
Source: the interior support margin used in Demailly, I §2.D.3 (2.23), printed
p.19; `Metric.infEDist` implements this margin with its native empty-set value ∞. -/
def mollifierDomain {m : ℕ} (U : Opens (EuclideanSpace ℝ (Fin m))) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set (EuclideanSpace ℝ (Fin m)))ᶜ)}

/--
Distributional mollification on a finite-dimensional real Euclidean space.  The
complex test-function dual is used explicitly: test functions are not
conjugated.  The existential `κ` records the bundled smooth compactly
supported test function represented by the displayed scaled kernel; `F` is
its distributional pairing, extended by zero outside the strict interior.
The ordered directional derivative operator `D` is the native Mathlib
`TestFunction.lineDerivCLM` transposition, iterated with the minus sign.
Coordinate multi-indices are the special case in which the directions are
`EuclideanSpace.single i 1`.  The last implication is the real-coordinate
form of the antiholomorphic equation in complex dimension `n`.

Source: Demailly, *Complex Analytic and Differential Geometry*, June 21, 2012,
I §2.D.3 (2.23), p.19; I §2.A (2.3), p.14; transposition (2.6), p.15.
The kernel need not be even: the adjoint approximate identity is reflected.

Proof: Dilation gives support in the closed ε-ball and normalization by the
Euclidean change-of-variables formula with determinant ε^m. At a point of
the strict interior, choose a small parameter ball whose translated closed
ε-balls have a common compact union contained in U. The fixed-support smooth
family pairing theorem makes F smooth there and allows differentiation under
T. Every x-derivative of the kernel is the negative corresponding y-derivative.
Repeated transposition therefore gives D, with one minus sign per derivative.
The iterated Fréchet derivative evaluated on coordinate unit vectors is the
corresponding ordered partial derivative; smoothness makes order immaterial.

For a fixed test φ, its compact support has a positive margin inside U. Thus
it lies in every sufficiently small strict interior. Pairing/integral
interchange gives the integral of F times φ as T applied to
ηε(y)=∫ρε(u)φ(y+u)du. These ηε have support in a single compact subset of U.
For every finite derivative order, positivity and normalization of ρε bound
the uniform derivative error by the modulus of continuity of that derivative
of φ on a fixed compact neighborhood. Hence ηε converges to φ in every
fixed-support test-function seminorm. Continuity of T yields the displayed
weak limit. Finally, complex linearity and the first derivative identities
give the ∂̄ equation, with +i and no conjugation. For empty U all pointwise
clauses are vacuous and its only test is zero; for the whole space the empty
complement has extended distance ∞, as required.
-/
theorem local_distribution_mollifier_regularization
    {m : ℕ} (hm : 1 ≤ m)
    (U : Opens (EuclideanSpace ℝ (Fin m)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hρ_support : tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆
      Metric.closedBall 0 1)
    (hρ_norm : ∫ x, ρ x ∂volume = 1) :
    ∃ (κ : ∀ ε : ℝ, 0 < ε → ∀ x, x ∈ mollifierDomain U ε →
          TestFunction U ℂ ⊤)
      (F : ∀ ε : ℝ, 0 < ε → EuclideanSpace ℝ (Fin m) → ℂ)
      (D : ∀ k : ℕ, (Fin k → Fin m) → TestFunction U ℂ ⊤ → ℂ),
      (∀ ε (hε : 0 < ε) x hx y,
        κ ε hε x hx y =
          (((ε⁻¹) ^ m : ℝ) : ℂ) *
            ((ρ (ε⁻¹ • (x - y)) : ℝ) : ℂ)) ∧
      (∀ ε (hε : 0 < ε) x,
        F ε hε x = if hx : x ∈ mollifierDomain U ε
          then T (κ ε hε x hx) else 0) ∧
      (∀ v φ, D 0 v φ = T φ) ∧
      (∀ k v φ,
        D (k + 1) v φ =
          - D k (Fin.tail v)
            ((TestFunction.lineDerivCLM ℂ
              (EuclideanSpace.single (v 0) 1)) φ)) ∧
      (∀ ε (hε : 0 < ε),
        ContDiffOn ℝ ∞ (F ε hε) (mollifierDomain U ε)) ∧
      (∀ ε (hε : 0 < ε) k (v : Fin k → Fin m) x hx,
        iteratedFDeriv ℝ k (F ε hε) x
            (fun i => EuclideanSpace.single (v i) 1) =
          D k v (κ ε hε x hx)) ∧
      (∀ φ : TestFunction U ℂ ⊤, ∃ ε₀ > 0,
        (∀ ε, 0 < ε → ε < ε₀ →
          tsupport (φ : EuclideanSpace ℝ (Fin m) → ℂ) ⊆
            mollifierDomain U ε) ∧
        Tendsto
          (fun ε : ℝ => if hε : 0 < ε then
            ∫ x in mollifierDomain U ε,
              F ε hε x * φ x
            else 0)
          (𝓝[>] (0 : ℝ)) (𝓝 (T φ))) ∧
      ((∀ n (hmn : m = 2 * n) (i : Fin m) (hi : i.val < n)
          (φ : TestFunction U ℂ ⊤),
          let j : Fin m := ⟨n + i.val, by omega⟩
          (D 1 (fun _ => i) φ + Complex.I * D 1 (fun _ => j) φ) / 2 = 0) →
        ∀ n (hmn : m = 2 * n) (i : Fin m) (hi : i.val < n)
          (ε : ℝ) (hε : 0 < ε) x (_hx : x ∈ mollifierDomain U ε),
          let j : Fin m := ⟨n + i.val, by omega⟩
          ((fderiv ℝ (F ε hε) x) (EuclideanSpace.single i 1) +
            Complex.I • (fderiv ℝ (F ε hε) x)
              (EuclideanSpace.single j 1)) / 2 = 0) := by
  classical
  let κ : ∀ ε : ℝ, 0 < ε → ∀ x, x ∈ mollifierDomain U ε → TestFunction U ℂ ⊤ :=
    fun ε hε x hx ↦ Classical.choose (exists_scaled_mollifier_test U ρ hρ_support ε hε x hx.2)
  let F : ∀ ε : ℝ, 0 < ε → EuclideanSpace ℝ (Fin m) → ℂ :=
    fun ε hε x ↦ if hx : x ∈ mollifierDomain U ε then T (κ ε hε x hx) else 0
  let D : ∀ k : ℕ, (Fin k → Fin m) → TestFunction U ℂ ⊤ → ℂ :=
    fun k ↦ Nat.rec (fun _ φ ↦ T φ) (fun k Dk v φ ↦
      - Dk (Fin.tail v) ((TestFunction.lineDerivCLM ℂ
        (EuclideanSpace.single (v 0) 1)) φ)) k
  have hκ : ∀ ε (hε : 0 < ε) x hx y,
      κ ε hε x hx y = (((ε⁻¹) ^ m : ℝ) : ℂ) *
        ((ρ (ε⁻¹ • (x - y)) : ℝ) : ℂ) := by
    intro ε hε x hx y
    exact (Classical.choose_spec (exists_scaled_mollifier_test U ρ hρ_support ε hε x hx.2)) y
  have hF : ∀ ε (hε : 0 < ε) x,
      F ε hε x = if hx : x ∈ mollifierDomain U ε then T (κ ε hε x hx) else 0 := by
    intro ε hε x
    rfl
  have hFinside : ∀ ε (hε : 0 < ε) x (hx : x ∈ mollifierDomain U ε),
      F ε hε x = T (κ ε hε x hx) := by
    intro ε hε x hx
    exact (hF ε hε x).trans (dite_eq_left hx)
  have hD0 : ∀ v φ, D 0 v φ = T φ := by
    intro v φ
    rfl
  have hDsucc : ∀ k v φ, D (k + 1) v φ =
      - D k (Fin.tail v) ((TestFunction.lineDerivCLM ℂ
        (EuclideanSpace.single (v 0) 1)) φ) := by
    intro k v φ
    rfl
  have hderiv : ∀ ε (hε : 0 < ε) k (v : Fin k → Fin m) x hx,
      iteratedFDeriv ℝ k (F ε hε) x
        (fun i ↦ EuclideanSpace.single (v i) 1) = D k v (κ ε hε x hx) := by
    exact distribution_mollifier_derivative_identity hm U T ρ hρ_support κ F D hκ hFinside hD0 hDsucc
  refine ⟨κ, F, D, ?_, ?_, ?_, ?_, ?_, hderiv, ?_, ?_⟩
  · intro ε hε x hx y
    exact (Classical.choose_spec (exists_scaled_mollifier_test U ρ hρ_support ε hε x hx.2)) y
  · intro ε hε x
    rfl
  · intro v φ
    rfl
  · intro k v φ
    rfl
  · intro ε hε
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    obtain ⟨r, hr0, hεr', hr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx.2
    have hεr : ε < r := ENNReal.ofReal_lt_ofReal_iff (ENNReal.ofReal_pos.mp
      ((ENNReal.ofReal_pos.mpr hε).trans hεr')) |>.mp hεr'
    let P : Opens (EuclideanSpace ℝ (Fin m)) :=
      ⟨Metric.ball x (r - ε), Metric.isOpen_ball⟩
    let K : Set (EuclideanSpace ℝ (Fin m)) := Metric.closedBall x r
    let H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℂ :=
      fun p y ↦ (((ε⁻¹) ^ m : ℝ) : ℂ) * ((ρ (ε⁻¹ • (p - y)) : ℝ) : ℂ)
    have hKU : K ⊆ U := by
      intro y hy
      by_contra hn
      have hdist : edist x y ≤ ENNReal.ofReal r := by
        rw [edist_dist]
        apply ENNReal.ofReal_le_ofReal
        simpa only [K, Metric.mem_closedBall, dist_comm] using hy
      exact (not_le.mpr hr) ((Metric.infEDist_le_edist_of_mem (show y ∈ (U : Set _)ᶜ from hn)).trans hdist)
    have hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)) := by
      apply ContDiff.contDiffOn
      exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (ρ.contDiff.comp ((contDiff_fst.sub contDiff_snd).const_smul ε⁻¹)))
    have hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K := by
      intro p hp
      apply closure_minimal _ Metric.isClosed_closedBall
      intro y hy
      have hρ : ρ (ε⁻¹ • (p - y)) ≠ 0 := by
        intro hz
        apply hy
        simp [H, hz]
      have hle := hρ_support (subset_closure hρ)
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hε)] at hle
      have hpy : ‖p - y‖ ≤ ε := by
        have := mul_le_mul_of_nonneg_left hle hε.le
        simpa only [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_one] using this
      have hp' : dist p x < r - ε := hp
      change dist y x ≤ r
      calc
        dist y x ≤ dist y p + dist p x := dist_triangle _ _ _
        _ ≤ ε + dist p x := add_le_add (by simpa [dist_eq_norm, norm_sub_rev] using hpy) le_rfl
        _ ≤ r := by linarith
    obtain ⟨sections, hsections, hsmooth, _⟩ :=
      HolomorphicAnosov.Analysis.distribution_smooth_fixed_support_family hm hm U P T K
        (isCompact_closedBall x r) hKU H hH hSupport
    refine ⟨(P : Set _), P.isOpen, Metric.mem_ball_self (sub_pos.mpr hεr), ?_⟩
    apply hsmooth.congr_mono ?_ Set.inter_subset_right
    intro p hp
    dsimp [F]
    rw [dite_eq_left hp.1]
    congr 1
    apply TestFunction.ext
    intro y
    rw [hsections p hp.2 y]
    exact Classical.choose_spec (exists_scaled_mollifier_test U ρ hρ_support ε hε p hp.1.2) y
  · intro φ
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist φ.hasCompactSupport
      U.isOpen.isClosed_compl (Set.disjoint_left.2 (fun x hx hxc ↦ hxc (φ.tsupport_subset hx)))
    refine ⟨(r : ℝ), hr, ?_, ?_⟩
    · intro ε hε hεr x hx
      refine ⟨φ.tsupport_subset hx, ?_⟩
      apply lt_of_lt_of_le (show ENNReal.ofReal ε < (r : ENNReal) by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact (ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < r from hr)).2 hεr)
      exact Metric.le_infEDist.mpr (fun y hy ↦ (hsep x hx y hy).le)
    · exact distribution_mollifier_weak_convergence hm U T ρ hρ_nonneg hρ_support hρ_norm κ F hκ hFinside φ
  · intro hbar n hmn i hi ε hε x hx
    have hi' := hderiv ε hε 1 (fun _ ↦ i) x hx
    let j : Fin m := ⟨n + i.val, by omega⟩
    have hj' := hderiv ε hε 1 (fun _ ↦ j) x hx
    simpa only [iteratedFDeriv_one_apply, smul_eq_mul] using
      (show (iteratedFDeriv ℝ 1 (F ε hε) x (fun _ ↦ EuclideanSpace.single i 1) +
        Complex.I * iteratedFDeriv ℝ 1 (F ε hε) x
          (fun _ ↦ EuclideanSpace.single j 1)) / 2 = 0 by
        rw [hi', hj']
        exact hbar n hmn i hi (κ ε hε x hx))

end HolomorphicAnosov.Analysis.Distribution
