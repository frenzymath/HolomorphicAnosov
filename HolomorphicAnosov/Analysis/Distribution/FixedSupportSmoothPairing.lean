import HolomorphicAnosov.Analysis.Distribution.FixedSupportJetContinuity
import HolomorphicAnosov.Analysis.Distribution.FixedSupportContinuousPairing
import HolomorphicAnosov.Analysis.Distribution.FixedSupportParameterDerivativeTests
import HolomorphicAnosov.Analysis.Distribution.FixedSupportFiniteOrderBound
import HolomorphicAnosov.Analysis.TestFunctionFixedSupport
import HolomorphicAnosov.Analysis.Distribution.FixedSupportPairingSmoothNonempty

/-!
# Smooth parameter pairing for fixed-support test families

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Proposition 6.3, pp. 68–69.
This is the parameter-differentiation part of the fixed-support family theorem.
-/

noncomputable section
open Set
open scoped ContDiff
namespace HolomorphicAnosov.Analysis

/-- At order zero, the prescribed section itself realizes the parameter derivative and its
continuous distribution pairing. -/
theorem fixed_support_pairing_zero_order_local
    {m k : ℕ} (_hm : 0 < m) (_hk : 0 < k)
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (_hK : IsCompact K) (_hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (_hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (_hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K)
    (sections : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤)
    (hSections : ∀ p ∈ P, ∀ y, sections p y = H p y)
    (p : EuclideanSpace ℝ (Fin k)) (hp : p ∈ P) :
    ∃ differentiatedSection : TestFunction U ℂ ⊤,
      (∀ y, differentiatedSection y =
        iteratedFDerivWithin ℝ 0 (fun q ↦ H q y) (P : Set _) p ([] : List (EuclideanSpace ℝ (Fin k))).get) ∧
      iteratedFDerivWithin ℝ 0 (fun q ↦ T (sections q))
        (P : Set _) p ([] : List (EuclideanSpace ℝ (Fin k))).get = T differentiatedSection := by
  refine ⟨sections p, ?_, ?_⟩
  · intro y
    simpa using hSections p hp y
  · simp

/-- A continuous distribution pairs smoothly with a fixed-support family, and real
parameter derivatives commute with pairing.

Source: Dyatlov, *Lecture notes for 18.155: distributions, elliptic regularity, and
applications to PDEs* (2 October 2026), Proposition 6.3, pp. 68–69, including its
proper-support alternative. The explicit Fréchet and LF-topology interpretation is
spelled out below. The representatives `sections` are prescribed only on the open `P`.

Proof: every spatial and parameter derivative of `H` vanishes outside `K`: outside
that closed set, all sections vanish on a common spatial neighborhood for parameters
in `P`. On `U`, joint smoothness makes these derivatives smooth; the open cover
`U ∪ Kᶜ` gives smooth zero extensions, hence differentiated test sections supported
in `K`. Restriction of `T` along the continuous fixed-support inclusion gives a bound
by finitely many derivative seminorms, by `distribution_fixed_support_finite_order_bound`.
Take the maximum of the finitely many orders in that bound. Spatial partial derivatives
and Fréchet derivatives of each order control one another by finite coordinate expansion.

Fix a closed parameter ball contained in `P`. Each mixed derivative is uniformly
continuous on its product with `K`. Therefore every spatial derivative seminorm, through
the controlling order, of the difference of two nearby parameter sections tends to zero.
The finite-order bound proves continuity of the paired section and of every paired
parameter derivative, exactly as equations (6.7)–(6.8).

For a small parameter increment `h`, apply the fundamental theorem of calculus along
`p + t • h`, for `0 ≤ t ≤ 1`, to each relevant mixed spatial derivative. Subtract the
linear term at `p`. Uniform continuity on the compact product bounds the remainder in
each controlling seminorm by `‖h‖ * ω(‖h‖)`, where `ω(r)` tends to zero. Applying the
finite-order bound proves that the real Fréchet derivative of the pairing is the pairing
of the parameter derivative. Its coefficients are the continuous paired coordinate
partials, so this derivative is continuous. Repeat with every parameter derivative.
Induction using `contDiffOn_succ_iff_fderiv_of_isOpen` gives every finite regularity
order, hence `ContDiffOn ℝ ∞`. Iterating the derivative identity gives the displayed
iterated Fréchet formula; joint smoothness permits the coordinate ordering used by the
list of directions. At order zero the differentiated section is the original section.
All derivatives within `P` agree with ordinary derivatives at its points because `P`
is open. Values of `sections` outside `P` consequently have no effect. Empty `P` gives
vacuous assertions; empty `K` or `U` gives zero sections and pairings. -/
theorem distribution_pairing_smooth_on_fixed_support
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K)
    (sections : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤)
    (hSections : ∀ p ∈ P, ∀ y, sections p y = H p y) :
    ContDiffOn ℝ ∞ (fun p ↦ T (sections p)) (P : Set _) ∧
    (∀ (α : Fin k → ℕ) (p : EuclideanSpace ℝ (Fin k)), p ∈ P →
      let directions := (List.finRange k).flatMap
        (fun i ↦ List.replicate (α i) (EuclideanSpace.single i (1 : ℝ)))
      ∃ differentiatedSection : TestFunction U ℂ ⊤,
        (∀ y, differentiatedSection y =
          iteratedFDerivWithin ℝ directions.length (fun q ↦ H q y) (P : Set _) p
            directions.get) ∧
        iteratedFDerivWithin ℝ directions.length (fun q ↦ T (sections q))
          (P : Set _) p directions.get = T differentiatedSection) := by
  have hzero_order (p : EuclideanSpace ℝ (Fin k)) (hp : p ∈ P) :
      ∃ differentiatedSection : TestFunction U ℂ ⊤,
        (∀ y, differentiatedSection y =
          iteratedFDerivWithin ℝ 0 (fun q ↦ H q y) (P : Set _) p
            ([] : List (EuclideanSpace ℝ (Fin k))).get) ∧
        iteratedFDerivWithin ℝ 0 (fun q ↦ T (sections q))
          (P : Set _) p ([] : List (EuclideanSpace ℝ (Fin k))).get =
          T differentiatedSection :=
    fixed_support_pairing_zero_order_local hm hk U P T K hK hKU H hH hSupport
      sections hSections p hp
  have hContinuous : ContinuousOn (fun p ↦ T (sections p)) (P : Set _) :=
    distribution_pairing_continuous_on_fixed_support U P T K hK hKU H hH hSupport
      sections hSections
  by_cases hPempty : (P : Set (EuclideanSpace ℝ (Fin k))) = ∅
  · constructor
    · simp [hPempty]
    · intro α p hp
      have hp' : p ∈ (P : Set (EuclideanSpace ℝ (Fin k))) := hp
      rw [hPempty] at hp'
      exact hp'.elim
  · exact distribution_pairing_smooth_on_fixed_support_nonempty hm hk U P
      (Set.nonempty_iff_ne_empty.mpr hPempty) T K hK hKU H hH hSupport sections hSections

end HolomorphicAnosov.Analysis
