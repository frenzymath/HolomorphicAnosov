import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Topology.PeriodicPointFromClosedCodeFibre
import HolomorphicAnosov.Topology.ToralBiInfiniteExpansivity
import HolomorphicAnosov.Topology.CodingIntegerCovariance
import HolomorphicAnosov.Topology.FactorIntegerRecurrence
import HolomorphicAnosov.Topology.FactorEqualIntegerOrbits
import HolomorphicAnosov.Topology.FactorPeriodicStride
import HolomorphicAnosov.Topology.IntegralToralMapInjective

namespace HolomorphicAnosov

open Set

/-- Manning's full symbolic fibre deduction from the actual clauses of ONE
retained Bowen coding tuple. Source: Manning Lemma6 pp.427–428 and Bowen
Proposition (6.2) pp.36–37; Steps1–5 of this parent. The coding premise here is
only a private construction interface: the original public theorem must construct
it from its geometric datum, rather than assuming coding or a periodic point.

Choose the proved target expansive margin and the compact uniform-continuity
modulus of h. Take one coding tuple at that mesh. Its target fibre is closed and
nonempty. Integer coding covariance and genuine qZ target-period invariance give
stride invariance. The tuple's original-metric past/future estimates and equal
integer target orbits make each guarded splice stay in the fibre by expansivity.
The checked finite-word/q-block theorem gives a code of positive period q*p;
project its period by actual covariance and keep its original fibre equation. -/
theorem periodic_fibre_from_bowen_coding
    {X : Type*} [MetricSpace X] [CompactSpace X] (F : X ≃ₜ X)
    {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hhyper : ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1)
    (h : X → UnitAddTorus (Fin n)) (hcontinuous : Continuous h)
    (hsem : ∀ x, h (F x) = integralToralMap A (h x)) (honto : Function.Surjective h)
    (hcoding : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (B : Fin N → Fin N → Prop)
      (R : Fin N → Set X) (coding : BowenBasicSetCoding.CodeSpace B → X),
      (∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) ∧
      Continuous coding ∧ Function.Surjective coding ∧
      (∀ a, coding (BowenBasicSetCoding.codeShift B a) = F (coding a)) ∧
      (∀ a b : BowenBasicSetCoding.CodeSpace B, a.val 0 = b.val 0 →
        ∃ c : BowenBasicSetCoding.CodeSpace B,
          (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
          (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) ∧
          (∀ j : ℤ, 0 ≤ j → dist ((F ^ j) (coding c)) ((F ^ j) (coding b)) < ε) ∧
          (∀ j : ℤ, j ≤ 0 → dist ((F ^ j) (coding c)) ((F ^ j) (coding a)) < ε))) :
    ∀ z : UnitAddTorus (Fin n), ∀ q : ℕ, 1 ≤ q →
      (integralToralMap A)^[q] z = z →
      ∃ x : X, h x = z ∧ ∃ r : ℕ, 1 ≤ r ∧ (F : X → X)^[r] x = x := by
  classical
  obtain ⟨e, he, hexp⟩ := integral_toral_biinfinite_expansivity A hhyper
  have huc := CompactSpace.uniformContinuous_of_continuous hcontinuous
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp huc e he
  obtain ⟨N, B, R, coding, hcode, hccont, hcsurj, hcov, hsplice⟩ := hcoding δ hδ
  intro z q hq hz
  let L : Set (BowenBasicSetCoding.CodeSpace B) := {a | h (coding a) = z}
  have hLne : L.Nonempty := by
    obtain ⟨x, hx⟩ := honto z
    obtain ⟨a, ha⟩ := hcsurj x
    exact ⟨a, by change h (coding a) = z; rw [ha, hx]⟩
  have hLclosed : IsClosed L :=
    isClosed_singleton.preimage (hcontinuous.comp hccont)
  have hLshift : ∀ a ∈ L, ∀ k : ℤ, ∃ b ∈ L,
      ∀ j : ℤ, b.val j = a.val ((q : ℤ) * k + j) := by
    intro a ha k
    let b : BowenBasicSetCoding.CodeSpace B :=
      ⟨SymbolicDynamics.FullShift.shift ((q : ℤ) * k) a.val, fun j ↦ by
        simpa only [SymbolicDynamics.FullShift.shift_apply, add_assoc] using
          a.property ((q : ℤ) * k + j)⟩
    refine ⟨b, ?_, fun j ↦ rfl⟩
    change h (coding b) = z
    have hcb := coding_integer_covariance F B R coding hcode a ((q : ℤ) * k)
    change coding b = (F ^ ((q : ℤ) * k)) (coding a) at hcb
    rw [hcb]
    exact factor_periodic_stride F (integralToralMap A) h hsem
      (integral_toral_map_injective A) q z hz (coding a) ha k
  have hLsplice : ∀ a ∈ L, ∀ b ∈ L, a.val 0 = b.val 0 →
      ∃ c ∈ L, (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
        (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) := by
    intro a ha b hb hab
    obtain ⟨c, hpast, hfuture, hdistfuture, hdistpast⟩ := hsplice a b hab
    refine ⟨c, ?_, hpast, hfuture⟩
    change h (coding c) = z
    have htargeteq : h (coding c) = h (coding a) := by
      have heq := hexp
        (fun j ↦ h ((F ^ j) (coding c))) (fun j ↦ h ((F ^ j) (coding a)))
        (factor_integer_recurrence F (integralToralMap A) h hsem (coding c))
        (factor_integer_recurrence F (integralToralMap A) h hsem (coding a))
        (fun j ↦ ?_)
      · simpa only [zpow_zero, Homeomorph.one_apply] using heq
      · by_cases hj : 0 ≤ j
        · have hbeq : h ((F ^ j) (coding b)) = h ((F ^ j) (coding a)) :=
            factor_equal_integer_orbits F (integralToralMap A) h hsem
              (integral_toral_map_injective A) (coding b) (coding a) (hb.trans ha.symm) j
          rw [← hbeq]
          exact (hmod (hdistfuture j hj)).le
        · exact (hmod (hdistpast j (by omega))).le
    exact htargeteq.trans ha
  obtain ⟨a, ha, r, hr, hfix⟩ :=
    periodic_point_from_closed_code_fibre B (F : X → X) coding hcov L hLne hLclosed q
      (by omega) hLshift hLsplice
  exact ⟨coding a, ha, r, hr, hfix⟩


end HolomorphicAnosov
