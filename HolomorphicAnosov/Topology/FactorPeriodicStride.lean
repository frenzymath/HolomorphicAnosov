import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Ring
import HolomorphicAnosov.Topology.FactorNaturalCovariance

namespace HolomorphicAnosov

/-- A positive target period gives invariance of its source fibre under precisely
qZ source iterates. Forward multiples use the period equation; backward multiples
cancel the q-iterate using target injectivity. Source: Manning Lemma 6, Step 2. -/
theorem factor_periodic_stride
    {X Y : Type*} [TopologicalSpace X] (F : X ≃ₜ X) (g : Y → Y) (h : X → Y)
    (hsem : ∀ x, h (F x) = g (h x)) (hinj : Function.Injective g)
    (q : ℕ) (z : Y) (hz : g^[q] z = z) (x : X) (hx : h x = z) (k : ℤ) :
    h ((F ^ ((q : ℤ) * k)) x) = z := by
  have hstep : ∀ j : ℤ,
      h ((F ^ (j + q)) x) = g^[q] (h ((F ^ j) x)) := by
    intro j
    have hp : (F ^ (j + q)) x = (F ^ q) ((F ^ j) x) := by
      rw [← Homeomorph.mul_apply, ← zpow_natCast F q, ← zpow_add]
      congr 2
      omega
    rw [hp]
    exact factor_natural_covariance F g h hsem q _
  induction k using Int.induction_on with
  | zero => simpa using hx
  | succ k ih =>
    have hp : (q : ℤ) * ((k : ℤ) + 1) = (q : ℤ) * k + q := by ring
    rw [hp, hstep, ih, hz]
  | pred k ih =>
    apply (hinj.iterate q)
    rw [hz]
    rw [← hstep]
    have hp : (q : ℤ) * (-(k : ℤ) - 1) + q = (q : ℤ) * -(k : ℤ) := by ring
    rw [hp]
    exact ih

end HolomorphicAnosov
