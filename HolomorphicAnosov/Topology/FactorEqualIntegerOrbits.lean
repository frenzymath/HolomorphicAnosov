import Mathlib.Topology.Homeomorph.Lemmas
import HolomorphicAnosov.Topology.FactorIntegerRecurrence

namespace HolomorphicAnosov

/-- Equal images determine equal target orbits at every integer time when the target
map is injective. Source: Manning Lemma 6, Step 3. -/
theorem factor_equal_integer_orbits
    {X Y : Type*} [TopologicalSpace X] (F : X ≃ₜ X) (g : Y → Y) (h : X → Y)
    (hsem : ∀ x, h (F x) = g (h x)) (hinj : Function.Injective g)
    (x y : X) (hxy : h x = h y) (j : ℤ) :
    h ((F ^ j) x) = h ((F ^ j) y) := by
  induction j using Int.induction_on with
  | zero => simpa using hxy
  | succ k ih => rw [factor_integer_recurrence F g h hsem, ih,
      factor_integer_recurrence F g h hsem]
  | pred k ih =>
    apply hinj
    rw [← factor_integer_recurrence F g h hsem,
      ← factor_integer_recurrence F g h hsem]
    simpa only [sub_add_cancel] using ih

end HolomorphicAnosov
