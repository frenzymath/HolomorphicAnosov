import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

/-- The algebra step in the source proof: the actual finitely generated group,
with its given operations, admits integer coordinates. Torsion-freeness converts
to injectivity of powers using `(a / b)^k`; the PID basis theorem then supplies
a finite basis of its additive integer module, including the empty basis. -/
theorem finite_abelian_torsionfree_coordinates (G : Type*) [Group G]
    (hfg : Group.FG G) (habelian : ∀ a b : G, a * b = b * a)
    (htorsion : ∀ a : G, ∀ k : ℕ, 0 < k → a ^ k = 1 → a = 1) :
    ∃ r : ℕ, Nonempty (G ≃* Multiplicative (Fin r → ℤ)) := by
  classical
  let comm : CommGroup G := { (inferInstance : Group G) with mul_comm := habelian }
  have : IsMulTorsionFree G := by
    refine ⟨fun k hk a b hab ↦ ?_⟩
    apply div_eq_one.mp
    apply htorsion (a / b) k (Nat.pos_of_ne_zero hk)
    change a ^ k = b ^ k at hab
    rw [div_pow, hab]
    exact div_self' _
  have : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr (GroupFG.iff_add_fg.mp hfg)
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive G)
  exact ⟨r, ⟨AddEquiv.toMultiplicativeRight
    ((b.repr.trans (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin r))).toAddEquiv)⟩⟩

end HolomorphicAnosov
