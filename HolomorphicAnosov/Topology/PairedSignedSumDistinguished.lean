import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
namespace HolomorphicAnosov.Topology

/-- A signed sum whose opposite terms are paired by an involution reduces to
its distinguished unpaired term. Source: Hatcher, Algebraic Topology, proof
of Theorem 2A.1 p.167, cancellation of paired edge classes in the abelianized
fundamental group. Remove the distinguished term; the involution preserves
the remainder, has no fixed points there, and pairs equal labels with opposite
coefficients. The finite involution cancellation theorem makes the remaining
sum zero. No torsion-free assumption on the abelian group is used. -/
theorem pairedSigned_sum_distinguished {I A : Type*} [Fintype I] [AddCommGroup A]
    (d : I) (pair : I → I) (hpair : Function.Involutive pair)
    (hd : pair d = d) (hfree : ∀ i, i ≠ d → pair i ≠ i)
    (sign : I → ℤ) (label : I → A)
    (hsign : ∀ i, i ≠ d → sign (pair i) = -sign i)
    (hlabel : ∀ i, label (pair i) = label i) :
    (∑ i, sign i • label i) = sign d • label d := by
  classical
  have hzero : (∑ i ∈ Finset.univ.erase d, sign i • label i) = 0 := by
    apply Finset.sum_involution (fun i _ ↦ pair i)
    · intro i hi
      rw [hsign i (Finset.mem_erase.mp hi).1, hlabel i, neg_zsmul, add_neg_cancel]
    · intro i hi _
      exact hfree i (Finset.mem_erase.mp hi).1
    · intro i hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi ⊢
      intro h
      apply hi
      exact hpair.injective (h.trans hd.symm)
    · intro i _
      exact hpair i
  have h := Finset.sum_erase_add Finset.univ (fun i ↦ sign i • label i)
    (Finset.mem_univ d)
  simpa [hzero] using h.symm

end HolomorphicAnosov.Topology
