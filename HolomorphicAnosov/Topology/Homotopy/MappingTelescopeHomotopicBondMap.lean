import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeSequence

/-!
# The comparison map for homotopic telescope bonds

Source: Hatcher, *Algebraic Topology*, proof of Proposition A.11, p.528,
fact (1), and Proposition 0.18, p.16. The cylinder follows the target cylinder
and then the reversed attaching homotopy in the next level.
-/

universe u

namespace HolomorphicAnosov.MappingTelescope.Sequence

open ContinuousMap

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
variable {f g : ∀ n, C(X n, X (n + 1))}

/-- The explicit continuous comparison map for a family of homotopic bonds.
Source: Hatcher, Proposition A.11(1), p.528, via the attaching-map construction
of Proposition 0.18, p.16. On cylinder `n`, concatenate its canonical homotopy
in `telescope g` with `H n` reversed and mapped into level `n+1`. Its bottom is
level `n`, and its top is level `n+1` composed with `f n`; hence it respects each
seam of `telescope f`. Induction on the generated relation and quotient descent
give the continuous map. This construction works for empty spaces as well.
-/
noncomputable def homotopicBondMap (H : ∀ n, (f n).Homotopy (g n)) : C(telescope f, telescope g) := by
  let K : ∀ n, (level g n).Homotopy ((level g (n + 1)).comp (f n)) := fun n ↦
    (cylinderHomotopy g n).trans ((Homotopy.refl (level g (n + 1))).comp (H n).symm)
  let raw : C(Cylinder X, telescope g) :=
    ⟨fun z ↦ K z.1 (z.2.2, z.2.1),
      continuous_sigma fun n ↦ (K n).continuous.comp continuous_swap⟩
  have respects : ∀ a b, setoid f a b → raw a = raw b := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · change K n (1, x) = K (n + 1) (0, f n x)
        simp
      · change K (n + 1) (0, f n x) = K n (1, x)
        simp
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  exact ⟨Quotient.lift raw respects, raw.continuous.quotient_lift respects⟩

/-- The homotopic-bond comparison fixes every canonical level.
Source: Hatcher, Proposition A.11(1), p.528. On the bottom of each cylinder the
concatenated homotopy equals its initial map, which is the same indexed level.
-/
@[simp] theorem homotopicBondMap_level (H : ∀ n, (f n).Homotopy (g n))
    (n : ℕ) (x : X n) : homotopicBondMap H (level f n x) = level g n x := by
  change ((cylinderHomotopy g n).trans
    ((Homotopy.refl (level g (n + 1))).comp (H n).symm)) (0, x) = _
  exact Homotopy.apply_zero _ _

end HolomorphicAnosov.MappingTelescope.Sequence
