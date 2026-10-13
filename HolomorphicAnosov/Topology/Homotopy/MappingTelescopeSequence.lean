import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.ContinuousOn

/-!
# Mapping telescopes of sequences

Source: Hatcher, *Algebraic Topology*, proof of Proposition A.11, p. 528,
definition before facts (1)–(3). Translate the slab `[n,n+1]` to `[0,1]` while
retaining its summand label. The carriers below are actual endpoint-generated
quotients with Mathlib's coinduced quotient topology, without CW assumptions.
This module defines both the varying-family and self-map carriers; the constant-family
comparison uses the concrete self-map definition below.
-/

namespace HolomorphicAnosov.MappingTelescope

universe u

/-- The real interval used in each cylinder. Source: Hatcher, A.11, p. 528. -/
abbrev TelescopeInterval := unitInterval

variable {P : Type u} [TopologicalSpace P]

/-- The raw constant-sequence cylinders, with product topology.
Source: Hatcher, A.11, p. 528, specialized to a self-map. -/
abbrev TelescopeCylinder (P : Type u) := ℕ × (P × TelescopeInterval)

/-- Exactly the two orientations of the endpoint seam for a self-map.
Source: Hatcher, A.11, p. 528. -/
def telescopeEdge (g : C(P, P)) (a b : TelescopeCylinder P) : Prop :=
  ∃ (n : ℕ) (x : P),
    (a = (n, (x, 1)) ∧ b = (n + 1, (g x, 0))) ∨
      (b = (n, (x, 1)) ∧ a = (n + 1, (g x, 0)))

/-- The equivalence relation generated only by the displayed self-map seams.
Source: Hatcher, A.11, p. 528; Mathlib `Relation.EqvGen.setoid`. -/
def telescopeSetoid (g : C(P, P)) : Setoid (TelescopeCylinder P) :=
  Relation.EqvGen.setoid (telescopeEdge g)

/-- The constant-sequence telescope. Its topology is the actual quotient topology.
Source: Hatcher, A.11, p. 528; Mathlib `instTopologicalSpaceQuotient`. -/
def telescope (g : C(P, P)) := Quotient (telescopeSetoid g)

instance (g : C(P, P)) : TopologicalSpace (telescope g) :=
  instTopologicalSpaceQuotient

/-- The canonical projection of the constant-sequence cylinders.
Source: Hatcher, A.11, p. 528; Mathlib `continuous_quotient_mk'`. -/
def telescopeQuotient (g : C(P, P)) : C(TelescopeCylinder P, telescope g) :=
  ⟨@Quotient.mk' _ (telescopeSetoid g), continuous_quotient_mk'⟩

/-- The bottom level of the constant-sequence cylinder labelled `n`.
Source: Hatcher, A.11, p. 528. -/
def telescopeLevel (g : C(P, P)) (n : ℕ) : C(P, telescope g) :=
  ⟨fun x ↦ telescopeQuotient g (n, (x, 0)),
    (telescopeQuotient g).continuous.comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))⟩

namespace Sequence

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]

/-- The topological disjoint union of the actual varying-space cylinders.
Source: Hatcher, A.11, p. 528; Mathlib's topological sigma construction. -/
abbrev Cylinder (X : ℕ → Type u) := Σ n, X n × TelescopeInterval

/-- The seam identifies only the top of cylinder `n` with its image at the next bottom.
Source: Hatcher, A.11, p. 528. -/
def edge (f : ∀ n, C(X n, X (n + 1))) (a b : Cylinder X) : Prop :=
  ∃ (n : ℕ) (x : X n),
    (a = ⟨n, (x, 1)⟩ ∧ b = ⟨n + 1, (f n x, 0)⟩) ∨
      (b = ⟨n, (x, 1)⟩ ∧ a = ⟨n + 1, (f n x, 0)⟩)

/-- The exact equivalence closure of the sequence's endpoint generators.
Source: Hatcher, A.11, p. 528; Mathlib `Relation.EqvGen.setoid`. -/
def setoid (f : ∀ n, C(X n, X (n + 1))) : Setoid (Cylinder X) :=
  Relation.EqvGen.setoid (edge f)

/-- The genuine mapping telescope of a sequence, with no extra equivalence hypotheses.
Source: Hatcher, A.11, p. 528; Mathlib `Quotient`. -/
def telescope (f : ∀ n, C(X n, X (n + 1))) := Quotient (setoid f)

instance (f : ∀ n, C(X n, X (n + 1))) : TopologicalSpace (telescope f) :=
  instTopologicalSpaceQuotient

/-- The continuous quotient projection from the disjoint union of cylinders.
Source: Hatcher, A.11, p. 528; Mathlib `continuous_quotient_mk'`. -/
def quotient (f : ∀ n, C(X n, X (n + 1))) : C(Cylinder X, telescope f) :=
  ⟨@Quotient.mk' _ (setoid f), continuous_quotient_mk'⟩

/-- The canonical continuous map of cylinder `n` into the telescope; no injectivity asserted.
Source: Hatcher, A.11, p. 528. -/
def cylinder (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) :
    C(X n × TelescopeInterval, telescope f) :=
  ⟨fun z ↦ quotient f ⟨n, z⟩, (quotient f).continuous.comp continuous_sigmaMk⟩

/-- The bottom level of a sequence cylinder. Source: Hatcher, A.11, p. 528. -/
def level (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : C(X n, telescope f) :=
  ⟨fun x ↦ cylinder f n (x, 0),
    (cylinder f n).continuous.comp (continuous_id.prodMk continuous_const)⟩

/-- The top level of a sequence cylinder. Source: Hatcher, A.11, p. 528. -/
def levelTop (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : C(X n, telescope f) :=
  ⟨fun x ↦ cylinder f n (x, 1),
    (cylinder f n).continuous.comp (continuous_id.prodMk continuous_const)⟩

/-- The endpoint seam in the quotient. Source: Hatcher, A.11, p. 528.

Proof: the representatives `(n,(x,1))` and `(n+1,(f n x,0))` are a forward
generator, witnessed by `n,x` and the two reflexive equalities. Insert that
generator using `Relation.EqvGen.rel`, then apply `Quotient.sound`.
DAG: `topo.mapping_telescope_sequence_carrier_g8`, endpoint-seam step.
-/
theorem levelTop_eq (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) (x : X n) :
    levelTop f n x = level f (n + 1) (f n x) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ ⟨n, x, Or.inl ⟨rfl, rfl⟩⟩

/-- The actual cylinder gives a homotopy to the next level composed with the bonding map.
Source: Hatcher, A.11, p. 528. Its endpoint proof uses the named seam theorem. -/
def cylinderHomotopy (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) :
    ContinuousMap.Homotopy (level f n) ((level f (n + 1)).comp (f n)) where
  toFun p := cylinder f n (p.2, p.1)
  continuous_toFun := (cylinder f n).continuous.comp (continuous_snd.prodMk continuous_fst)
  map_zero_left _ := rfl
  map_one_left x := levelTop_eq f n x

/-- Raw reindexing of the constant-family cylinders, with its actual two inverse functions.
Source: Hatcher, A.11, p. 528; Mathlib `Equiv.sigmaEquivProd` and the sigma/discrete
product continuity criteria. -/
def constantCylinderHomeomorph (P : Type u) [TopologicalSpace P] :
    Cylinder (fun _ ↦ P) ≃ₜ TelescopeCylinder P where
  toFun a := (a.1, a.2)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_sigma (fun _ ↦ continuous_const.prodMk continuous_id)
  continuous_invFun := continuous_prod_of_discrete_left.mpr
    (fun n ↦ continuous_sigmaMk (σ := fun _ : ℕ ↦ P × TelescopeInterval) (i := n))

/-- Raw reindexing preserves exactly the generated endpoint equivalence relations.
Source: Hatcher, A.11, p. 528, and the construction in the current DAG node.

Proof: on a forward or reverse generator, the reindexing sends the two sigma
representatives to the identical product coordinates. Thus each generator
maps to the corresponding generator with the same `n,x` witnesses. Induction
on `EqvGen` transports the rel, refl, symm, and trans constructors, proving
the forward implication. Apply the same argument to the inverse reindexing
for the reverse implication, then use its two inverse equations.
DAG: `topo.mapping_telescope_sequence_carrier_g8`, constant-relation steps.
-/
theorem constant_relation_iff (g : C(P, P)) (a b : Cylinder (fun _ ↦ P)) :
    setoid (fun _ ↦ g) a b ↔
      telescopeSetoid g (constantCylinderHomeomorph P a) (constantCylinderHomeomorph P b) := by
  constructor
  · intro h
    change Relation.EqvGen (edge (fun _ ↦ g)) a b at h
    change Relation.EqvGen (telescopeEdge g)
      (constantCylinderHomeomorph P a) (constantCylinderHomeomorph P b)
    induction h with
    | refl => exact .refl _
    | symm a b h ih => exact .symm _ _ ih
    | trans a b c hab hbc ihab ihbc => exact .trans _ _ _ ihab ihbc
    | rel a b h =>
        rcases h with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact .rel _ _ ⟨n, x, Or.inl ⟨rfl, rfl⟩⟩
        · exact .rel _ _ ⟨n, x, Or.inr ⟨rfl, rfl⟩⟩
  · have backward : ∀ (c d : TelescopeCylinder P), Relation.EqvGen (telescopeEdge g) c d →
        Relation.EqvGen (edge (fun _ ↦ g))
          ((constantCylinderHomeomorph P).symm c) ((constantCylinderHomeomorph P).symm d) := by
      intro c d h
      induction h with
      | refl => exact .refl _
      | symm c d h ih => exact .symm _ _ ih
      | trans c d e hcd hde ihcd ihde => exact .trans _ _ _ ihcd ihde
      | rel c d h =>
          rcases h with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          · exact .rel _ _ ⟨n, x, Or.inl ⟨rfl, rfl⟩⟩
          · exact .rel _ _ ⟨n, x, Or.inr ⟨rfl, rfl⟩⟩
    exact backward _ _

/-- The explicit quotient reindexing identifies the constant sequence with the self-map telescope.
Source: Hatcher, A.11, p. 528; Mathlib `Homeomorph.Quotient.congr`,
`Topology/Homeomorph/Quotient.lean:46–48`, DAG `mathlib.homeomorph_quotient_congr_g2`.
This two-carrier constructor applies to the concrete raw reindexing homeomorphism and the
generated-relation equivalence. Only that relation proof is postponed; both quotient functions,
their inverse equations, and their continuity fields are supplied by the constructor. -/
def constantHomeomorph (g : C(P, P)) :
    telescope (fun _ ↦ g) ≃ₜ HolomorphicAnosov.MappingTelescope.telescope g :=
  Homeomorph.Quotient.congr (constantCylinderHomeomorph P) (constant_relation_iff g)

end Sequence
end HolomorphicAnosov.MappingTelescope
