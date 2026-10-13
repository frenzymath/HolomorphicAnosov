import HolomorphicAnosov.Topology.CWFinitePointSubdivision

/-!
# Finite mapping-cone replacement for point-vertex refinement

Source: Fritsch–Piccinini, Cellular Structures in Topology (1990), Lemma 2.3.7,
printed p.67, with the CW attachment construction of pp.62–63. The finite point
subdivision theorem proves the stronger conclusion without needing the supplied
complement subcomplex and disk homeomorphism. This interface retains exactly
its original hypotheses for existing callers.
-/

open _root_.Topology
universe u
namespace HolomorphicAnosov

/-- Finite mapping-cone replacement for one selected characteristic disk.

Proof: apply the finite point subdivision theorem to the interior coordinate a.
Its dimension induction first makes a chosen boundary image a vertex in a lower
cell, then adds the cone peak, radial edge, and cone on the punctured sphere.
Finite carrier composition preserves disjoint open-cell covers, finite fibres,
and the old characteristic maps off a finite set. Substitute the given equality
mapping a to x and unpack these properties into the original interface.
-/
theorem cw_point_vertex_mapping_cone_replacement
    (X : Type u) [TopologicalSpace X] [T2Space X]
    (old : CWComplex (Set.univ : Set X))
    {n : ℕ} (i : @CWComplex.cell X _ Set.univ old n)
    (x : X) (a : Fin n → ℝ)
    (ha : a ∈ Metric.ball (0 : Fin n → ℝ) 1)
    (hax : (@CWComplex.map X _ Set.univ old n i) a = x)
    (A : CWComplex.Subcomplex (Set.univ : Set X))
    (_hA : let _ : CWComplex (Set.univ : Set X) := old
      (A : Set X) = (CWComplex.skeleton (Set.univ : Set X) n : Set X) \
        (@CWComplex.map X _ Set.univ old n i).target)
    (_H : Metric.closedBall (0 : Fin n → ℝ) 1 ≃ₜ
      Metric.closedBall (0 : Fin n → ℝ) 1)
    (_hboundary : Set.MapsTo (@CWComplex.map X _ Set.univ old n i)
      (Metric.sphere (0 : Fin n → ℝ) 1) (A : Set X)) :
    ∃ new : CWComplex (Set.univ : Set X),
      let oldCell := @CWComplex.cell X _ Set.univ old
      let oldMap := @CWComplex.map X _ Set.univ old
      let newCell := @CWComplex.cell X _ Set.univ new
      let newMap := @CWComplex.map X _ Set.univ new
      ∃ (changed : Set (Σ k, oldCell k))
        (carrier : (Σ k, newCell k) → (Σ k, oldCell k)),
        changed.Finite ∧
        (∃ v : newCell 0, (newMap 0 v).target = {x}) ∧
        (∀ e : Σ k, newCell k,
          e.1 ≤ (carrier e).1 ∧
          (newMap e.1 e.2).target ⊆ (oldMap (carrier e).1 (carrier e).2).target) ∧
        (∀ e : Σ k, oldCell k,
          (oldMap e.1 e.2).target =
            ⋃ (f : Σ k, newCell k) (_ : carrier f = e),
              (newMap f.1 f.2).target) ∧
        (∀ e : Σ k, oldCell k,
          Set.Finite {f : Σ k, newCell k | carrier f = e}) ∧
        (∀ (k : ℕ) (j : oldCell k),
          (⟨k, j⟩ : Σ k, oldCell k) ∉ changed →
          ∃ q : newCell k, carrier ⟨k, q⟩ = ⟨k, j⟩ ∧
            Set.EqOn (newMap k q) (oldMap k j)
              (Metric.closedBall (0 : Fin k → ℝ) 1)) := by
  obtain ⟨new,R,⟨v,hv⟩,_⟩ := cw_point_vertex_finite_refinement n old i a ha
  refine ⟨new,R.changed,R.carrier,R.finite_changed,⟨v,?_⟩,
    (fun e ↦ ⟨R.dimension e,R.subset e⟩),R.cover,R.finite_fiber,R.unchanged⟩
  simpa only [hax] using hv

end HolomorphicAnosov

