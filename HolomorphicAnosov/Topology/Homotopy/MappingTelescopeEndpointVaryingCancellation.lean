import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeHomotopicBondMap

import HolomorphicAnosov.Topology.Homotopy.ParameterizedPathCancellation

/-! # Endpoint-varying cylinder cancellation for mapping telescopes

Source: Hatcher, Algebraic Topology, Proposition A.11(1), p.528, and
Proposition 0.18, p.16. The explicit comparison composite on each cylinder is
(P*Q)*Q⁻¹, where P is the cylinder homotopy and Q is the attaching homotopy
mapped into the next level. Parameterized path cancellation contracts this to
P while fixing both endpoints. Curry its compact time interval, descend the
resulting continuous map into C(I,telescope) through the telescope quotient,
and uncurry. This proves joint continuity without any condition on the levels.
-/

universe u

namespace HolomorphicAnosov.MappingTelescope.Sequence
open ContinuousMap unitInterval
open HolomorphicAnosov.HomotopyCancellation
noncomputable section

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
variable {f g : ∀ n, C(X n, X (n + 1))}
private def bondInLevel (H : ∀ n, (f n).Homotopy (g n)) (n : ℕ) :=
  (Homotopy.refl (level f (n+1))).comp (H n)

private theorem composite_cylinder (H : ∀ n, (f n).Homotopy (g n))
    (n : ℕ) (t : I) (x : X n) :
    homotopicBondMap (fun n ↦ (H n).symm) (homotopicBondMap H (cylinder f n (x,t))) =
      (((cylinderHomotopy f n).trans (bondInLevel H n)).trans
        (bondInLevel H n).symm) (t,x) := by
  change homotopicBondMap (fun n ↦ (H n).symm)
    (((cylinderHomotopy g n).trans
      ((Homotopy.refl (level g (n+1))).comp (H n).symm)) (t,x)) = _
  rw [Homotopy.trans_apply, Homotopy.trans_apply]
  split_ifs
  · change ((cylinderHomotopy f n).trans
      ((Homotopy.refl (level f (n+1))).comp (H n).symm.symm)) _ = _
    rw [Homotopy.symm_symm]
    rfl
  · change homotopicBondMap (fun n ↦ (H n).symm) (level g (n+1) _) = level f (n+1) _
    exact homotopicBondMap_level _ _ _

private def rawCancel (H : ∀ n, (f n).Homotopy (g n)) : C(Cylinder X, C(I, telescope f)) :=
  ⟨fun z ↦ ((cancelFamily (cylinderHomotopy f z.1) (bondInLevel H z.1)).toContinuousMap.comp
    ContinuousMap.prodSwap).curry (z.2.2,z.2.1),
    continuous_sigma fun n ↦
      (((cancelFamily (cylinderHomotopy f n) (bondInLevel H n)).toContinuousMap.comp
        ContinuousMap.prodSwap).curry).continuous.comp continuous_swap⟩

private theorem rawCancel_bottom (H : ∀ n, (f n).Homotopy (g n))
    (n : ℕ) (x : X n) (s : I) : rawCancel H ⟨n,(x,0)⟩ s = level f n x := by
  exact HomotopyRel.eq_snd (cancelFamily (cylinderHomotopy f n) (bondInLevel H n)) s
    (Or.inl rfl)
private theorem rawCancel_top (H : ∀ n, (f n).Homotopy (g n))
    (n : ℕ) (x : X n) (s : I) : rawCancel H ⟨n,(x,1)⟩ s = level f (n+1) (f n x) := by
  exact (HomotopyRel.eq_snd (cancelFamily (cylinderHomotopy f n) (bondInLevel H n)) s
    (Or.inr rfl)).trans ((cylinderHomotopy f n).apply_one x)

private theorem rawCancel_respects (H : ∀ n, (f n).Homotopy (g n)) :
    ∀ a b, setoid f a b → rawCancel H a = rawCancel H b := by
  intro a b hab
  induction hab with
  | rel a b hab =>
    rcases hab with ⟨n,x,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ <;>
      ext s <;> simp only [rawCancel_top, rawCancel_bottom]
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h k => exact h.trans k

private def quotientCancel (H : ∀ n, (f n).Homotopy (g n)) : C(telescope f, C(I,telescope f)) :=
  ⟨Quotient.lift (rawCancel H) (rawCancel_respects H),
    (rawCancel H).continuous.quotient_lift (rawCancel_respects H)⟩


private def inverseCancellation (H : ∀ n, (f n).Homotopy (g n)) :
    ((homotopicBondMap (fun n ↦ (H n).symm)).comp (homotopicBondMap H)).HomotopyRel
      (ContinuousMap.id (telescope f)) (⋃ n, Set.range (level f n)) where
  toFun z := quotientCancel H z.2 z.1
  continuous_toFun := (quotientCancel H).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    induction z using Quotient.inductionOn with | h z =>
      rcases z with ⟨n,x,t⟩
      change cancelFamily (cylinderHomotopy f n) (bondInLevel H n) (0,(t,x)) = _
      rw [HomotopyWith.apply_zero]
      exact (composite_cylinder H n t x).symm
  map_one_left z := by
    induction z using Quotient.inductionOn with | h z =>
      rcases z with ⟨n,x,t⟩
      change cancelFamily (cylinderHomotopy f n) (bondInLevel H n) (1,(t,x)) = _
      rw [HomotopyWith.apply_one]
      rfl
  prop' s z hz := by
    obtain ⟨n,x,rfl⟩ := Set.mem_iUnion.mp hz
    change rawCancel H ⟨n,(x,0)⟩ s = _
    rw [rawCancel_bottom]
    simp

/-- The homotopic-bond comparisons have inverse homotopies relative to all
canonical levels. Source: Hatcher, Proposition A.11(1), p.528, and Proposition
0.18, p.16.

On each cylinder the comparison composite is (P*Q)*Q⁻¹: both comparison maps
fix the levels, and reversing the input attaching homotopy twice gives Q.
The continuous family contraction `cancelFamily P Q` ends at P and fixes its
endpoints. Its top is level(n+1)(f_n x), equal to the next cylinder's bottom,
so induction on the generated seam relation gives a well-defined quotient
map into C(I,telescope). Quotient continuity and continuous evaluation on the
compact interval give the required jointly continuous homotopy. Its initial
map is the comparison composite; its final map is the identity. Its value on
each bottom level is constant, proving relativity. Repeat with the reversed
bond homotopies for the other composite. This also covers empty level spaces.
-/
theorem exists_endpoint_varying_cylinder_cancellation
    (H : ∀ n, (f n).Homotopy (g n)) :
    ∃ _F : ((homotopicBondMap (fun n ↦ (H n).symm)).comp (homotopicBondMap H)).HomotopyRel
        (ContinuousMap.id (telescope f)) (⋃ n, Set.range (level f n)),
      ∃ _G : ((homotopicBondMap H).comp (homotopicBondMap (fun n ↦ (H n).symm))).HomotopyRel
        (ContinuousMap.id (telescope g)) (⋃ n, Set.range (level g n)), True := by
  refine ⟨inverseCancellation H, ?_, trivial⟩
  simpa only [Homotopy.symm_symm] using inverseCancellation (fun n ↦ (H n).symm)

end
end HolomorphicAnosov.MappingTelescope.Sequence
