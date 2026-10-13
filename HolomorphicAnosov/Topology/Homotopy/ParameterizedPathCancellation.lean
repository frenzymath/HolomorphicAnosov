import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! # Cancellation in continuous families of paths

The path associativity, backtracking contraction, and right identity homotopies
are those of Mathlib's fundamental groupoid. Evaluate their composite on the
fixed paths `t ↦ t/2` and `t ↦ (t+1)/2` in the unit interval, then compose with
any continuous family of concatenated paths. This yields joint continuity
without any local compactness assumption on the parameter space.
-/

open ContinuousMap unitInterval
namespace HolomorphicAnosov.HomotopyCancellation
noncomputable section
private def half : I := ⟨1/2, by norm_num⟩
private def first : Path (0 : I) half where
  toFun t := ⟨(t : ℝ)/2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  continuous_toFun := by fun_prop
  source' := by ext; norm_num
  target' := by ext; norm_num [half]
private def second : Path half (1 : I) where
  toFun t := ⟨((t : ℝ)+1)/2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  continuous_toFun := by fun_prop
  source' := by ext; norm_num [half]
  target' := by ext; norm_num
private def cancel : ((first.trans second).trans second.symm).Homotopy first :=
  (Path.Homotopy.transAssoc first second second.symm).trans
    (((Path.Homotopy.refl first).hcomp (Path.Homotopy.reflTransSymm second).symm).trans
      (Path.Homotopy.transRefl first))

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
variable {a b c : C(A,B)}
private theorem trans_first (P : a.Homotopy b) (Q : b.Homotopy c) (t : I) (x : A) :
    (P.trans Q) (first t, x) = P (t,x) := by
  rw [Homotopy.trans_apply]
  have ht : ((first t : I) : ℝ) ≤ 1/2 := by change (t:ℝ)/2 ≤ 1/2; linarith [t.2.2]
  simp only [ht, dite_true]
  congr 2
  apply Subtype.ext
  change 2 * ((t:ℝ)/2) = t
  ring
private theorem trans_second (P : a.Homotopy b) (Q : b.Homotopy c) (t : I) (x : A) :
    (P.trans Q) (second t, x) = Q (t,x) := by
  rw [Homotopy.trans_apply]
  split_ifs with ht
  · have hz : t = 0 := by apply Subtype.ext; change (t:ℝ) = 0; change ((t:ℝ)+1)/2 ≤ 1/2 at ht; linarith [t.2.1]
    subst t
    norm_num [second, half]
  · congr 2
    apply Subtype.ext
    change 2 * (((t:ℝ)+1)/2) - 1 = t
    ring

private theorem cancel_zero (P : a.Homotopy b) (Q : b.Homotopy c) (t : I) (x : A) :
    (P.trans Q) (cancel (0,t), x) = ((P.trans Q).trans Q.symm) (t,x) := by
  rw [HomotopyWith.apply_zero]
  change (P.trans Q) (((first.trans second).trans second.symm) t, x) = _
  rw [Path.trans_apply]
  conv_rhs => rw [Homotopy.trans_apply]
  split_ifs with ht
  · rw [Path.trans_apply]
    conv_rhs => rw [Homotopy.trans_apply]
    split_ifs
    · exact trans_first P Q _ x
    · exact trans_second P Q _ x
  · exact trans_second P Q _ x

/-- A continuous family of paths followed by a path and its reversal contracts,
relative to both endpoints, to the first family.

Proof: let p(t)=t/2 and q(t)=(t+1)/2 in I. Mathlib's associativity homotopy,
the reverse of `reflTransSymm q` horizontally composed with the constant
homotopy on p, and `transRefl p` give K:((p*q)*q⁻¹)~p relative endpoints.
For given families P and Q, evaluate (P*Q)(K(s,t),x). This is jointly continuous
as a composite of continuous maps. The identities (P*Q)(p(t),x)=P(t,x) and
(P*Q)(q(t),x)=Q(t,x) identify its initial and final maps and fixed endpoints.
Source: Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic, lines 62–165;
Hatcher, Algebraic Topology, Proposition 0.18, p.16 (attaching-map cancellation).
-/
def cancelFamily (P : a.Homotopy b) (Q : b.Homotopy c) :
    ((P.trans Q).trans Q.symm).toContinuousMap.HomotopyRel P.toContinuousMap
      {z | z.1 = 0 ∨ z.1 = 1} where
  toFun z := (P.trans Q) (cancel (z.1,z.2.1), z.2.2)
  continuous_toFun := (P.trans Q).continuous.comp
    ((cancel.toHomotopy.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      continuous_snd.snd)
  map_zero_left z := cancel_zero P Q z.1 z.2
  map_one_left z := by
    dsimp only
    rw [HomotopyWith.apply_one]
    change (P.trans Q) (first z.1, z.2) = _
    exact trans_first P Q _ _
  prop' s z hz := by
    rcases z with ⟨t,x⟩
    change t = 0 ∨ t = 1 at hz
    rcases hz with hz | hz
    · subst t
      change (P.trans Q) (cancel (s,0),x) = _
      simp
    · subst t
      change (P.trans Q) (cancel (s,1),x) = _
      rw [Path.Homotopy.target]
      change (P.trans Q) (first 1,x) = _
      rw [trans_first]
      simp


/-- Existence of endpoint-fixed cancellation for an arbitrary continuous
parameter family. The explicit witness is `cancelFamily`, whose construction
and continuity proof are given above. -/
theorem parameterized_cancellation (P : a.Homotopy b) (Q : b.Homotopy c) :
    Nonempty (((P.trans Q).trans Q.symm).toContinuousMap.HomotopyRel P.toContinuousMap
      {z | z.1 = 0 ∨ z.1 = 1}) := ⟨cancelFamily P Q⟩

end
end HolomorphicAnosov.HomotopyCancellation
