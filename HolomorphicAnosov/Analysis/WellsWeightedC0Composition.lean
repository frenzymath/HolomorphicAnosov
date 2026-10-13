import HolomorphicAnosov.Analysis.WeightedC0Lipschitz
import HolomorphicAnosov.Analysis.WeightedC0ContDiff
import HolomorphicAnosov.Analysis.WeightedC0DerivativeFormula

/-!
# Weighted composition on the Banach space of null sequences

Source: John C. Wells, *Invariant manifolds of non-linear operators*, Pacific Journal of
Mathematics 62(1) (1976), pp. 287–288, Proposition and equation (1).

`C₀(ℕ,E)` carries Mathlib's genuine supremum norm and complete normed-space structure.
The discrete domain `ℕ` identifies vanishing at infinity with convergence of sequences to zero.
A map given on an open ball is represented by a total function, with every hypothesis and
conclusion restricted to that same ball. Its arbitrary outside values are immaterial.
-/

open scoped ContDiff ZeroAtInfty

namespace HolomorphicAnosov.Analysis

/-- Wells's weighted composition theorem for real Banach spaces, on the original open ball.

John C. Wells, Invariant manifolds of non-linear operators, Pacific Journal of
Mathematics62(1)(1976),285–293; publisher cover/metadata says Invariant manifolds on non-linear
operators. Definition of c0(E) and C_λf, printedp287/PDF4; Proposition and written
finite-head/tail induction, printedp288/PDF5, equation(1). The source states the centered
Lipschitz C^r composition assertion; this node restricts it to the actual open common-domain ball,
without extending f outside its given domain.

The order `r : ℕ∞` is a positive integer or smooth infinity, coerced into Mathlib's
`ℕ∞ω`; it does not include the outer analytic order. The total representative `C` is specified
on the entire original ball by its coordinate formula. No condition is imposed outside that
ball. The within derivatives on these open balls are the ordinary Fréchet derivatives.
The integer exponent in the last line is `(1-m)*n`, including its negative values.

Complete natural-language proof from the current DAG node:

W0. Follow Wells’s definition of c0(E) on p287 literally. On discrete N every sequence is
continuous, and cocompact N=atTop identifies C₀(N,E) exactly with the sequences converging to
zero. Its pointwise operations and norm inherited from bounded continuous functions are the stated
supremum operations/norm, and the actual complete-space instance supplies completeness for Banach
E and F. The bounded-function dist_le theorem, applied to a difference and zero with C≥0, gives
both coordinate norm≤sequence norm and the uniform-bound-to-sup-norm estimate. Thus the carrier is
the true c0 Banach space, not the full product or an unrelated chain/function space.

W1. Let w∈Ω_s and set a_n=λ^(−n)w_n. Since λ≥1, 0<λ^(−n)≤1, so ‖a_n‖≤‖w_n‖≤‖w‖<s and a_n→0. For
0<ρ<s−‖w‖, every v with ‖v‖<ρ satisfies w+v∈Ω_s. All segments a_n+θλ^(−n)v_n, 0≤θ≤1, lie in the
source ball because their norms are at most ‖w‖+‖v‖<s. This one source-ball margin is independent
of derivative order. We regard maps on open sets by any total representative when invoking ambient
calculus; all derivative and segment calculations occur inside the given open sets and never
assume a smooth extension.

W2. The coordinate formula, f(0)=0, and the given Lipschitz estimate give ‖λ^n f(a_n)‖≤L‖w_n‖→0.
Likewise for w,z∈Ω_s, ‖λ^n(f(λ^(−n)w_n)−f(λ^(−n)z_n))‖≤L‖w_n−z_n‖. Taking supremum gives a
well-defined c0(F)-valued map A₀=C_λf, A₀(0)=0 and ‖A₀(w)−A₀(z)‖≤L‖w−z‖. In particular A₀ is
continuous. No higher derivative estimate is used here.

W3. On B_E(0,s), ordinary C^r gives continuity of D^m f for every m≤r and differentiability of D^k
f for k<r. Bind this to the forward iterated-jet calculus criterion, UniqueDiffOn of the open
ball, and the equality of within and ambient iterated derivatives on an open set. The derivative
of D^k f is the left-curried D^(k+1)f, by the actual derivative recursion; currying is an
isometry. This supplies an operator-valued HasFDerivAt, hence HasFDerivWithinAt on every segment,
whenever the mean-value theorem below is applied. Smooth infinity here is the ENat smooth order,
not the outer analytic order.

W4. For 1≤m≤r define A_m(w) by the stated coordinate formula, initially as an algebraic
m-multilinear map on c0(E). The coefficients λ^((1−m)n) are positive and ≤1; this assertion is
used only for m≥1. Continuity of D^m f at0 bounds ‖D^m f(a_n)‖ on a sufficiently long tail, and
the remaining finitely many values have a finite maximum. Choose M≥0 bounding them all. The
evaluation op-norm estimate gives ‖(A_m(w)[h₁,…,h_m])_n‖≤M∏j‖(h_j)_n‖. Since m≥1, use h₁,n→0 and
boundedness of the other directions to see that the output tends to zero. Its sup norm is
≤M∏j‖h_j‖. Coordinatewise multilinearity therefore defines an actual c0(F)-valued multilinear map;
the bounded multilinear constructor makes it continuous, and the existing opNorm_le_bound gives
‖A_m(w)‖≤M. No bound on the whole source ball has been imposed.

W5. Fix m≥1 and ε>0. Choose δ>0 with 2δ<s such that ‖D^m f(x)−D^m f(0)‖<ε/4 when ‖x‖<2δ. Choose N
with ‖a_n‖<δ for n>N. If ‖v‖<δ, the tail arguments a_n+λ^(−n)v_n have norm<2δ, so their D^m f
values differ from those at a_n by <ε/2. For the finitely many n≤N, continuity at a_n gives one
smaller positive radius making the differences <ε/2. Reduce the radius also below s−‖w‖.
Multiplication by λ^((1−m)n) cannot increase these bounds. Apply the multilinear evaluation bound
and opNorm_le_bound to the coordinate differences to obtain ‖A_m(w+v)−A_m(w)‖≤ε/2. This is
operator-norm continuity of A_m, using exactly Wells’s finite-head/tail choice; only continuity
at0 and the finite head points is needed.

W6. For each 0≤k<r, prove the first-order derivative identity D A_k(w)=curryLeft(A_(k+1)(w)), with
k=0 interpreted in the ordinary c0(F) target rather than the zero-linear-map carrier. Put
b_n=λ^(−n)v_n and g_k=D^k f (g₀=f). The previous finite-head/tail argument, now for D^(k+1)f and
all points a_n+θb_n, makes ‖Dg_k(a_n+θb_n)−Dg_k(a_n)‖≤ε simultaneously in n and θ when ‖v‖ is
sufficiently small; currying preserves norms. Each segment lies inside B_E(0,s) by W1, and W3
supplies its actual derivative at every segment point. Apply
Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' to g_k on that segment, with fixed
φ=Dg_k(a_n). Its precise conclusion is ‖g_k(a_n+b_n)−g_k(a_n)−Dg_k(a_n)[b_n]‖≤ε‖b_n‖. For k=0,
multiplication by λ^n cancels λ^(−n), giving the c0 remainder ≤ε‖v‖. For k≥1, multiply by
λ^((1−k)n), evaluate on the k unscaled directions and take the supremum. The remaining coefficient
is λ^(−kn)≤1, and the remainder operator norm is ≤ε‖v‖ by opNorm_le_bound. The linear term is
precisely λ^(−kn)D^(k+1)f(a_n)[v_n,(h₁)_n,…,(h_k)_n], the left-currying of A_(k+1)(w). Since ε is
arbitrary this proves the Frechet derivative in the operator-valued target. It is a first-order
application to each preceding derivative field, not an inference of C^k from a Peano remainder
alone.

W7. W2 gives the zeroth field, W4–W5 give continuous A_m for all positive m≤r, and W6 gives the
derivative recursion for every k<r. The exact iterated-Frechet recursion identifies these fields
successively with the ordinary iterated derivatives of C_λf on Ω_s; its zeroth derivative is the
zero-linear map evaluating to C_λf(w), not zero. Pass to within derivatives on this same open Ω_s,
which is UniqueDiffOn. The reverse continuous/differentiable-jet criterion now yields C^r there.
For smooth infinity the same criterion requires every finite m, and the above arguments apply to
each m on Ω_s. The point/order-dependent radii are used to prove continuity/differentiability
locally; they do not shrink Ω_s or require global uniform continuity. The resulting m-linear
identity is exactly the formula in the unchanged statement.

W8. The proof works for arbitrary Banach codomain F: every printed estimate is an F-norm estimate
or an operator norm from E to a space built from F, and no identification of E with F is used.
Wells prints the proposition for E→E; this is the identical written argument with its target
relabelled F, not an application of an E→E-only theorem to an unrelated carrier. λ=1 is valid
because output tails use the c0 directions, not geometric decay. L=0 causes no division; it forces
f=0 by the centered bound. Zero domain or codomain Banach spaces and finite-head N=0 are covered;
direction products with zero factors are zero. The source ball and Ω_s contain0 since s>0. Source
equation(1) uses repeated-direction shorthand [h]; the node states the full multilinear recursion.
The displayed higher Taylor subtraction on p288 omits the ordinary factorial denominators; it is
not copied as a valid identity or used to justify smoothness.
-/
theorem wells_weighted_c0_composition
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (s lam L : ℝ) (r : ℕ∞) (f : E → F)
    (hs : 0 < s) (hlam : 1 ≤ lam) (hL : 0 ≤ L) (hr : 1 ≤ r)
    (hf : ContDiffOn ℝ (r : ℕ∞ω) f (Metric.ball 0 s))
    (hf_zero : f 0 = 0)
    (hf_lipschitz : ∀ x ∈ Metric.ball (0 : E) s, ∀ y ∈ Metric.ball (0 : E) s,
      ‖f x - f y‖ ≤ L * ‖x - y‖) :
    ∃ C : C₀(ℕ, E) → C₀(ℕ, F),
      (∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ n : ℕ,
        C w n = (lam ^ n) • f ((lam ^ n)⁻¹ • w n)) ∧
      C 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s,
        ∀ z ∈ Metric.ball (0 : C₀(ℕ, E)) s, ‖C w - C z‖ ≤ L * ‖w - z‖) ∧
      ContDiffOn ℝ (r : ℕ∞ω) C (Metric.ball (0 : C₀(ℕ, E)) s) ∧
      (∀ m : ℕ, 1 ≤ m → (m : ℕ∞) ≤ r →
        ∀ w ∈ Metric.ball (0 : C₀(ℕ, E)) s, ∀ h : Fin m → C₀(ℕ, E), ∀ n : ℕ,
          (iteratedFDerivWithin ℝ m C (Metric.ball (0 : C₀(ℕ, E)) s) w h) n =
            lam ^ (((1 : ℤ) - (m : ℤ)) * (n : ℤ)) •
              iteratedFDerivWithin ℝ m f (Metric.ball (0 : E) s)
                ((lam ^ n)⁻¹ • w n) (fun j ↦ h j n)) := by
  obtain ⟨C, hC, hzero, hLip⟩ := weighted_c0_lipschitz s lam L f hs hlam hL hf_zero hf_lipschitz
  have hCsmooth : ContDiffOn ℝ (r : ℕ∞ω) C (Metric.ball (0 : C₀(ℕ, E)) s) := by
    rw [contDiffOn_iff_forall_nat_le]
    intro m hm
    have horder : ((max 1 m : ℕ) : ℕ∞) ≤ r := by
      exact_mod_cast max_le hr hm
    have hmax : ContDiffOn ℝ (max 1 m : ℕ) C (Metric.ball (0 : C₀(ℕ, E)) s) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show max 1 m ≠ 0 by omega)
      rw [hk]
      apply weighted_c0_contDiffOn_succ s lam hs hlam k f ?_ C hC
      apply hf.of_le
      rw [← Nat.cast_succ, ← hk]
      exact_mod_cast horder
    exact hmax.of_le (by exact_mod_cast le_max_right 1 m)
  refine ⟨C, hC, hzero, hLip, hCsmooth, ?_⟩
  intro m _ hm w hw h n
  exact weighted_c0_derivative_formula s lam r f C hlam hf hCsmooth hC m hm w hw h n

end HolomorphicAnosov.Analysis
