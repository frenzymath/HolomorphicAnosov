import HolomorphicAnosov.Analysis.CompositionHolderInduction
import HolomorphicAnosov.Analysis.IteratedFDerivIsometryLeft
import HolomorphicAnosov.Analysis.IteratedFDerivIsometryRight

/-!
# Uniform Hölder bound for composition

Rafael de la Llave and Rafael Obaya, *Regularity of the composition operator in
spaces of Hölder functions*, DCDS 5(1) (1999), 157–184, Theorem 4.3(ii.3),
pp.169–170; Definitions 2.1/2.5 and Proposition 3.6.

The derivatives are Mathlib's unnormalized iterated Fréchet derivatives, with
original multilinear operator norms. On the open domains, within derivatives
agree with ordinary derivatives. Order zero is the canonical zero-linear
encoding of the function value, isometric to that value. No new norm or
Hölder-class definition is introduced.
-/

namespace HolomorphicAnosov

universe u v w

/-- Uniform spatial `C^(n,α)` composition estimate in the original real Banach norms.

Source: de la Llave–Obaya, Theorem 4.3(ii.3), pp.169–170, specialized to open convex
source and receiving domains (compensated constants one), with strict `0 < α < 1`.
The constant is quantified before the spaces, domains, maps and bounds, and thus
is independent of all of them. The exponent is `n + α`, with no factorial
normalization. Empty domains, zero bounds and zero-dimensional spaces are included.

Natural-language proof from the DAG:

CH1: Use the original norms throughout. Write N_(k,α)(F;S) for the MAX of the suprema of
||D^jF||,0≤j≤k, and the α-Hölder seminorm of D^kF on S, as in Definitions2.1/2.5. Empty suprema
are0. The assumptions give N_(n,α)(f;A)≤Af and N_(n,α)(g;B)≤Ag. If A is empty every conclusion is
vacuous; if B is empty MapsTo forces A empty. Otherwise work on these exact open convex domains.
They have compensated constants1, because their straight segments lie in the domains and have length
equal to the original norm distance. No convexity of f(A), common domain construction, or parameter
regularity is asserted.

CH2: First establish ordinary C^n of H=g∘f independently of the norm induction. Translate the two
given ContDiffOn certificates to ContMDiffOn on the identity models of their original normed spaces.
Apply ContMDiffOn.comp with the actual set inclusion A⊆f⁻¹(B), and translate back by
contMDiffOn_iff_contDiffOn. This gives H C^n on exactly A. Open-set UniqueDiffOn on A and B
identifies selected within derivatives with ordinary ones. The forward finite derivative criterion
gives differentiability of the order-j field for j<n. In particular f,g,H are differentiable at
their relevant points since n≥1. HasFDerivAt.comp then gives, at EVERY x∈A,
DH(x)=(Dg(f(x))).comp(Df(x)). Let R be this operator-valued right side on A. The identity is EqOn on
the entire A, not just equality at a single point. Transfer it to each iterated within derivative by
iteratedFDerivWithin_congr, and use the exact right-curry isometry. Hence for0≤j≤n−1 the jth
derivative field of DH has the same norm and pairwise difference norm as D^(j+1)H. Therefore
N_(n,α)(H;A)=max(sup_A||H||,N_(n−1,α)(R;A)). The source uses precisely this recursive MAX identity
in the last displayed calculation on p170. No derivative of order n+1 is used.

CH3: Make the source lower-factor estimates explicit. For any k≥1, if N_(k,α)(F;S)≤a on an open
convex S, the field D^(k−1)F is differentiable by the finite criterion. Its derivative is the
LEFT-currying isometry applied to D^kF, so its derivative norm is≤a. The convex mean-value bound
gives difference≤a||x−y|| on S. For0<||x−y||≤1, this is≤a||x−y||^α; for larger distance the two
value bounds give≤2a≤2a||x−y||^α. At equal points the difference is0. Thus N_(k−1,α)(F;S)≤2a, the
convex κ=1 specialization of Proposition3.6. Applied to f it gives N_(n−1,α)(f;A)≤2Af. The exact
RIGHT-curry norm/difference identity gives N_(n−1,α)(Df;A)≤Af and N_(n−1,α)(Dg;B)≤Ag.
fderiv_of_isOpen supplies C^(n−1) of these derivative fields on A and B. Their operator targets are
real Banach spaces by the existing continuous-linear-map completeness instance in the original
operator norm, with identity real scalar homomorphism, normed metrizable source and complete target.
All these bindings preserve the actual domain and lose precisely one finite derivative order.

CH4: For the base n=1 put t=1+α. The original derivative bound and convex mean-value estimate on A
give Lip(f|A)≤Af. The actual MapsTo f A B permits evaluating the GIVEN α-Hölder Dg field at
f(x),f(y), so ||Dg(f(x))−Dg(f(y))||≤Ag Af^α||x−y||^α, while ||Dg(f(x))||≤Ag. Thus
N_(0,α)(Dg∘f;A)≤Ag(1+Af^α), and CH3 gives N_(0,α)(Df;A)≤Af. These are continuous fields on A by the
same finite composition law at order0. The fixed bilinear operation
C:(F→L[ℝ]G)→L[ℝ]((E→L[ℝ]F)→L[ℝ](E→L[ℝ]G)), C(T)(S)=T.comp(S), has norm≤1: the operator-composition
bound followed by opNorm_le_bound in each argument proves this. Apply the published bilinear Hölder
provider at order0 to these two ORIGINAL Banach-valued fields. It gives N_(0,α)(R;A)≤2Ag Af(1+Af^α),
exactly the first inequality in the proof on printed170, using part(ii.1) of the theorem. Values of
H are bounded by Ag because f(A)⊆B. For0≤Af≤1, 2Af(1+Af^α)≤4; for Af≥1, Af≤Af^(1+α) and the same
expression is≤4Af^(1+α). Consequently CH2 gives N_(1,α)(H;A)≤4Ag(1+Af^(1+α)). Set M_(1,α)=4. No
second derivative is used and Af=0 causes no division.

CH5: For n≥2 set t=n+α and assume the composition estimate at order n−1 for arbitrary original real
Banach source/receiving/output spaces on open convex domains. Apply it on A,B to f and the
operator-valued map Dg. CH3 supplies N_(n−1,α)(f;A)≤2Af, N_(n−1,α)(Dg;B)≤Ag, and both maps C^(n−1),
with the SAME MapsTo f A B. Therefore N_(n−1,α)(Dg∘f;A)≤M_(n−1,α)Ag(1+(2Af)^(n−1+α)). CH3 also gives
N_(n−1,α)(Df;A)≤Af. Apply the already published bilinear provider at order n−1 to operator
composition C of norm≤1 as bound in CH4. With Q_(n−1)=2^(2n−1), it yields
N_(n−1,α)(R;A)≤Q_(n−1)M_(n−1,α)Ag Af(1+(2Af)^(t−1)). This is the written induction on printed170,
with κ_A=1 and its lower-factor Proposition3.6 made explicit. Only derivatives through order n
participate; the GIVEN order-n Hölder field is never differentiated.

CH6: For a=Af>0 the elementary real-power identities give a(1+(2a)^(t−1))=a+2^(t−1)a^t. Since t>1,
splitting0<a≤1 and a≥1 gives a≤1+a^t, and hence a+2^(t−1)a^t≤(1+2^(t−1))(1+a^t). At a=0 the original
product is0, so the same bound holds directly, without cancellation at a zero base. Choose
M_(n,α)=max(1,2^(2n−1)M_(n−1,α)(1+2^(n−1+α))) for n≥2. Together with M_(1,α)=4 this gives finite
constants≥1 depending ONLY on n and α. CH2's MAX recursion and sup_A||H||≤Ag prove
N_(n,α)(H;A)≤M_(n,α)Ag(1+Af^(n+α)). All individual jet and top Hölder bounds follow. Ag=0, zero maps
and zero-dimensional spaces require no division and are included. The published statement asserts
existence of M_t and prints the factor 1+||f||_(C^t)^t, not (1+||f||_(C^t))^t. The explicit
constants here are choices obtained from its written proof, not claimed to be the author's unique
constants. The inherited stray equality sign in the second product-induction summand on p169 is
already disclosed in the bilinear provider; it is not copied as a valid identity. This proves only
uniform spatial composition bounds for the stated domains and MapsTo data, not equal-exponent
parameter continuity or native receiving-domain existence.
-/
theorem composition_holder_bound (n : ℕ) (α : ℝ) (hn : 1 ≤ n)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (E : Type u) (F : Type v) (G : Type w)
        [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
        (A : Set E) (B : Set F) (f : E → F) (g : F → G) (Af Ag : ℝ),
        IsOpen A → Convex ℝ A → IsOpen B → Convex ℝ B →
        ContDiffOn ℝ n f A → ContDiffOn ℝ n g B → Set.MapsTo f A B →
        0 ≤ Af → 0 ≤ Ag →
        (∀ j : ℕ, j ≤ n → ∀ x ∈ A, ‖iteratedFDerivWithin ℝ j f A x‖ ≤ Af) →
        (∀ j : ℕ, j ≤ n → ∀ y ∈ B, ‖iteratedFDerivWithin ℝ j g B y‖ ≤ Ag) →
        (∀ x ∈ A, ∀ x' ∈ A,
          ‖iteratedFDerivWithin ℝ n f A x - iteratedFDerivWithin ℝ n f A x'‖ ≤
            Af * ‖x - x'‖ ^ α) →
        (∀ y ∈ B, ∀ y' ∈ B,
          ‖iteratedFDerivWithin ℝ n g B y - iteratedFDerivWithin ℝ n g B y'‖ ≤
            Ag * ‖y - y'‖ ^ α) →
        ContDiffOn ℝ n (g ∘ f) A ∧
          (∀ j : ℕ, j ≤ n → ∀ x ∈ A,
            ‖iteratedFDerivWithin ℝ j (g ∘ f) A x‖ ≤ M * Ag * (1 + Af ^ ((n : ℝ) + α))) ∧
          (∀ x ∈ A, ∀ x' ∈ A,
            ‖iteratedFDerivWithin ℝ n (g ∘ f) A x -
              iteratedFDerivWithin ℝ n (g ∘ f) A x'‖ ≤
                M * Ag * (1 + Af ^ ((n : ℝ) + α)) * ‖x - x'‖ ^ α) := by
  obtain ⟨M, hM, H⟩ := composition_holder_bound_same_universe.{u, max v w}
    n α hn hα_pos hα_lt_one
  refine ⟨M, hM, ?_⟩
  intro E F G _ _ _ _ _ _ _ _ _ A B f g Af Ag hA hcA hB hcB hf hg hm hAf hAg hfn hgn hfh hgh
  let Fu : Type max v w := ULift.{w, v} F
  let Gu : Type max v w := ULift.{v, w} G
  let eF : Fu ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  let eG : Gu ≃ₗᵢ[ℝ] G := LinearIsometryEquiv.ulift ℝ G
  let fu : E → Fu := eF.symm ∘ f
  let gu : Fu → Gu := eG.symm ∘ (g ∘ eF)
  let Bu : Set Fu := eF ⁻¹' B
  have hBu : IsOpen Bu := hB.preimage eF.continuous
  have hcBu : Convex ℝ Bu := hcB.linear_preimage eF.toLinearEquiv.toLinearMap
  have hmu : Set.MapsTo fu A Bu := by
    intro x hx
    simpa only [fu, Bu, Set.mem_preimage, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply] using hm hx
  have hfu : ContDiffOn ℝ n fu A := eF.symm.contDiff.comp_contDiffOn hf
  have hgu : ContDiffOn ℝ n gu Bu := eG.symm.contDiff.comp_contDiffOn
    (hg.comp_continuousLinearMap (eF : Fu →L[ℝ] F))
  have hfn' (j : ℕ) (hj : j ≤ n) (x : E) (hx : x ∈ A) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ Af := by
    simpa only [iteratedFDerivWithin_of_isOpen _ hA hx] using hfn j hj x hx
  have hgn' (j : ℕ) (hj : j ≤ n) (x : F) (hx : x ∈ B) :
      ‖iteratedFDeriv ℝ j g x‖ ≤ Ag := by
    simpa only [iteratedFDerivWithin_of_isOpen _ hB hx] using hgn j hj x hx
  have hfh' (x : E) (hx : x ∈ A) (y : E) (hy : y ∈ A) :
      ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤ Af * ‖x-y‖ ^ α := by
    simpa only [iteratedFDerivWithin_of_isOpen _ hA hx,
      iteratedFDerivWithin_of_isOpen _ hA hy] using hfh x hx y hy
  have hgh' (x : F) (hx : x ∈ B) (y : F) (hy : y ∈ B) :
      ‖iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y‖ ≤ Ag * ‖x-y‖ ^ α := by
    simpa only [iteratedFDerivWithin_of_isOpen _ hB hx,
      iteratedFDerivWithin_of_isOpen _ hB hy] using hgh x hx y hy
  have hfun (j : ℕ) (hj : j ≤ n) (x : E) (hx : x ∈ A) :
      ‖iteratedFDeriv ℝ j fu x‖ ≤ Af := by
    rw [eF.symm.norm_iteratedFDeriv_comp_left]
    exact hfn' j hj x hx
  have hgun (j : ℕ) (hj : j ≤ n) (x : Fu) (hx : x ∈ Bu) :
      ‖iteratedFDeriv ℝ j gu x‖ ≤ Ag := by
    rw [eG.symm.norm_iteratedFDeriv_comp_left, eF.norm_iteratedFDeriv_comp_right]
    exact hgn' j hj (eF x) hx
  have hfuh (x : E) (hx : x ∈ A) (y : E) (hy : y ∈ A) :
      ‖iteratedFDeriv ℝ n fu x - iteratedFDeriv ℝ n fu y‖ ≤ Af * ‖x-y‖ ^ α := by
    rw [norm_iteratedFDeriv_sub_comp_left]
    exact hfh' x hx y hy
  have hguh (x : Fu) (hx : x ∈ Bu) (y : Fu) (hy : y ∈ Bu) :
      ‖iteratedFDeriv ℝ n gu x - iteratedFDeriv ℝ n gu y‖ ≤ Ag * ‖x-y‖ ^ α := by
    rw [norm_iteratedFDeriv_sub_comp_left, norm_iteratedFDeriv_sub_comp_right]
    simpa only [← eF.map_sub, eF.norm_map] using hgh' (eF x) hx (eF y) hy
  obtain ⟨_, hcompn, hcomph⟩ := H E Fu Gu A Bu fu gu Af Ag hA hcA hBu hcBu
    hfu hgu hmu hAf hAg hfun hgun hfuh hguh
  have heq : gu ∘ fu = eG.symm ∘ (g ∘ f) := by
    ext x
    simp only [gu, fu, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  refine ⟨hg.comp hf hm, ?_, ?_⟩
  · intro j hj x hx
    have h := hcompn j hj x hx
    rw [heq, eG.symm.norm_iteratedFDeriv_comp_left] at h
    simpa only [iteratedFDerivWithin_of_isOpen _ hA hx] using h
  · intro x hx y hy
    have h := hcomph x hx y hy
    rw [heq, norm_iteratedFDeriv_sub_comp_left] at h
    simpa only [iteratedFDerivWithin_of_isOpen _ hA hx,
      iteratedFDerivWithin_of_isOpen _ hA hy] using h

end HolomorphicAnosov
