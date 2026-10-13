import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bilinear closure of finite-order Hölder derivative bounds

Source: Rafael de la Llave and Rafael Obaya, Regularity of the composition operator in spaces of Hölder
functions, Discrete and Continuous Dynamical Systems 5(1) (January1999),157–184,
DOI10.3934/dcds.1999.5.157. Definitions2.1 printed159 and2.5 printed162; Definition3.5 and
Proposition3.6 printed165–166; Proposition4.2 statement168 and full proof169 (PDF12–13); convex
compensated domains are noted in Proposition5.2 printed171. Obtained full article:
literature/Regularity of the composition operator in spaces of Hölder functions (Obaya, R. Llave,
Rafael) (z-library.sk, 1lib.sk, z-lib.sk).pdf; full extracted text literature/de-la-llave-obaya-
composition-holder-1999.txt.

DAG node: `analysis.de_la_llave_obaya_bilinear_holder_bound_g6`.
The statement uses the given real Banach norms, not an equivalent or normalized norm.
`iteratedFDeriv ℝ j` is the unnormalized jth Fréchet derivative with its continuous-multilinear
operator norm. At j = 0 its norm is exactly the norm of the value, by
`norm_iteratedFDeriv_zero`. No derivative of order n + 1 is assumed.
-/

universe uD uU uV uW

namespace HolomorphicAnosov

noncomputable section

/-- Bilinear closure with the explicit constant `2 ^ (2 * n + 1) * ‖B‖ * Af * Ag`.

Source: Rafael de la Llave and Rafael Obaya, Regularity of the composition operator in spaces of Hölder
functions, Discrete and Continuous Dynamical Systems 5(1) (January1999),157–184,
DOI10.3934/dcds.1999.5.157. Definitions2.1 printed159 and2.5 printed162; Definition3.5 and
Proposition3.6 printed165–166; Proposition4.2 statement168 and full proof169 (PDF12–13); convex
compensated domains are noted in Proposition5.2 printed171. Obtained full article:
literature/Regularity of the composition operator in spaces of Hölder functions (Obaya, R. Llave,
Rafael) (z-library.sk, 1lib.sk, z-lib.sk).pdf; full extracted text literature/de-la-llave-obaya-
composition-holder-1999.txt.

The open, convex domain may be empty. The bounds may vanish, the bilinear map may be zero,
and any of the real Banach spaces may have dimension zero. All derivative and Hölder
bounds use the original source and target norms. The exponent is strictly between zero and one.
Only finite spatial derivatives are assumed, with no parameter regularity hypothesis.

Natural-language proof (the node's complete source-relative proof):

BH1: Fix the original real Banach spaces, their norms, S, n and α. For F which is C^k on S, let
N_(k,α)(F;S) be the maximum of the suprema of ||D^jF|| for0≤j≤k and the α-Hölder seminorm of D^kF on
S. Suprema over empty sets, including empty sets of distinct pairs, are0. This is exactly the MAX
norm in Definitions2.1/2.5, with unnormalized Fréchet derivatives and the original source norm in
the Hölder denominator. The assumptions give N_(n,α)(f;S)≤Af and N_(n,α)(g;S)≤Ag. It suffices to
bound N_(n,α)(H;S). If S is empty all pointwise assertions and C^n on S are vacuous; assume S is
nonempty for the induction. No extension or parameter derivative is involved.

BH2: Establish H C^n before the quantitative induction. The constant map z↦B is C^n; applying
ContDiffOn.clm_apply to it and f gives z↦B(f(z)) C^n with values in V→L[ℝ]W. A second application
with g gives H C^n on the same S. Since S is open, UniqueDiffOn ℝ S holds and selected within
derivatives equal ordinary derivatives at points of S. Every derivative below concerns these same
functions restricted to S. This is the ordinary finite product-calculus prerequisite of
Proposition4.2.

BH3: For n=0 follow the base case on printed169. For x,y∈S,
H(x)−H(y)=B(f(x)−f(y))(g(x))+B(f(y))(g(x)−g(y)). Applying the continuous-linear-map operator-norm
inequality twice gives ||H(x)||≤||B||AfAg and ||H(x)−H(y)||≤2||B||AfAg||x−y||^α. Thus
N_(0,α)(H;S)≤C_0||B||AfAg for C_0=2. Only the given continuity, value and α-Hölder bounds of f,g are
used; no derivative of order1 is required.

BH4: For n≥1 make Proposition3.6 explicit on convex S, whose compensated constant is1. Let F be f or
g, and A the corresponding bound Af or Ag. The forward direction of
contDiffOn_iff_continuousOn_differentiableOn gives differentiability on S of Z=D^(n−1)F, because
n−1<n and S is UniqueDiffOn. The iteratedFDeriv recursion identifies DZ with the canonical LEFT-
currying of D^nF, a linear isometry, so ||DZ||≤A. Apply the convex mean-value norm estimate with
comparison linear map0 to x,y∈S: their full segment lies in S, and ||Z(x)−Z(y)||≤A||x−y||.
For0<||x−y||≤1 this is≤A||x−y||^α. For||x−y||>1, use the two value bounds to get≤2A≤2A||x−y||^α; at
x=y the difference is0. Lower derivatives retain bound A. Hence N_(n−1,α)(F;S)≤2A. This is the
source downgrade estimate with κ_S=1 and does not differentiate the order-n field.

BH5: Follow the printed derivative identity with its full operator types. Define
b1:(D→L[ℝ]U)→L[ℝ](V→L[ℝ](D→L[ℝ]W)) by b1(h)(v)(d)=B(h(d))(v), and b2:U→L[ℝ]((D→L[ℝ]V)→L[ℝ](D→L[ℝ]W))
by b2(u)(h)(d)=B(u)(h(d)). These are B.precompL D and B.precompR D. Applying the operator-norm
inequality to each input and then opNorm_le_bound to each bundled linear map gives
||b1||,||b2||≤||B||. These formulas are bilinear in the indicated inputs and preserve the original
norms. Their operator targets are Banach by the continuous-linear-map completeness instance, with
identity real scalar homomorphism, normed metrizable source and complete target, applied
recursively.

Df,Dg are C^(n−1) on the same open S by fderiv_of_isOpen with (n−1)+1≤n. Constant/evaluation twice
gives H1=b1(Df,g) and H2=b2(f,Dg) C^(n−1) on S, both valued in D→L[ℝ]W. At every x∈S, the exact
bilinear derivative theorem gives D_SH=H1+H2, where D_S is fderivWithin on S. Transfer this EqOn
identity to iterated derivatives by iteratedFDerivWithin_congr and use
iteratedFDerivWithin_add_apply with the just-established finite regularity. The canonical RIGHT-
currying linear isometry then identifies D^(j+1)H with the right-uncurrying of D^j(H1+H2), for
each0≤j≤n−1. It preserves norms and differences, not merely values of norms at one point. The same
right-curry identity for f,g gives N_(n−1,α)(Df;S)≤Af and N_(n−1,α)(Dg;S)≤Ag, using derivatives of
orders1 through n and the given order-n Hölder bounds. Within and ordinary fields are identified
only at points of the open S. No order-n field is differentiated.

BH6: Assume the result at order n−1 for arbitrary real Banach factor/output spaces. Apply it to H1
with factor bounds Af and2Ag from BH4–BH5, and to H2 with bounds2Af and Ag; their bilinear norms
are≤||B||. Each N_(n−1,α)(Hi;S) is therefore≤2C_(n−1)||B||AfAg. Triangle inequalities for all
derivatives and all top Hölder differences give N_(n−1,α)(H1+H2;S)≤4C_(n−1)||B||AfAg. The exact
right-curry identities in BH5 give the source recursion
N_(n,α)(H;S)=max(sup_S||H||,N_(n−1,α)(DH;S)). Together with sup_S||H||≤||B||AfAg, this
is≤C_n||B||AfAg for C_n=4C_(n−1), C_0=2. Hence C_n=2^(2n+1), the published constant with κ_S=1, and
all bounds in the statement follow. Zero Af, zero Ag, zero B and zero-dimensional spaces are covered
without division by these quantities. The printed second summand on p169 has a stray equality sign
after ||b||. The valid summand used here is C_(n−1)||b|| ||f||_(C^(t−1)) ||dg||_(C^(t−1)),
determined by its explicitly printed b1/b2 derivative identity. This typographical defect is
disclosed instead of quoted as a valid equality.
-/
theorem deLaLlaveObaya_bilinear_holder_bound
    {D : Type uD} {U : Type uU} {V : Type uV} {W : Type uW}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (S : Set D) (hS : IsOpen S) (hSconv : Convex ℝ S)
    (n : ℕ) (α Af Ag : ℝ)
    (hαpos : 0 < α) (hαlt : α < 1) (hAf : 0 ≤ Af) (hAg : 0 ≤ Ag)
    (f : D → U) (g : D → V)
    (hf : ContDiffOn ℝ n f S) (hg : ContDiffOn ℝ n g S)
    (hfnorm : ∀ j : ℕ, j ≤ n → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ Af)
    (hgnorm : ∀ j : ℕ, j ≤ n → ∀ x ∈ S, ‖iteratedFDeriv ℝ j g x‖ ≤ Ag)
    (hfholder : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤
        Af * Real.rpow ‖x - y‖ α)
    (hgholder : ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y‖ ≤
        Ag * Real.rpow ‖x - y‖ α)
    (B : U →L[ℝ] V →L[ℝ] W) :
    let H : D → W := fun x ↦ B (f x) (g x)
    let K : ℝ := (2 : ℝ) ^ (2 * n + 1) * ‖B‖ * Af * Ag
    ContDiffOn ℝ n H S ∧
      (∀ j : ℕ, j ≤ n → ∀ x ∈ S, ‖iteratedFDeriv ℝ j H x‖ ≤ K) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        ‖iteratedFDeriv ℝ n H x - iteratedFDeriv ℝ n H y‖ ≤
          K * Real.rpow ‖x - y‖ α) := by
  classical
  -- Mathlib's binomial derivative bound implements the finite product calculus.
  -- For the Hölder bound, apply it to the two terms in H - H ∘ (· + δ).
  -- Each lower derivative is Hölder by the convex mean-value estimate; translation
  -- commutes with all iterated derivatives. For n ≥ 1 this gives 2^(n+2), which
  -- is at most the specified 2^(2*n+1). At n = 0 use the sharp two-term estimate.
  dsimp only
  have hH : ContDiffOn ℝ n (fun x ↦ B (f x) (g x)) S :=
    (contDiffOn_const.clm_apply hf).clm_apply hg
  have bbound (T : Set D) (hT : IsOpen T) (F : D → U) (G : D → V)
      (hF : ContDiffOn ℝ n F T) (hG : ContDiffOn ℝ n G T)
      (j : ℕ) (hj : j ≤ n) (z : D) (hz : z ∈ T) (a b : ℝ)
      (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hFa : ∀ i ≤ j, ‖iteratedFDeriv ℝ i F z‖ ≤ a)
      (hGb : ∀ i ≤ j, ‖iteratedFDeriv ℝ i G z‖ ≤ b) :
      ‖iteratedFDeriv ℝ j (fun t ↦ B (F t) (G t)) z‖ ≤
        (2 : ℝ) ^ j * ‖B‖ * a * b := by
    have he (i : ℕ) (q : D → W) :
        iteratedFDerivWithin ℝ i q T z = iteratedFDeriv ℝ i q z :=
      iteratedFDerivWithin_of_isOpen _ hT hz
    rw [← he]
    apply (B.norm_iteratedFDerivWithin_le_of_bilinear hF hG (hT.uniqueDiffOn)
      hz (by exact_mod_cast hj)).trans
    calc
      ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i F T z‖ * ‖iteratedFDerivWithin ℝ (j - i) G T z‖ ≤
          ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a * b := by
        gcongr with i hi
        · rw [iteratedFDerivWithin_of_isOpen _ hT hz]
          exact hFa i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        · rw [iteratedFDerivWithin_of_isOpen _ hT hz]
          exact hGb (j - i) (Nat.sub_le _ _)
      _ = (2 : ℝ) ^ j * ‖B‖ * a * b := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hs : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hs]
        ring
  refine ⟨hH, ?_, ?_⟩
  · intro j hj x hx
    apply (bbound S hS f g hf hg j hj x hx Af Ag hAf hAg
      (fun i hi ↦ hfnorm i (hi.trans hj) x hx)
      (fun i hi ↦ hgnorm i (hi.trans hj) x hx)).trans
    have hp : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (2 * n + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (norm_nonneg B)) hAf) hAg
  · intro x hx y hy
    have hr : 0 ≤ Real.rpow ‖x - y‖ α := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hn : n = 0
    · subst n
      have hfn (x : D) (hx : x ∈ S) : ‖f x‖ ≤ Af := by
        simpa only [norm_iteratedFDeriv_zero] using hfnorm 0 le_rfl x hx
      have hgn (x : D) (hx : x ∈ S) : ‖g x‖ ≤ Ag := by
        simpa only [norm_iteratedFDeriv_zero] using hgnorm 0 le_rfl x hx
      have hfd : ‖f x - f y‖ ≤ Af * Real.rpow ‖x - y‖ α := by
        simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
          LinearIsometryEquiv.norm_map] using hfholder x hx y hy
      have hgd : ‖g x - g y‖ ≤ Ag * Real.rpow ‖x - y‖ α := by
        simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
          LinearIsometryEquiv.norm_map] using hgholder x hx y hy
      have he : B (f x) (g x) - B (f y) (g y) =
          B (f x - f y) (g x) + B (f y) (g x - g y) := by simp [map_sub]
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
        LinearIsometryEquiv.norm_map, mul_zero, zero_add, pow_one]
      rw [he]
      calc
        _ ≤ ‖B (f x - f y) (g x)‖ + ‖B (f y) (g x - g y)‖ := norm_add_le _ _
        _ ≤ ‖B‖ * (Af * Real.rpow ‖x - y‖ α) * Ag +
            ‖B‖ * Af * (Ag * Real.rpow ‖x - y‖ α) := by
          apply add_le_add
          · exact (B.le_opNorm₂ _ _).trans (by gcongr; exact hgn x hx)
          · exact (B.le_opNorm₂ _ _).trans (by gcongr; exact hfn y hy)
        _ = _ := by ring
    have hfall : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤
        (2 * Af) * Real.rpow ‖x - y‖ α := by
      intro j hj
      by_cases he : j = n
      · subst j
        exact (hfholder x hx y hy).trans (by nlinarith)
      have hd : ∀ z ∈ S, DifferentiableAt ℝ (iteratedFDeriv ℝ j f) z :=
        fun z hz ↦ (hf.contDiffAt (hS.mem_nhds hz)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast (show j < n by omega))
      have hb : ∀ z ∈ S, ‖fderiv ℝ (iteratedFDeriv ℝ j f) z‖ ≤ Af := by
        intro z hz
        rw [norm_fderiv_iteratedFDeriv]
        exact hfnorm (j + 1) (by omega) z hz
      by_cases hdist : ‖x - y‖ ≤ 1
      · have hp : ‖x - y‖ ≤ Real.rpow ‖x - y‖ α := by
          convert Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hdist hαpos.le hαlt.le using 1
          simp only [Real.rpow_one]
        exact (hSconv.norm_image_sub_le_of_norm_fderiv_le hd hb hy hx).trans (by nlinarith)
      · have hp := Real.one_le_rpow (le_of_not_ge hdist) hαpos.le
        apply (norm_sub_le _ _).trans
        have hfx := hfnorm j hj x hx
        have hfy := hfnorm j hj y hy
        have hp' : 2 * Af ≤ (2 * Af) * Real.rpow ‖x - y‖ α := by
          calc
            2 * Af = (2 * Af) * 1 := by ring
            _ ≤ (2 * Af) * Real.rpow ‖x - y‖ α :=
              mul_le_mul_of_nonneg_left hp (by positivity)
        nlinarith
    have hgall : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x - iteratedFDeriv ℝ j g y‖ ≤
        (2 * Ag) * Real.rpow ‖x - y‖ α := by
      intro j hj
      by_cases he : j = n
      · subst j
        exact (hgholder x hx y hy).trans (by nlinarith)
      have hd : ∀ z ∈ S, DifferentiableAt ℝ (iteratedFDeriv ℝ j g) z :=
        fun z hz ↦ (hg.contDiffAt (hS.mem_nhds hz)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast (show j < n by omega))
      have hb : ∀ z ∈ S, ‖fderiv ℝ (iteratedFDeriv ℝ j g) z‖ ≤ Ag := by
        intro z hz
        rw [norm_fderiv_iteratedFDeriv]
        exact hgnorm (j + 1) (by omega) z hz
      by_cases hdist : ‖x - y‖ ≤ 1
      · have hp : ‖x - y‖ ≤ Real.rpow ‖x - y‖ α := by
          convert Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hdist hαpos.le hαlt.le using 1
          simp only [Real.rpow_one]
        exact (hSconv.norm_image_sub_le_of_norm_fderiv_le hd hb hy hx).trans (by nlinarith)
      · have hp := Real.one_le_rpow (le_of_not_ge hdist) hαpos.le
        apply (norm_sub_le _ _).trans
        have hgx := hgnorm j hj x hx
        have hgy := hgnorm j hj y hy
        have hp' : 2 * Ag ≤ (2 * Ag) * Real.rpow ‖x - y‖ α := by
          calc
            2 * Ag = (2 * Ag) * 1 := by ring
            _ ≤ (2 * Ag) * Real.rpow ‖x - y‖ α :=
              mul_le_mul_of_nonneg_left hp (by positivity)
        nlinarith
    let δ : D := y - x
    let q : D → D := fun z ↦ z + δ
    let T : Set D := S ∩ q ⁻¹' S
    have hqcont : ContDiffOn ℝ n q T := by
      dsimp [q]
      fun_prop
    have hqmap : Set.MapsTo q T S := by
      intro z hz
      exact hz.2
    have hTopen : IsOpen T := by
      exact hS.inter (hS.preimage (by fun_prop))
    have hxT : x ∈ T := by
      refine ⟨hx, ?_⟩
      change x + (y - x) ∈ S
      simpa [add_comm, add_left_comm, add_assoc] using hy
    have hfT : ContDiffOn ℝ n f T := hf.mono Set.inter_subset_left
    have hfq : ContDiffOn ℝ n (fun z ↦ f (q z)) T := hf.comp hqcont hqmap
    have hgT : ContDiffOn ℝ n g T := hg.mono Set.inter_subset_left
    have hgq : ContDiffOn ℝ n (fun z ↦ g (q z)) T := hg.comp hqcont hqmap
    let F : D → U := fun z ↦ f z - f (q z)
    let G : D → V := g
    let F' : D → U := fun z ↦ f (q z)
    let G' : D → V := fun z ↦ g z - g (q z)
    have hF : ContDiffOn ℝ n F T := hfT.sub hfq
    have hG : ContDiffOn ℝ n G T := hgT
    have hF' : ContDiffOn ℝ n F' T := hfq
    have hG' : ContDiffOn ℝ n G' T := hgT.sub hgq
    have hqx : q x = y := by dsimp [q, δ]; abel
    have hfTx := hfT.contDiffAt (hTopen.mem_nhds hxT)
    have hfqx := hfq.contDiffAt (hTopen.mem_nhds hxT)
    have hgTx := hgT.contDiffAt (hTopen.mem_nhds hxT)
    have hgqx := hgq.contDiffAt (hTopen.mem_nhds hxT)
    have hFd : ∀ i ≤ n, ‖iteratedFDeriv ℝ i F x‖ ≤
        (2 * Af) * Real.rpow ‖x - y‖ α := by
      intro i hi
      dsimp [F]
      rw [fun_iteratedFDeriv_sub_apply (hfTx.of_le (by exact_mod_cast hi))
        (hfqx.of_le (by exact_mod_cast hi))]
      change ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i (fun z ↦ f (z + δ)) x‖ ≤ _
      rw [iteratedFDeriv_comp_add_right]
      change ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f (q x)‖ ≤ _
      rw [hqx]
      exact hfall i hi
    have hGd : ∀ i ≤ n, ‖iteratedFDeriv ℝ i G x‖ ≤ Ag := by
      intro i hi
      exact hgnorm i hi x hx
    have hF'd : ∀ i ≤ n, ‖iteratedFDeriv ℝ i F' x‖ ≤ Af := by
      intro i hi
      change ‖iteratedFDeriv ℝ i (fun z ↦ f (z + δ)) x‖ ≤ _
      rw [iteratedFDeriv_comp_add_right]
      change ‖iteratedFDeriv ℝ i f (q x)‖ ≤ _
      rw [hqx]
      exact hfnorm i hi y hy
    have hG'd : ∀ i ≤ n, ‖iteratedFDeriv ℝ i G' x‖ ≤
        (2 * Ag) * Real.rpow ‖x - y‖ α := by
      intro i hi
      dsimp [G']
      rw [fun_iteratedFDeriv_sub_apply (hgTx.of_le (by exact_mod_cast hi))
        (hgqx.of_le (by exact_mod_cast hi))]
      change ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i (fun z ↦ g (z + δ)) x‖ ≤ _
      rw [iteratedFDeriv_comp_add_right]
      change ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g (q x)‖ ≤ _
      rw [hqx]
      exact hgall i hi
    let H : D → W := fun z ↦ B (f z) (g z)
    have hHT : ContDiffOn ℝ n H T := hH.mono Set.inter_subset_left
    have hHq : ContDiffOn ℝ n (fun z ↦ H (q z)) T := hH.comp hqcont hqmap
    have hBFG : ContDiffOn ℝ n (fun z ↦ B (F z) (G z)) T :=
      (contDiffOn_const.clm_apply hF).clm_apply hG
    have hBFG' : ContDiffOn ℝ n (fun z ↦ B (F' z) (G' z)) T :=
      (contDiffOn_const.clm_apply hF').clm_apply hG'
    have heq : (fun z ↦ H z - H (q z)) =
        (fun z ↦ B (F z) (G z) + B (F' z) (G' z)) := by
      funext z
      simp [H, F, G, F', G', map_sub]
    have hdif : iteratedFDeriv ℝ n H x - iteratedFDeriv ℝ n H y =
        iteratedFDeriv ℝ n (fun z ↦ B (F z) (G z)) x +
          iteratedFDeriv ℝ n (fun z ↦ B (F' z) (G' z)) x := by
      have hqder : iteratedFDeriv ℝ n (fun z ↦ H (q z)) x =
          iteratedFDeriv ℝ n H y := by
        change iteratedFDeriv ℝ n (fun z ↦ H (z + δ)) x = _
        rw [iteratedFDeriv_comp_add_right]
        change iteratedFDeriv ℝ n H (q x) = _
        rw [hqx]
      rw [← hqder, ← fun_iteratedFDeriv_sub_apply
        (hHT.contDiffAt (hTopen.mem_nhds hxT)) (hHq.contDiffAt (hTopen.mem_nhds hxT)),
        heq, fun_iteratedFDeriv_add_apply
        (hBFG.contDiffAt (hTopen.mem_nhds hxT)) (hBFG'.contDiffAt (hTopen.mem_nhds hxT))]
    change ‖iteratedFDeriv ℝ n H x - iteratedFDeriv ℝ n H y‖ ≤ _
    rw [hdif]
    have h1 := bbound T hTopen F G hF hG n le_rfl x hxT
      ((2 * Af) * Real.rpow ‖x - y‖ α) Ag (by positivity) hAg hFd hGd
    have h2 := bbound T hTopen F' G' hF' hG' n le_rfl x hxT
      Af ((2 * Ag) * Real.rpow ‖x - y‖ α) hAf (by positivity) hF'd hG'd
    have hp : (2 : ℝ) ^ (n + 2) ≤ (2 : ℝ) ^ (2 * n + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      _ ≤ _ + _ := norm_add_le _ _
      _ ≤ (2 : ℝ) ^ n * ‖B‖ * ((2 * Af) * Real.rpow ‖x - y‖ α) * Ag +
          (2 : ℝ) ^ n * ‖B‖ * Af * ((2 * Ag) * Real.rpow ‖x - y‖ α) :=
        add_le_add h1 h2
      _ = (2 : ℝ) ^ (n + 2) * ‖B‖ * Af * Ag * Real.rpow ‖x - y‖ α := by
        rw [pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp (norm_nonneg B)) hAf) hAg) hr


end

end HolomorphicAnosov
