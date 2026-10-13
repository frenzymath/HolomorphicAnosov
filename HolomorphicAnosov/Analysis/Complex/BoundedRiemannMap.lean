import HolomorphicAnosov.Analysis.Complex.ConwaySquareRootCriterionDiskBiholomorphism
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.Deriv.Inverse
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Normalized Riemann maps of bounded simply connected plane domains

This module states node `analysis.marked_rectangle_g3_bounded_riemann_map`.

Sources: Terence Tao, *246A Notes 5: conformal mapping* (18 October 2016), Theorem 4,
Section 3, Propositions 40–41, and Lemma 17 / Theorem 19 on disk automorphisms.
Supplement: Curtis T. McMullen, *Advanced Complex Analysis*, Harvard Math 213a notes,
local title dated January 22, 2017, Theorem 1.15 and Corollaries 1.16–1.18 (p. 10),
Lemmas 4.2–4.4 and the Riemann mapping proof (pp. 58–59).

Local sources: `literature/Tao-246A-Notes5-2016.html` and
`literature/McMullen-Complex-Analysis-213a-2010.pdf`; the latter filename does not
indicate the date printed on its title page.

`SimplyConnectedSpace ↥U` uses the subspace topology of the original domain. Complex
`DifferentiableOn` on an open subset is holomorphy. The two functions below are total
representatives; only their restrictions to the disk and `U` are constrained. The
range and inverse equations explicitly express the biholomorphic correspondence.
No extension to either boundary is asserted.
-/

namespace HolomorphicAnosov

/-- A bounded nonempty open simply connected plane domain admits a normalized
biholomorphic parametrization by the open unit disk.

The positive-real derivative normalization is expressed by zero imaginary part and
strictly positive real part of the genuine complex derivative at zero. Since the
unit disk is open and contains zero, its `DifferentiableOn` hypothesis supplies that
derivative independently of the arbitrary values of the total representative outside
the disk.

Source proof, expanded as in the current DAG node:

1. Tao Notes5 Proposition40 begins by obtaining an injection into the disk. In the bounded case
here no exterior square-root construction is needed: choose R>sup_{z∈U}|z−z₀| and set
a(z)=(z−z₀)/R. This is holomorphic and injective, maps U into D, fixes z₀, and has a′(z₀)=1/R>0. U
is connected because it is nonempty and simply connected. Since U is open and contains z₀ it
contains a positive-radius ball and more than one point; all normal-family and nonconstant
assertions below concern this genuine domain, not a singleton.

2. Following Tao Proposition41, let I be all injective holomorphic g:U→D with g(z₀)=0, and
M=sup_{g∈I}|g′(z₀)|. The affine member makes I nonempty and M≥1/R>0. Choose r>0 with B(z₀,r)⊂U.
For every g∈I the map ζ↦g(z₀+rζ) is a holomorphic disk map fixing zero; the Schwarz derivative
bound gives r|g′(z₀)|≤1. Thus M is finite. By the defining least-upper-bound property choose g_n∈I
with |g_n′(z₀)|→M. This proves all maximizing-sequence guards before using compactness.

3. Expand the bounded-family Montel step of Tao Proposition41 using McMullen Corollary1.18 p10 and
Lemma4.3 p58, whose source proof is Ascoli with derivative estimates. If B(c,t)⊂U, t>0, and g:U→D
is holomorphic, the function G(z)=(t/2)(g(z)−g(c)) maps B(c,t) into the closed radius-t ball
centered at G(c)=0, since |g(z)−g(c)|≤2. Schwarz therefore gives |g′(c)|≤2/t. On a compact K⊂U
choose δ>0 so every point at distance<δ from K has its radius-δ ball in U (a finite interior-ball
cover supplies such a δ). This derivative bound gives |g′|≤2/δ throughout that neighborhood,
uniformly in g. Parametrize the straight segment between sufficiently close z,w∈K by u↦z+u(w−z),
u∈[0,1]. The complex derivative restricts to the real derivative g′(z+u(w−z))(w−z); its norm is at
most (2/δ)|w−z|. The real interval mean-value inequality yields |g(z)−g(w)|≤(2/δ)|z−w|. Hence the
restrictions of every g_n to K are uniformly equicontinuous and take values in the compact closed
unit disk. Apply the existing Arzela–Ascoli compact-closure theorem and compact subsequence
extraction to get a subsequence uniformly convergent on K. The derivative estimate is derived
directly from the existing Schwarz leaf rather than introducing a new Cauchy-estimate obligation.

4. Supply the omitted global diagonal step. Enumerate the closed positive-radius rational-
center/rational-radius disks whose doubled closed disks lie in U; their interiors cover U. Let K_m
be the union of the first m such closed disks. These are increasing compact subsets of U, their
interiors cover U, and every compact subset of U lies in some K_m by the finite-subcover property.
Extract successively on K_1,K_2,…, each time taking a subsequence of the preceding sequence. If
T_m:N→N is the increasing index map at stage m with T_{m+1}=T_m∘σ_{m+1}, the diagonal n_m=T_m(m)
is strictly increasing because σ_{m+1}(m+1)≥m+1. For every fixed j the diagonal tail is a
subsequence of the jth extraction and converges uniformly on K_j. The limits agree on overlaps,
hence define one f:U→ℂ with local uniform convergence g_{n_m}→f. Pointwise convergence gives
f(z₀)=0 and |f(z)|≤1. The locally uniform scalar-limit theorem gives holomorphy on the same open
U, and the derivative-limit theorem gives g_{n_m}′(z₀)→f′(z₀), hence |f′(z₀)|=M>0. In particular f
is nonconstant. This uses bounded Euclidean Ascoli, never the omitted-values Montel theorem or any
uniformization-dependent normal-family provider.

5. Expand the Hurwitz/univalent-limit step using McMullen Lemma4.2 p58. If f(a)=f(b) for distinct
a,b∈U, the analytic function F=f−f(a) is not identically zero because f is nonconstant. The
identity principle excludes a zero germ at b. Local zero factorization gives a positive finite
order m at b and a sufficiently small closed disk K=B̄(b,s)⊂U, avoiding a, such that F is nonzero
on ∂K and b is its only zero in K. The boundary minimum |F| is positive. The functions
F_n=g_{n_m}−g_{n_m}(a) converge uniformly to F on K; for large m their straight boundary
interpolation with F avoids zero. Winding homotopy invariance and the holomorphic disk zero-count
theorem give F_n a positive number m of zeros inside K. Any such c satisfies
g_{n_m}(c)=g_{n_m}(a), with c≠a, contradicting injectivity. Therefore f is injective. Every disk
used has its closure inside U; no general Hurwitz theorem or compactness of normalized maps on a
pre-existing disk is silently assumed.

6. Because f is nonconstant on connected U, the analytic open-mapping theorem makes f(U) open in
ℂ. Its values already lie in the closed unit disk. If |f(a)|=1 at an interior a∈U, openness would
put an ambient neighborhood of that boundary value inside the closed disk, impossible. Thus f maps
U into the OPEN disk D, fixes z₀, is injective and satisfies |f′(z₀)|=M. This verifies f∈I and
attainment of the extremum, including the interior-range step omitted by mere pointwise bounded
convergence.

7. Write explicitly the disk automorphisms used in Tao Theorem19 and Proposition41. For |α|<1 put
A_α(w)=(w−α)/(1−conj(α)w). On D the denominator is nonzero because |conj(α)w|<1, and
1−|A_α(w)|²=((1−|α|²)(1−|w|²))/|1−conj(α)w|²>0. Its inverse is A_α⁻¹(v)=(v+α)/(1+conj(α)v), with
the same denominator and range guards. Direct substitution proves the two inverse identities. Both
rational maps are holomorphic on D, and A_α(α)=0. These calculations establish onto-ness,
injectivity and holomorphicity of the exact maps; no separate disk-automorphism classification is
needed.

8. Suppose f(U) omits α∈D. Since f(z₀)=0, necessarily α≠0. The function q=A_α∘f is holomorphic and
nowhere zero on the SAME simply connected open U. Apply Complex.exists_continuousOn_pow_eq with
X=ℂ and n=2 to obtain a continuous s on U with s²=q there. Then s(a)≠0 for every a∈U and
|s(a)|²=|q(a)|<1, so s maps into D∖{0}. Upgrade its regularity explicitly: for z→a, z≠a,
eventually z∈U and s(z)+s(a)≠0 by continuity and 2s(a)≠0; the identity
(s(z)−s(a))/(z−a)=[(q(z)−q(a))/(z−a)]/[s(z)+s(a)] tends to q′(a)/(2s(a)). The punctured-slope
criterion proves complex differentiability of s at every a, hence holomorphy on U. Equality
s(a)=s(b) implies q(a)=q(b) and then f(a)=f(b), so s is injective. This is the full square-root
premise used in Tao Proposition41; a principal square root on a slit plane is not substituted for
it.

9. Let β=s(z₀) and h=A_β∘s. The preceding exact disk-automorphism facts show h∈I. Put S(w)=w² and
B=A_α⁻¹∘S∘A_β⁻¹, a holomorphic disk self-map. From s²=A_α∘f we get f=B∘h on U, and
β²=q(z₀)=A_α(0)=−α gives B(0)=0. This reverse map is not a rotation: A_β carries any pair t,−t
with 0<|t|<1 to distinct points that S∘A_β⁻¹ sends to the same value, so B is not injective. Tao
Lemma17 gives |B′(0)|<1. To discharge its strictness without leaving a hidden equality-case
theorem, differentiate the displayed rational formulas:
|B′(0)|=2|β|(1−|β|²)/(1−|α|²)=2|β|/(1+|β|²)<1, since 0<|β|<1, |α|=|β|² and (1−|β|)²>0. The
derivative chain rule now gives M=|f′(z₀)|=|B′(0)|·|h′(z₀)|<|h′(z₀)|, contradicting the defining
supremum. The positive M also rules out either factor vanishing. Thus f is onto D.

10. The injective nonconstant holomorphic map f:U→D is open, so its now-bijective inverse ψ:D→U is
continuous: for open V⊂U, ψ⁻¹(V)=f(V) is open. The existing holomorphic-embedding inverse theorem
makes ψ holomorphic; ψ(0)=z₀, and the derivative chain rule gives ψ′(0)f′(z₀)=1. Thus a=ψ′(0)≠0.
Let c=conj(a)/|a|, so |c|=1, and set φ(ζ)=ψ(cζ). Rotation ζ↦cζ is a biholomorphic disk
automorphism, so φ is a holomorphic bijection D→U with holomorphic inverse ζ↦conj(c)f(ζ). Finally
φ(0)=z₀ and φ′(0)=ac=|a|>0 real. This is precisely the statement’s normalization, with no boundary
regularity or extension.

-/
theorem bounded_riemann_map (U : Set ℂ) (hU_nonempty : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U) (hU_open : IsOpen U)
    [SimplyConnectedSpace ↥U] (z₀ : ℂ) (hz₀ : z₀ ∈ U) :
    ∃ φ ψ : ℂ → ℂ,
      DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) ∧
      DifferentiableOn ℂ ψ U ∧
      Set.BijOn φ (Metric.ball (0 : ℂ) 1) U ∧
      Set.MapsTo ψ U (Metric.ball (0 : ℂ) 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, ψ (φ z) = z) ∧
      (∀ z ∈ U, φ (ψ z) = z) ∧
      φ 0 = z₀ ∧
      (deriv φ 0).im = 0 ∧
      0 < (deriv φ 0).re := by
  classical
  have hsc : IsSimplyConnected U := (inferInstance : SimplyConnectedSpace ↥U)
  have hconnected : IsConnected U := ⟨hU_nonempty, hsc.isPathConnected.isConnected.2⟩
  have hproper : U ≠ Set.univ := by
    intro h
    exact NormedSpace.unbounded_univ ℂ ℂ (h ▸ hU_bounded)
  have hsqrt : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, (g z) ^ 2 = f z := by
    intro f hf hfzero
    have hzero : (0 : ℂ) ∉ f '' U := by
      rintro ⟨z, hz, he⟩
      exact hfzero z hz he
    obtain ⟨g, hgc, hgf⟩ := Complex.exists_continuousOn_pow_eq hsc hU_open
      hf.continuousOn hzero (n := 2) (by norm_num)
    refine ⟨g, ?_, fun z _ ↦ hgf z⟩
    intro z hz
    have hgzero : g z ≠ 0 := by
      intro he
      apply hfzero z hz
      rw [← hgf z, he]
      simp
    have hd : HasDerivAt (fun w : ℂ ↦ w ^ 2) (2 * g z) (g z) := by
      simpa using hasDerivAt_pow 2 (g z)
    have hdg : HasDerivAt g (deriv f z / (2 * g z)) z :=
      hd.of_comp_left (hgc.continuousAt (hU_open.mem_nhds hz))
        ((hf z hz).differentiableAt (hU_open.mem_nhds hz)).hasDerivAt
        (mul_ne_zero (by norm_num) hgzero) (Filter.Eventually.of_forall hgf)
    exact hdg.differentiableAt.differentiableWithinAt
  obtain ⟨F, G, hF, hG, hbij, hmaps, hGF, hFG, hF0, hFre, hFpos⟩ :=
    -- The existing source criterion carries the extremal normal-family argument.
    -- This specialization does not claim to discharge that lower admission.
    conway_square_root_criterion_disk_biholomorphism hU_open hconnected
      hproper hsqrt z₀ hz₀
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hG0 : G 0 = z₀ := by simpa [hF0] using hGF z₀ hz₀
  have hdF : HasDerivAt F (deriv F z₀) (G 0) := by
    rw [hG0]
    exact ((hF z₀ hz₀).differentiableAt (hU_open.mem_nhds hz₀)).hasDerivAt
  have hFne : deriv F z₀ ≠ 0 := by
    intro he
    simp [he] at hFpos
  have hdG : HasDerivAt G (deriv F z₀)⁻¹ 0 :=
    hdF.of_local_left_inverse
      (hG.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0)) hFne
      (Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds h0) fun z hz ↦ hFG z hz)
  refine ⟨G, F, hG, hF, ?_, hbij.mapsTo, hFG, hGF, hG0, ?_, ?_⟩
  · exact hbij.symm ⟨hFG, hGF⟩
  · rw [hdG.deriv, Complex.inv_im, hFre]
    simp
  · rw [hdG.deriv, Complex.inv_re]
    exact div_pos hFpos (Complex.normSq_pos.mpr hFne)

end HolomorphicAnosov

