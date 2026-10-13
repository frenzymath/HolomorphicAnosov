import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.ContinuousMap.CocompactMap
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Affine automorphisms of the complex plane

Source: Curtis T. McMullen, *Advanced Complex Analysis*, Harvard Math 213a course
notes, dated January 22, 2017, printed p.28 (PDF29), Theorem 2.2 and Corollary 2.3.
The corresponding DAG node is `analysis.complex_plane_biholomorphism_affine`.
-/

open Filter Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- Entire mutually inverse maps of the complex plane have a unique nonzero affine
coefficient pair; conversely, every such pair defines mutually inverse entire maps.
Here `Differentiable ℂ` expresses holomorphicity on the entire complex plane, and
uniqueness is uniqueness of the ordered pair `(a, b)`.

Source: McMullen, *Advanced Complex Analysis*, printed p.28, Theorem 2.2 and
Corollary 2.3; isolation of zeros p.8 and the Cauchy polynomial-growth bound,
Theorem 1.12, p.9. Power-series details: Demailly, *Complex Analytic and
Differential Geometry*, June 21, 2012, I §3.B p.22, (3.9)–(3.11).

Proof: The two maps are continuous inverse bijections. The inverse image under
`F` of a closed ball is its continuous image under `G`, hence compact and bounded.
Consequently `|F(z)|` tends to infinity as `|z|` tends to infinity. On a small
punctured disk put `u(ζ) = 1 / F(1 / ζ)` and put `u(0) = 0`. This is holomorphic
off zero and continuous at zero, so the removable-singularity theorem makes it
analytic there. Its germ is nonzero, since it never vanishes on that punctured
disk. Finite-zero factorization gives `u(ζ) = ζ^n v(ζ)` with `v(0) ≠ 0` and
`n ≥ 1`. On a smaller disk `|v|` is bounded below by a positive constant, so
`|F(z)| ≤ C |z|^n` for sufficiently large `|z|`.

The one-variable Cauchy power-series estimate at zero bounds the coefficient
of order `k` by `C R^(n-k)` for large radii `R`. If `k > n`, sending `R` to infinity
makes this coefficient zero. The same coefficients represent `F` on every disk,
so `F` is a polynomial `P`. Repeating the argument for `G` gives a polynomial
`Q`. Neither is constant. Since `Q(P(z)) = z` at every complex number, the
infinite-roots theorem gives `Q.comp P = X`. If their positive degrees are `r`
and `s`, the leading term of the composite has nonzero coefficient and degree
`r*s`; thus `r*s = 1` and both degrees are one.

Write `P(X) = a*X + b`; its degree gives `a ≠ 0`. The inverse identities then
give `G(w) = (w-b)/a`. Evaluation at zero fixes `b = F(0)` and evaluation at one
fixes `a = F(1)-F(0)`, proving uniqueness. Conversely the two displayed affine
functions are entire when `a ≠ 0`, and substitution proves both inverse
identities. That is the published polynomial-growth route. The kernel proof
below instead uses an agent-written divided-difference/Liouville argument:
the chain rule makes `F'(0)` nonzero, removable divided differences make
`D(z) = dslope F 0 z`, `H = 1 / D`, and `K = dslope H 0` entire, and properness
gives `K(z) = 1 / (F(z)-F(0)) - 1 / (F'(0)*z)` tending to zero at infinity.
Liouville gives `K = 0`, hence `H` and `D` are constant and `F` is affine.
The same inverse, uniqueness and converse algebra then finishes the statement.
-/
theorem complex_plane_biholomorphism_affine :
    (∀ F G : ℂ → ℂ,
      Differentiable ℂ F → Differentiable ℂ G →
      (∀ z : ℂ, G (F z) = z) → (∀ w : ℂ, F (G w) = w) →
      ∃! ab : ℂ × ℂ,
        ab.1 ≠ 0 ∧
        (∀ z : ℂ, F z = ab.1 * z + ab.2) ∧
        (∀ w : ℂ, G w = (w - ab.2) / ab.1)) ∧
    (∀ a b : ℂ, a ≠ 0 →
      Differentiable ℂ (fun z : ℂ => a * z + b) ∧
      Differentiable ℂ (fun w : ℂ => (w - b) / a) ∧
      (∀ z : ℂ, (a * z + b - b) / a = z) ∧
      (∀ w : ℂ, a * ((w - b) / a) + b = w)) := by
  -- Mathlib-only pruning of the polynomial route: the inverse supplies properness
  -- and a nonzero derivative at zero. Removability makes D(z)=dslope F 0 z entire;
  -- injectivity and the chain rule make D nowhere zero. Hence H=1/D and K=dslope H 0
  -- are entire. Away from zero K(z)=1/(F(z)-F(0))-1/(F'(0)*z), which tends to zero
  -- at infinity by properness. Liouville gives K=0, then H and D are constant.
  -- Thus F(z)=F'(0)*z+F(0); the inverse law and evaluation at zero/one supply G
  -- and uniqueness. This argument introduces no growth or boundedness premise.
  classical
  constructor
  · intro F G hF hG hGF hFG
    have hinj : Function.Injective F := Function.LeftInverse.injective hGF
    have hderiv : deriv F 0 ≠ 0 := by
      have hchain := (hG (F 0)).hasDerivAt.comp 0 (hF 0).hasDerivAt
      have hid : HasDerivAt (fun z : ℂ ↦ z) (deriv G (F 0) * deriv F 0) 0 := by
        simpa only [Function.comp_def, hGF] using hchain
      have heq := hid.unique (hasDerivAt_id 0)
      intro hz
      simp [hz] at heq
    have hd : Differentiable ℂ (dslope F 0) := by
      apply differentiableOn_univ.mp
      exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr
        hF.differentiableOn
    have hn : ∀ z, dslope F 0 z ≠ 0 := by
      intro z
      by_cases hz : z = 0
      · simpa [hz] using hderiv
      · rw [dslope_of_ne F hz, slope, sub_zero, smul_eq_mul]
        exact mul_ne_zero (inv_ne_zero hz) (sub_ne_zero.mpr (fun heq ↦ hz (hinj heq)))
    let H : ℂ → ℂ := fun z ↦ (dslope F 0 z)⁻¹
    have hH : Differentiable ℂ H := hd.inv hn
    let K := dslope H 0
    have hK : Differentiable ℂ K := by
      apply differentiableOn_univ.mp
      exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr
        hH.differentiableOn
    let e : ℂ ≃ₜ ℂ :=
      { toEquiv := ⟨F, G, hGF, hFG⟩
        continuous_toFun := hF.continuous
        continuous_invFun := hG.continuous }
    have hproper : Tendsto F (cocompact ℂ) (cocompact ℂ) :=
      e.toCocompactMap.cocompact_tendsto'
    have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    have hsubproper : Tendsto (fun z ↦ F z - F 0) (cocompact ℂ) (cocompact ℂ) := by
      have ht := (Homeomorph.addRight (-F 0)).toCocompactMap.cocompact_tendsto'
      have ht' : Tendsto (fun z : ℂ ↦ z + (-F 0)) (cocompact ℂ) (cocompact ℂ) := ht
      simpa [sub_eq_add_neg, Function.comp_def] using ht'.comp hproper
    have ht : Tendsto (fun z : ℂ ↦ (F z - F 0)⁻¹ - (deriv F 0)⁻¹ * z⁻¹)
        (cocompact ℂ) (𝓝 0) := by
      simpa using (hinv.comp hsubproper).sub (hinv.const_mul (deriv F 0)⁻¹)
    have hevent : K =ᶠ[cocompact ℂ]
        (fun z : ℂ ↦ (F z - F 0)⁻¹ - (deriv F 0)⁻¹ * z⁻¹) := by
      filter_upwards [isCompact_singleton.compl_mem_cocompact (s := ({0} : Set ℂ))]
        with z hz
      have hz0 : z ≠ 0 := by simpa using hz
      dsimp [K, H]
      rw [dslope_of_ne _ hz0, slope, sub_zero, smul_eq_mul,
        dslope_of_ne F hz0, slope, sub_zero, smul_eq_mul, dslope_same]
      simp only [vsub_eq_sub]
      field_simp [hz0, hderiv]
    have hzero : K = Function.const ℂ 0 :=
      hK.eq_const_of_tendsto_cocompact (ht.congr' hevent.symm)
    have hHconst (z : ℂ) : H z = (deriv F 0)⁻¹ := by
      have hm := sub_smul_dslope H 0 z
      have hk : K z = 0 := congrFun hzero z
      rw [sub_zero] at hm
      change z • K z = H z - H 0 at hm
      rw [hk, smul_zero] at hm
      have heq : H z = H 0 := sub_eq_zero.mp hm.symm
      simpa [H] using heq
    have hds (z : ℂ) : dslope F 0 z = deriv F 0 := by
      exact inv_injective (hHconst z)
    have hFa (z : ℂ) : F z = deriv F 0 * z + F 0 := by
      have hm := sub_smul_dslope F 0 z
      rw [sub_zero, hds, smul_eq_mul] at hm
      linear_combination -hm
    have hGa (w : ℂ) : G w = (w - F 0) / deriv F 0 := by
      have heq := hFa (G w)
      rw [hFG] at heq
      apply (eq_div_iff hderiv).mpr
      linear_combination -heq
    refine ⟨(deriv F 0, F 0), ⟨hderiv, hFa, hGa⟩, ?_⟩
    rintro ⟨a, b⟩ ⟨ha, hF', hG'⟩
    have hb : b = F 0 := by simpa using (hF' 0).symm
    have ha' : a = deriv F 0 := by
      have heq := hF' 1
      rw [hFa, hb] at heq
      linear_combination -heq
    exact Prod.ext ha' hb
  · intro a b ha
    refine ⟨((differentiable_const a).mul differentiable_id).add (differentiable_const b),
      (differentiable_id.sub (differentiable_const b)).div_const a, ?_, ?_⟩
    · intro z
      field_simp
      ring
    · intro w
      field_simp
      ring

end HolomorphicAnosov

