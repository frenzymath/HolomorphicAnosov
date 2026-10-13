import HolomorphicAnosov.Analysis.Complex.ConwaySquareRootCriterionPositiveSeed
import HolomorphicAnosov.Analysis.Complex.ConwayExtremalDiskMap
import HolomorphicAnosov.Analysis.Complex.ConwaySquareRootDerivativeImprovement
import HolomorphicAnosov.Analysis.Complex.HolomorphicBijOnInverse

/-!
# Conway's square-root criterion for a normalized disk biholomorphism

Source: John B. Conway, *Functions of One Complex Variable*, second edition (1978),
Chapter VII, Lemma 4.3, printed pp. 161–163 (PDF pp. 172–174).
DAG node: `analysis.conway_square_root_criterion_disk_biholomorphism`.
-/

namespace HolomorphicAnosov

/-- Conway, Chapter VII, Lemma 4.3, printed pp. 161–163: a proper complex region with
the holomorphic square-root property admits a normalized biholomorphism to the unit disk.
For the normal-family and injective-limit ingredients, see also McMullen, *Advanced Complex
Analysis*, Corollary 1.18, printed p. 10, and Lemmas 4.2–4.3, printed pp. 58–59.

Here `IsConnected U` includes nonemptiness. On an open subset of `ℂ`, `DifferentiableOn ℂ`
is precisely holomorphy (equivalently `AnalyticOnNhd ℂ`). The total functions `F` and `G`
represent maps on their indicated open domains; their values elsewhere are unrestricted.
`BijOn` and the two inverse identities assert that `G` is the actual inverse of `F` between
`U` and `Metric.ball 0 1`. The last two conditions say the complex derivative is positive real.

Natural-language proof:
Choose `b` outside `U`. By the square-root hypothesis choose holomorphic `g` with
`g(z)^2 = z-b` on `U`. It is nowhere zero and injective. Its image and its negative are
disjoint: `g(x) = -g(y)` implies `x=y` by squaring and then `g(x)=0`, a contradiction.
The open mapping theorem supplies `r>0` with the disk of radius `r` around `g(a)` inside
`g(U)`. Its negative disk misses `g(U)`, so `|w+g(a)| ≥ r` for `w` in `g(U)`. Consequently
`T(w) = (r/2)/(w+g(a))` is injective on that image and has modulus at most `1/2` there.
Composing `T ∘ g` with a disk automorphism taking its value at `a` to zero and a rotation
gives an injective holomorphic map `U → D` with positive real derivative at `a`. An injective
holomorphic map is open, hence a homeomorphism onto its open image; the local holomorphic
inverse theorem gives a nonzero derivative, which justifies this phase normalization.

Let the normalized family consist of all injective holomorphic maps `U → D` taking `a`
to zero with positive real derivative at `a`. The family is nonempty by the preceding
construction. On each sufficiently small disk with its closed double-radius disk in `U`,
the translated and rescaled Schwarz derivative bound gives a uniform derivative bound.
The segment mean-value estimate gives equicontinuity. A finite disk cover handles any
compact subset of `U`. Values lie in the compact closed unit disk. Arzelà–Ascoli, applied
successively on a countable compact exhaustion and followed by diagonal extraction, gives
a subsequence converging uniformly on every compact set to a holomorphic `f`. Derivatives
also converge locally uniformly. Thus `f(a)=0`, `f'(a)` is real and nonnegative, and `|f|≤1`.
If `f` is nonconstant, the open mapping theorem implies that its values lie in `D`.

A nonconstant limit is injective. Otherwise take distinct `x,y` with `f(x)=f(y)` and a
small closed disk about `y` excluding `x` on which `f-f(x)` has its sole zero at `y` and
no boundary zero. Isolation and local factorization give its boundary winding a positive
integer value, the multiplicity of that zero. Compact uniform convergence makes the
straight boundary homotopy to `f_n-f_n(x)` nonvanishing for large `n`, so winding is
preserved. The holomorphic zero-count theorem then forces a zero of `f_n-f_n(x)` inside
the disk, contradicting injectivity since `x` is outside. Therefore a nonconstant limit
is injective, has nonzero derivative, and has positive derivative at `a`. A constant
limit is zero because its value at `a` is zero.

The local Schwarz bound makes the positive derivatives at `a` bounded above. Their
supremum `M` is positive because the family is nonempty. Choose normalized maps whose
derivatives tend to `M`. The compact-convergence subsequence has derivative `M` at `a`,
so its limit is nonconstant and belongs to the family. It is an extremal map `f`.

If `w ∈ D` is omitted by `f`, then `w ≠ 0`. The function
`q = (f-w)/(1-conj(w)*f)` is a nowhere-zero holomorphic injection into `D`. Choose a
holomorphic square root `h` by hypothesis. Squaring proves `h` injective, and `|h|<1`.
Put `β=h(a)`, so `β^2=-w` and `0<|β|<1`. Compose `h` with the disk automorphism taking
`β` to zero, then rotate its nonzero derivative to positive real. The resulting normalized
map `k` satisfies, by differentiating `h^2=q` and the rational automorphism formulas,
`k'(a) = f'(a)*(1+|w|)/(2*sqrt(|w|)) > f'(a)`. The strict inequality follows from
`(1-sqrt(|w|))^2>0`. All denominators are nonzero because the corresponding values have
modulus less than one. This contradicts extremality, proving `f(U)=D`.

The injective holomorphic surjection `f` is open, and therefore a homeomorphism `U → D`.
Its inverse is holomorphic by the holomorphic inverse theorem. Extend each map arbitrarily
outside its open domain to obtain the displayed total functions and inverse identities.
-/
theorem conway_square_root_criterion_disk_biholomorphism
    {U : Set ℂ} (hUopen : IsOpen U) (hUconnected : IsConnected U)
    (hUproper : U ≠ Set.univ)
    (hsqrt : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, (g z) ^ 2 = f z)
    (a : ℂ) (ha : a ∈ U) :
    ∃ F G : ℂ → ℂ,
      DifferentiableOn ℂ F U ∧
      DifferentiableOn ℂ G (Metric.ball (0 : ℂ) 1) ∧
      Set.BijOn F U (Metric.ball (0 : ℂ) 1) ∧
      Set.MapsTo G (Metric.ball (0 : ℂ) 1) U ∧
      (∀ z ∈ U, G (F z) = z) ∧
      (∀ w ∈ Metric.ball (0 : ℂ) 1, F (G w) = w) ∧
      F a = 0 ∧ (deriv F a).im = 0 ∧ 0 < (deriv F a).re := by
  obtain ⟨f₀, hf₀, hi₀, hm₀, hz₀, him₀, hpos₀⟩ :=
    conway_square_root_criterion_positive_seed hUopen hUconnected hUproper hsqrt a ha
  have hd₀ : deriv f₀ a ≠ 0 := by
    intro h
    simp [h] at hpos₀
  obtain ⟨f, hf, hi, hm, hz, hd, hmax⟩ :=
    conway_extremal_disk_map hUopen hUconnected.isPreconnected ha
      ⟨f₀, hf₀, hi₀, hm₀, hz₀, hd₀⟩
  have hsurj : Set.SurjOn f U (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    by_contra hn
    obtain ⟨k, hk, hki, hkm, hkz, hkd⟩ :=
      conway_square_root_derivative_improvement hUopen hsqrt ha hf hi hm hz hd
        (mem_ball_zero_iff.mp hw) hn
    exact (not_lt_of_ge (hmax k hk hki hkm hkz)) hkd
  let c : ℂ := (‖deriv f a‖ : ℂ) / deriv f a
  have hc : ‖c‖ = 1 := by simp [c, hd]
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
  let F : ℂ → ℂ := fun z ↦ c * f z
  have hF : DifferentiableOn ℂ F U := hf.const_mul c
  have hFi : Set.InjOn F U := by
    intro z hz w hw he
    exact hi hz hw (mul_left_cancel₀ hc0 he)
  have hFm : Set.MapsTo F U (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    simpa only [F, mem_ball_zero_iff, norm_mul, hc, one_mul] using hm hz
  have hFs : Set.SurjOn F U (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    have hdiv : w / c ∈ Metric.ball (0 : ℂ) 1 := by
      simpa only [mem_ball_zero_iff, norm_div, hc, div_one] using hw
    obtain ⟨z, hz, he⟩ := hsurj hdiv
    refine ⟨z, hz, ?_⟩
    change c * f z = w
    rw [he, mul_div_cancel₀ _ hc0]
  obtain ⟨G, hG, hGm, hGF, hFG⟩ :=
    holomorphic_bijOn_inverse hUopen hF ⟨hFm, hFi, hFs⟩
  have hder : deriv F a = (‖deriv f a‖ : ℂ) := by
    rw [((hf.differentiableAt (hUopen.mem_nhds ha)).hasDerivAt.const_mul c).deriv]
    exact div_mul_cancel₀ _ hd
  exact ⟨F, G, hF, hG, ⟨hFm, hFi, hFs⟩, hGm, hGF, hFG,
    by simp [F, hz], by simp [hder], by simpa [hder] using norm_pos_iff.mpr hd⟩

end HolomorphicAnosov
