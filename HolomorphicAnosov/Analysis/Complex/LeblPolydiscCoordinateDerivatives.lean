import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.SeparatelyHolomorphicSmooth
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.List.FinRange
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.Perm.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Ordered holomorphic coordinate derivatives on a polydisc

Source: Jiří Lebl, *Tasty Bits of Several Complex Variables*, version 3.4,
December 23, 2020, Proposition 1.1.3, pp.12–13; Proposition 1.2.2 and its
kernel-differentiation proof, pp.19–20; Theorem 1.2.6, p.21.

The coordinate space is `Fin d → ℂ` with its ordinary finite-product norm.
The local definitions below fix the order of derivatives and of the nested
counterclockwise circle integrals. No symmetry of mixed derivatives is built
into a definition, and values or derivatives outside the given open set are
unrestricted. The proof differentiates the actual finite ordered Cauchy integral;
source regularity and Cauchy-series providers remain explicit imports.
-/

namespace HolomorphicAnosov.Analysis.Complex

open scoped ContDiff

noncomputable section

namespace LeblPolydisc

variable {d : ℕ}

/-- The coordinate unit vector of Lebl's coordinate derivative convention,
pp.12–13. -/
def coordinateVector (j : Fin d) : Fin d → ℂ := Pi.single j 1

/-- Lebl's coordinate partial derivative, pp.12–13, as evaluation of the
complex Fréchet derivative on the coordinate unit vector. -/
def coordinateDerivative (j : Fin d) (q : (Fin d → ℂ) → ℂ) : (Fin d → ℂ) → ℂ :=
  fun z ↦ (fderiv ℂ q z) (coordinateVector j)

/-- Ordered derivatives from Lebl's repeated-kernel calculation, pp.19–20.
The left fold has `Q_[] = f` and `Q_(J ++ [j]) = P_j(Q_J)`. -/
def orderedDerivative (f : (Fin d → ℂ) → ℂ) (J : List (Fin d)) : (Fin d → ℂ) → ℂ :=
  J.foldl (fun q j ↦ coordinateDerivative j q) f

/-- The increasing coordinate list in the multi-index convention of
Lebl Proposition 1.2.2, pp.19–20. -/
def multiIndexList (α : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap (fun j ↦ List.replicate (α j) j)

/-- The deterministically ordered multi-index derivative in Lebl
Proposition 1.2.2, pp.19–20. -/
def multiIndexDerivative (f : (Fin d → ℂ) → ℂ) (α : Fin d → ℕ) : (Fin d → ℂ) → ℂ :=
  orderedDerivative f (multiIndexList α)

/-- The open coordinate polydisc of Lebl Proposition 1.2.2, p.19. -/
def openPolydisc (a : Fin d → ℂ) (R : Fin d → ℝ) : Set (Fin d → ℂ) :=
  {z | ∀ j, ‖z j - a j‖ < R j}

/-- The closed coordinate polydisc used for the boundary hypotheses of
Lebl Proposition 1.2.2, pp.19–20. -/
def closedPolydisc (a : Fin d → ℂ) (R : Fin d → ℝ) : Set (Fin d → ℂ) :=
  {z | ∀ j, ‖z j - a j‖ ≤ R j}

/-- The multi-index factorial in Lebl Proposition 1.2.2, pp.19–20. -/
def multiIndexFactorial (α : Fin d → ℕ) : ℕ := ∏ j, (α j).factorial

/-- Successive counterclockwise circle integration in the displayed order
of Lebl (1.1), p.13: the head of the list is the outermost circle. -/
def successiveCircleIntegral (a : Fin d → ℂ) (R : Fin d → ℝ) :
    List (Fin d) → ((Fin d → ℂ) → ℂ) → ℂ
  | [], q => q a
  | j :: J, q => circleIntegral
      (fun ζ ↦ successiveCircleIntegral a R J (fun w ↦ q (Function.update w j ζ)))
      (a j) (R j)

/-- Lebl's distinguished-boundary integral, (1.1), p.13, with coordinate
zero outermost and all circles oriented counterclockwise. -/
def distinguishedBoundaryIntegral (a : Fin d → ℂ) (R : Fin d → ℝ)
    (q : (Fin d → ℂ) → ℂ) : ℂ :=
  successiveCircleIntegral a R (List.finRange d) q

/-- The multi-index Cauchy kernel of Lebl Proposition 1.2.2, pp.19–20.
Its negative powers are literal reciprocals of positive natural powers. -/
def cauchyKernel (f : (Fin d → ℂ) → ℂ) (α : Fin d → ℕ) (z : Fin d → ℂ) :
    (Fin d → ℂ) → ℂ :=
  fun ζ ↦ f ζ * ∏ j, ((ζ j - z j) ^ (α j + 1))⁻¹

/-- The Cauchy coefficient in Lebl Proposition 1.2.2, pp.19–20, using the
same distinguished-boundary order and normalization as the derivative formula. -/
def cauchyCoefficient (f : (Fin d → ℂ) → ℂ) (a : Fin d → ℂ) (R : Fin d → ℝ)
    (α : Fin d → ℕ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ d)⁻¹ *
    distinguishedBoundaryIntegral a R (cauchyKernel f α a)

/-- Full finite-product holomorphy gives smoothness through the published
separate-holomorphy theorem, with scalar target embedded in its one-coordinate
product. No one-variable source theorem is applied to the multivariable domain. -/
theorem contDiffOn_of_holomorphic {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f : (Fin d → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ ∞ f U := by
  have hprod : ContDiffOn ℂ ∞ (fun z (_ : Fin 1) ↦ f z) U := by
    apply HolomorphicAnosov.contDiffOn_of_continuousOn_separately_holomorphic hU
    · exact continuousOn_pi.mpr (fun _ ↦ hf.continuousOn)
    · intro z j
      apply differentiableOn_pi.mpr
      intro k
      exact hf.comp ((contDiff_update (𝕜 := ℂ) ∞ z j).differentiable (by simp)).differentiableOn
        (fun _ ht ↦ ht)
  exact (contDiffOn_pi.mp hprod) 0

/-- Differentiating the actual smooth function and evaluating at its fixed
coordinate vector preserves smoothness on the SAME open set. -/
theorem coordinateDerivative_contDiffOn {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f : (Fin d → ℂ) → ℂ} (hf : ContDiffOn ℂ ∞ f U) (j : Fin d) :
    ContDiffOn ℂ ∞ (coordinateDerivative j f) U := by
  exact (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- Finite left-fold derivative iteration preserves actual smoothness and
holomorphy, with no conclusion about values outside the original open set. -/
theorem orderedDerivative_regular {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f : (Fin d → ℂ) → ℂ} (hf : ContDiffOn ℂ ∞ f U) (J : List (Fin d)) :
    ContDiffOn ℂ ∞ (orderedDerivative f J) U ∧
      DifferentiableOn ℂ (orderedDerivative f J) U := by
  have hs : ContDiffOn ℂ ∞ (orderedDerivative f J) U := by
    induction J generalizing f with
    | nil => exact hf
    | cons j J ih => exact ih (coordinateDerivative_contDiffOn hU hf j)
  exact ⟨hs, hs.differentiableOn (by simp)⟩

/-- A local equality on an open set gives equality of its actual coordinate
Fréchet derivatives, including their totalizations. -/
theorem coordinateDerivative_congr {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f g : (Fin d → ℂ) → ℂ} (heq : Set.EqOn f g U) (j : Fin d) :
    Set.EqOn (coordinateDerivative j f) (coordinateDerivative j g) U := by
  intro z hz
  have hlocal : f =ᶠ[nhds z] g := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact heq hy
  exact congrArg (fun D : (Fin d → ℂ) →L[ℂ] ℂ ↦ D (coordinateVector j)) hlocal.fderiv_eq

/-- Equality of ordered derivatives propagates through their remaining list
using only the original open-set germ. -/
theorem orderedDerivative_congr {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f g : (Fin d → ℂ) → ℂ} (heq : Set.EqOn f g U) (J : List (Fin d)) :
    Set.EqOn (orderedDerivative f J) (orderedDerivative g J) U := by
  induction J generalizing f g with
  | nil => exact heq
  | cons j J ih => exact ih (coordinateDerivative_congr hU heq j)

/-- Symmetry of the genuine second Fréchet derivative proves the coordinate
swap; it is not built into the derivative definitions. -/
theorem coordinateDerivative_commute {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f : (Fin d → ℂ) → ℂ} (hf : ContDiffOn ℂ ∞ f U) (i j : Fin d) :
    Set.EqOn (coordinateDerivative i (coordinateDerivative j f))
      (coordinateDerivative j (coordinateDerivative i f)) U := by
  intro z hz
  have hD := ((hf.contDiffAt (hU.mem_nhds hz)).fderiv_right
    (m := 1) (by simp)).differentiableAt one_ne_zero
  have hi := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector i) z)
  have hj := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector j) z)
  have hsym := (hf.contDiffAt (hU.mem_nhds hz)).isSymmSndFDerivAt (by simp)
  have hei : fderiv ℂ (coordinateDerivative i f) z =
      (fderiv ℂ (fderiv ℂ f) z).flip (coordinateVector i) := by
    convert! hi.fderiv using 1
    simp
  have hej : fderiv ℂ (coordinateDerivative j f) z =
      (fderiv ℂ (fderiv ℂ f) z).flip (coordinateVector j) := by
    convert! hj.fderiv using 1
    simp
  change fderiv ℂ (coordinateDerivative j f) z (coordinateVector i) =
    fderiv ℂ (coordinateDerivative i f) z (coordinateVector j)
  rw [hei, hej]
  exact hsym.eq (coordinateVector i) (coordinateVector j)

/-- Permuting an actual finite derivative list preserves its value on U:
induct through list swaps, using second-derivative symmetry at each smooth
intermediate function and preserving every subsequent derivative germ. -/
theorem orderedDerivative_perm {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f : (Fin d → ℂ) → ℂ} (hf : ContDiffOn ℂ ∞ f U)
    {J K : List (Fin d)} (hJK : J.Perm K) :
    Set.EqOn (orderedDerivative f J) (orderedDerivative f K) U := by
  induction hJK generalizing f with
  | nil => intro z hz; rfl
  | cons j h ih => exact ih (coordinateDerivative_contDiffOn hU hf j)
  | swap i j J =>
      exact orderedDerivative_congr hU (coordinateDerivative_commute hU hf i j) J
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ hf).trans (ih₂ hf)

/-- The count criterion turns the proved permutation invariance into exact
multi-index order independence. -/
theorem orderedDerivative_eq_of_count {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f : (Fin d → ℂ) → ℂ} (hf : ContDiffOn ℂ ∞ f U)
    (J K : List (Fin d)) (hcount : ∀ j, J.count j = K.count j) :
    Set.EqOn (orderedDerivative f J) (orderedDerivative f K) U :=
  orderedDerivative_perm hU hf (List.perm_iff_count.mpr hcount)

/-- The increasing multi-index list has exactly its prescribed occurrence
counts, proved from literal replication rather than a symmetry convention. -/
theorem multiIndexList_count (α : Fin d → ℕ) (j : Fin d) :
    (multiIndexList α).count j = α j := by
  have hcount (L : List (Fin d)) :
      (L.flatMap (fun i ↦ List.replicate (α i) i)).count j = L.count j * α j := by
    induction L with
    | nil => simp
    | cons i L ih =>
      by_cases hij : i = j
      · subst i
        simp [ih, Nat.add_mul, Nat.add_comm]
      · simp [ih, hij, List.count_replicate]
  simpa only [multiIndexList, List.count_finRange, one_mul] using hcount (List.finRange d)

/-- Appending one actual coordinate derivative increments its count index.
The identification is a consequence of the proved order independence. -/
theorem multiIndexDerivative_increment {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f : (Fin d → ℂ) → ℂ} (hf : ContDiffOn ℂ ∞ f U)
    (α : Fin d → ℕ) (j : Fin d) :
    Set.EqOn (coordinateDerivative j (multiIndexDerivative f α))
      (multiIndexDerivative f (α + Pi.single j 1)) U := by
  have hcount : ∀ i, ((multiIndexList α) ++ [j]).count i =
      (multiIndexList (α + Pi.single j 1)).count i := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [multiIndexList_count]
    · simp [multiIndexList_count, hij, Ne.symm hij]
  have h := orderedDerivative_eq_of_count hU hf
    ((multiIndexList α) ++ [j]) (multiIndexList (α + Pi.single j 1)) hcount
  simpa only [orderedDerivative, List.foldl_append, List.foldl_cons, List.foldl_nil,
    multiIndexDerivative] using h

/-- Function extensionality of the actual nested integral does not require
any holomorphy or integrability assumptions. -/
theorem successiveCircleIntegral_congr (a : Fin d → ℂ) (R : Fin d → ℝ)
    (J : List (Fin d)) {f g : (Fin d → ℂ) → ℂ} (h : f = g) :
    successiveCircleIntegral a R J f = successiveCircleIntegral a R J g := by
  rw [h]

/-- Integrating successor coordinates preserves the fixed coordinate zero;
the literal update recursion then equals the lower-dimensional tail recursion. -/
theorem successiveCircleIntegral_succ (a : Fin (d + 1) → ℂ) (R : Fin (d + 1) → ℝ)
    (J : List (Fin d)) (q : (Fin (d + 1) → ℂ) → ℂ) :
    successiveCircleIntegral a R (J.map Fin.succ) q =
      successiveCircleIntegral (Fin.tail a) (Fin.tail R) J
        (fun w ↦ q (Fin.cons (a 0) w)) := by
  induction J generalizing q with
  | nil => simp [successiveCircleIntegral, Fin.cons_self_tail]
  | cons j J ih =>
    simp only [List.map_cons, successiveCircleIntegral, Fin.tail]
    congr 1
    funext ζ
    rw [ih]
    congr 1
    funext w
    rw [← Fin.cons_update]

/-- The Lebl list-update integral is EXACTLY the published native Fin.cons
boundary integral. The proof checks the different recursions, including the
empty dimension, rather than declaring their equality by notation. -/
theorem distinguishedBoundaryIntegral_eq_native (a : Fin d → ℂ) (R : Fin d → ℝ)
    (q : (Fin d → ℂ) → ℂ) :
    distinguishedBoundaryIntegral a R q =
      HolomorphicAnosov.PolydiscBoundaryCauchySeries.iteratedCircleIntegral d a R q := by
  induction d with
  | zero =>
      simp only [distinguishedBoundaryIntegral, List.finRange_zero,
        successiveCircleIntegral,
        HolomorphicAnosov.PolydiscBoundaryCauchySeries.iteratedCircleIntegral]
      congr 1
      ext j
      exact Fin.elim0 j
  | succ d ih =>
      simp only [distinguishedBoundaryIntegral, List.finRange_succ,
        successiveCircleIntegral,
        HolomorphicAnosov.PolydiscBoundaryCauchySeries.iteratedCircleIntegral]
      congr 1
      funext ζ
      rw [successiveCircleIntegral_succ]
      have hfun : (fun w ↦ q (Function.update (Fin.cons (a 0) w) 0 ζ)) =
          (fun w ↦ q (Fin.cons ζ w)) := by
        funext w
        rw [Fin.update_cons_zero]
      rw [hfun]
      exact ih (Fin.tail a) (Fin.tail R) (fun w ↦ q (Fin.cons ζ w))

/-- The prescribed Cauchy coefficient agrees with the native provider's
coefficient, with the SAME normalization, circle order and literal powers. -/
theorem cauchyCoefficient_eq_native (f : (Fin d → ℂ) → ℂ)
    (a : Fin d → ℂ) (R : Fin d → ℝ) (α : Fin d → ℕ) :
    cauchyCoefficient f a R α =
      HolomorphicAnosov.PolydiscBoundaryCauchySeries.coefficient a R f α := by
  unfold cauchyCoefficient
  rw [distinguishedBoundaryIntegral_eq_native]
  unfold HolomorphicAnosov.PolydiscBoundaryCauchySeries.coefficient
  simp only [zpow_neg, zpow_natCast]
  have hk : cauchyKernel f α a = (fun ζ ↦ f ζ *
      ∏ j, ((ζ j - a j) ^ ((α j : ℤ) + 1))⁻¹) := by
    funext ζ
    unfold cauchyKernel
    congr 1
  rw [hk]

/-- The actual finite-product topology contains a positive closed polydisc
around each point of an open set; its half-radius preserves the original norm. -/
theorem exists_closedPolydisc {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {a : Fin d → ℂ} (ha : a ∈ U) :
    ∃ R : Fin d → ℝ, (∀ j, 0 < R j) ∧ closedPolydisc a R ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  refine ⟨fun _ ↦ ε / 2, (fun _ ↦ half_pos hε), ?_⟩
  intro z hz
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have hnorm : ‖z - a‖ ≤ ε / 2 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr hz
  exact hnorm.trans_lt (half_lt_self hε)

/-- The zero-jet step of Lebl's identity-theorem proof: once the actual
factorial coefficient identity has been established, the published native
Cauchy series is the zero series. This implication adds no premise to the
original theorem; its coefficient identity is exactly its preceding clause. -/
theorem zeroJet_germ_of_coefficients
    (hd : 1 ≤ d) {U : Set (Fin d → ℂ)} (hU : IsOpen U)
    {f : (Fin d → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U)
    (hcoef : ∀ a R, (∀ j, 0 < R j) → closedPolydisc a R ⊆ U →
      ∀ α, (multiIndexFactorial α : ℂ) * cauchyCoefficient f a R α =
        multiIndexDerivative f α a)
    {a : Fin d → ℂ} (ha : a ∈ U)
    (hzero : ∀ α, multiIndexDerivative f α a = 0) :
    ∃ V : Set (Fin d → ℂ), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ ∀ z ∈ V, f z = 0 := by
  obtain ⟨R, hR, hclosed⟩ := exists_closedPolydisc hU ha
  have hsep : ∀ z j, DifferentiableOn ℂ (fun t ↦ f (Function.update z j t))
      ((fun t ↦ Function.update z j t) ⁻¹' U) := by
    intro z j
    exact hf.comp ((contDiff_update (𝕜 := ℂ) ∞ z j).differentiable (by simp)).differentiableOn
      (fun _ ht ↦ ht)
  have hPD := HolomorphicAnosov.PolydiscCauchy.polydisc_cauchy_power_series hd U hU
    f hf.continuousOn hsep a R hR hclosed
  have hczero : ∀ α, HolomorphicAnosov.PolydiscBoundaryCauchySeries.coefficient a R f α = 0 := by
    intro α
    have hc := hcoef a R hR hclosed α
    rw [hzero α, cauchyCoefficient_eq_native] at hc
    have hfac : (multiIndexFactorial α : ℂ) ≠ 0 := by
      exact_mod_cast (Finset.prod_ne_zero_iff.mpr (fun j hj ↦ Nat.factorial_ne_zero (α j)))
    exact (mul_eq_zero.mp hc).resolve_left hfac
  have hopen : IsOpen (openPolydisc a R) := by
    have h : openPolydisc a R = ⋂ j, {z | ‖z j - a j‖ < R j} := by
      ext z
      simp only [openPolydisc, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [h]
    exact isOpen_iInter_of_finite (fun j ↦ isOpen_lt
      ((continuous_apply j).sub continuous_const).norm continuous_const)
  refine ⟨openPolydisc a R, hopen, (fun j ↦ by simpa using hR j), ?_, ?_⟩
  · intro z hz
    exact hclosed (fun j ↦ (hz j).le)
  · intro z hz
    have hsum := (hPD.2.1 z hz).1
    have hterms : HolomorphicAnosov.PolydiscBoundaryCauchySeries.seriesTerm a R f z =
        (fun _ ↦ (0 : ℂ)) := by
      funext α
      simp only [HolomorphicAnosov.PolydiscBoundaryCauchySeries.seriesTerm, hczero, zero_mul]
    rw [hterms] at hsum
    exact hsum.unique hasSum_zero

/-- The FULL complex parameter derivative of the actual rational kernel.
Each pole is guarded independently; finite-product differentiation supplies
an actual continuous linear operator on Fin d→ℂ, not a one-variable proxy. -/
theorem cauchyKernel_hasFDerivAt (f : (Fin d → ℂ) → ℂ) (α : Fin d → ℕ)
    (ζ z : Fin d → ℂ) (hpole : ∀ j, ζ j - z j ≠ 0) :
    HasFDerivAt (fun w ↦ cauchyKernel f α w ζ)
      ((f ζ) • ∑ j : Fin d,
        (∏ k ∈ Finset.univ.erase j, (ζ k - z k) ^ (-((α k : ℤ) + 1))) •
          (((-((α j : ℤ) + 1) : ℤ) : ℂ) *
            (ζ j - z j) ^ (-((α j : ℤ) + 1) - 1)) •
              (-(ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ))) z := by
  have hfactor (j : Fin d) :
      HasFDerivAt (fun w : Fin d → ℂ ↦ (ζ j - w j) ^ (-((α j : ℤ) + 1)))
        ((((-((α j : ℤ) + 1) : ℤ) : ℂ) *
          (ζ j - z j) ^ (-((α j : ℤ) + 1) - 1)) •
            (-(ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ))) z := by
    exact (hasDerivAt_zpow (-((α j : ℤ) + 1)) (ζ j - z j) (Or.inl (hpole j))).comp_hasFDerivAt z
      ((ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt.const_sub (ζ j))
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ ↦ hfactor j)
  have hmul := hprod.const_smul (f ζ)
  convert! hmul using 1

/-- At the actual distinguished boundary, every parameter in a smaller
closed polydisc has the original positive pole margin Rⱼ-rⱼ. -/
theorem kernel_pole_margin (a ζ z : Fin d → ℂ) (R r : Fin d → ℝ)
    (hboundary : ∀ j, ‖ζ j - a j‖ = R j)
    (hinner : z ∈ closedPolydisc a r) (hr : ∀ j, r j < R j) :
    ∀ j, 0 < R j - r j ∧ R j - r j ≤ ‖ζ j - z j‖ ∧ ζ j - z j ≠ 0 := by
  intro j
  have htri : ‖ζ j - a j‖ ≤ ‖ζ j - z j‖ + ‖z j - a j‖ := by
    convert norm_add_le (ζ j - z j) (z j - a j) using 1
    abel_nf
  have hmargin : R j - r j ≤ ‖ζ j - z j‖ := by
    rw [hboundary j] at htri
    linarith [hinner j]
  refine ⟨sub_pos.mpr (hr j), hmargin, ?_⟩
  exact norm_pos_iff.mp ((sub_pos.mpr (hr j)).trans_le hmargin)

/-- Differentiating the FULL kernel in one coordinate gives its actual
incremented multi-index, with the positive exponent multiplier. This is the
literal rational-kernel step in Lebl Proposition 1.2.2, pp.19–20. -/
theorem cauchyKernel_coordinateDerivative (f : (Fin d → ℂ) → ℂ) (α : Fin d → ℕ)
    (ζ z : Fin d → ℂ) (hpole : ∀ j, ζ j - z j ≠ 0) (j : Fin d) :
    coordinateDerivative j (fun w ↦ cauchyKernel f α w ζ) z =
      (α j + 1 : ℂ) * cauchyKernel f (α + Pi.single j 1) z ζ := by
  rw [coordinateDerivative, (cauchyKernel_hasFDerivAt f α ζ z hpole).fderiv]
  simp only [smul_apply, sum_apply,
    smul_eq_mul, neg_apply, ContinuousLinearMap.proj_apply,
    coordinateVector]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same]
    have hprod : (∏ k, ((ζ k - z k) ^ ((α + (Pi.single j 1 : Fin d → ℕ)) k + 1))⁻¹) =
        (∏ k ∈ Finset.univ.erase j, ((ζ k - z k) ^ (α k + 1))⁻¹) *
          ((ζ j - z j) ^ (α j + 2))⁻¹ := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      congr 1
      · apply Finset.prod_congr rfl
        intro k hk
        have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
        simp [hkj]
      · simp
    unfold cauchyKernel
    rw [hprod]
    have hzpow (k : Fin d) : (ζ k - z k) ^ (-((α k : ℤ) + 1)) =
        ((ζ k - z k) ^ (α k + 1))⁻¹ := by
      rw [zpow_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add, zpow_natCast]
    have hzpow2 : (ζ j - z j) ^ (-((α j : ℤ) + 1) - 1) =
        ((ζ j - z j) ^ (α j + 2))⁻¹ := by
      have hexp : -((α j : ℤ) + 1) - 1 = -((α j + 2 : ℕ) : ℤ) := by omega
      rw [hexp, zpow_neg, zpow_natCast]
    simp only [hzpow, hzpow2, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
    ring
  · intro k hk hkj
    simp [hkj]
  · simp

/-- Compact Cauchy-kernel differentiation with ALL dominated-integral guards
proved from joint continuity of the actual scalar integrand and its actual
full complex derivative. The bound is obtained on a genuine compact parameter
buffer, not added as a premise. This is the one-circle implementation of
Lebl's compact-kernel differentiation argument, pp.19–20. -/
theorem compact_interval_parameter_derivative
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    (G : (Fin d → ℂ) → ℝ → T)
    (D : (Fin d → ℂ) → ℝ → (Fin d → ℂ) →L[ℂ] T)
    {U : Set (Fin d → ℂ)} (hU : IsOpen U) {z : Fin d → ℂ} (hz : z ∈ U)
    (a b : ℝ)
    (hG : ContinuousOn (fun p : (Fin d → ℂ) × ℝ ↦ G p.1 p.2) (U ×ˢ Set.uIcc a b))
    (hD : ContinuousOn (fun p : (Fin d → ℂ) × ℝ ↦ D p.1 p.2) (U ×ˢ Set.uIcc a b))
    (hderiv : ∀ w ∈ U, ∀ t ∈ Set.uIcc a b, HasFDerivAt (fun y ↦ G y t) (D w t) w) :
    HasFDerivAt (fun w ↦ ∫ t in a..b, G w t) (∫ t in a..b, D z t) z := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hclosed : Metric.closedBall z r ⊆ U := by
    intro w hw
    apply hball
    exact (Metric.mem_closedBall.mp hw).trans_lt (half_lt_self hε)
  have hcompact := (isCompact_closedBall z r).prod (isCompact_uIcc : IsCompact (Set.uIcc a b))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (hD.mono (Set.prod_mono hclosed (fun _ h ↦ h)))
  have hsliceG (w : Fin d → ℂ) (hw : w ∈ U) : ContinuousOn (G w) (Set.uIcc a b) :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht ↦ ⟨hw, ht⟩)
  have hsliceD : ContinuousOn (D z) (Set.uIcc a b) :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht ↦ ⟨hz, ht⟩)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball z r) (bound := fun _ ↦ C) (Metric.ball_mem_nhds z hr)
  · filter_upwards [hU.mem_nhds hz] with w hw
    exact ((hsliceG w hw).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · exact (hsliceG z hz).intervalIntegrable
  · exact (hsliceD.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact Filter.Eventually.of_forall (fun t ht w hw ↦
      hC (w, t) ⟨Metric.ball_subset_closedBall hw, Set.uIoc_subset_uIcc ht⟩)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t ht w hw ↦
      hderiv w (hclosed (Metric.ball_subset_closedBall hw)) t (Set.uIoc_subset_uIcc ht))

/-- The zero multi-index is the literal empty derivative fold. -/
theorem multiIndexDerivative_zero (f : (Fin d → ℂ) → ℂ) :
    multiIndexDerivative f 0 = f := by
  have hnil : multiIndexList (0 : Fin d → ℕ) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    have hc := multiIndexList_count (0 : Fin d → ℕ) j
    have hpos := List.count_pos_iff.mpr hj
    simp only [hc, Pi.zero_apply, lt_self_iff_false] at hpos
  rw [multiIndexDerivative, hnil]
  rfl

/-- The order-zero case is the actual published finite-polydisc Cauchy
formula, translated through the proved integral-convention correspondence.
Every coordinate slice is restricted to its exact original receiving domain. -/
theorem cauchy_formula_zero (hd : 1 ≤ d)
    {U : Set (Fin d → ℂ)} (hU : IsOpen U) {f : (Fin d → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f U) (a : Fin d → ℂ) (R : Fin d → ℝ)
    (hR : ∀ j, 0 < R j) (hclosed : closedPolydisc a R ⊆ U)
    {z : Fin d → ℂ} (hz : z ∈ openPolydisc a R) :
    multiIndexDerivative f 0 z = (multiIndexFactorial (0 : Fin d → ℕ) : ℂ) *
      ((2 * (Real.pi : ℂ) * Complex.I) ^ d)⁻¹ *
        distinguishedBoundaryIntegral a R (cauchyKernel f 0 z) := by
  have hsep : ∀ w j, DifferentiableOn ℂ (fun t ↦ f (Function.update w j t))
      ((fun t ↦ Function.update w j t) ⁻¹' U) := by
    intro w j
    exact hf.comp ((contDiff_update (𝕜 := ℂ) ∞ w j).differentiable (by simp)).differentiableOn
      (fun _ ht ↦ ht)
  have h := (HolomorphicAnosov.PolydiscCauchy.polydisc_cauchy_power_series hd U hU
    f hf.continuousOn hsep a R hR hclosed).1 z hz
  rw [multiIndexDerivative_zero, distinguishedBoundaryIntegral_eq_native]
  have hk : cauchyKernel f 0 z = (fun ζ ↦ f ζ *
      HolomorphicAnosov.PolydiscBoundaryCauchySeries.kernel ζ z) := by
    funext ζ
    simp [cauchyKernel, HolomorphicAnosov.PolydiscBoundaryCauchySeries.kernel, zpow_neg]
  rw [hk]
  simpa only [HolomorphicAnosov.PolydiscBoundaryCauchySeries.cauchyTransform,
    multiIndexFactorial, Pi.zero_apply, Nat.factorial_zero, Finset.prod_const_one,
    Nat.cast_one, one_mul, zpow_neg, zpow_natCast] using h

/-- Differentiating an ACTUAL circle integral in the full finite-dimensional
complex parameter uses its literal real-angle parametrization and weight.
Joint continuity on the original circle supplies every integration guard. -/
theorem compact_circle_parameter_derivative
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    (G : (Fin d → ℂ) → ℂ → T)
    (D : (Fin d → ℂ) → ℂ → (Fin d → ℂ) →L[ℂ] T)
    {U : Set (Fin d → ℂ)} (hU : IsOpen U) {z : Fin d → ℂ} (hz : z ∈ U)
    (a : ℂ) (R : ℝ)
    (hG : ContinuousOn (fun p : (Fin d → ℂ) × ℂ ↦ G p.1 p.2)
      (U ×ˢ Metric.sphere a |R|))
    (hD : ContinuousOn (fun p : (Fin d → ℂ) × ℂ ↦ D p.1 p.2)
      (U ×ˢ Metric.sphere a |R|))
    (hderiv : ∀ w ∈ U, ∀ ζ ∈ Metric.sphere a |R|,
      HasFDerivAt (fun y ↦ G y ζ) (D w ζ) w) :
    HasFDerivAt (fun w ↦ circleIntegral (G w) a R)
      (circleIntegral (D z) a R) z := by
  let γ := circleMap a R
  let W : ℝ → ℂ := fun t ↦ circleMap 0 R t * Complex.I
  have hp : Continuous (fun p : (Fin d → ℂ) × ℝ ↦ (p.1, γ p.2)) :=
    continuous_fst.prodMk ((continuous_circleMap a R).comp continuous_snd)
  have hm : Set.MapsTo (fun p : (Fin d → ℂ) × ℝ ↦ (p.1, γ p.2))
      (U ×ˢ Set.uIcc 0 (2 * Real.pi)) (U ×ˢ Metric.sphere a |R|) := by
    intro p hp
    exact ⟨hp.1, circleMap_mem_sphere' a R p.2⟩
  have hw : Continuous (fun p : (Fin d → ℂ) × ℝ ↦ W p.2) :=
    (((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const)
  have hGG : ContinuousOn (fun p : (Fin d → ℂ) × ℝ ↦ W p.2 • G p.1 (γ p.2))
      (U ×ˢ Set.uIcc 0 (2 * Real.pi)) :=
    hw.continuousOn.smul (hG.comp hp.continuousOn hm)
  have hDD : ContinuousOn (fun p : (Fin d → ℂ) × ℝ ↦ W p.2 • D p.1 (γ p.2))
      (U ×ˢ Set.uIcc 0 (2 * Real.pi)) :=
    hw.continuousOn.smul (hD.comp hp.continuousOn hm)
  have h := compact_interval_parameter_derivative
    (fun w t ↦ W t • G w (γ t)) (fun w t ↦ W t • D w (γ t)) hU hz
    0 (2 * Real.pi) hGG hDD
    (fun w hw t ht ↦ (hderiv w hw (γ t) (circleMap_mem_sphere' a R t)).const_smul (W t))
  simpa only [circleIntegral, deriv_circleMap, γ, W] using h

/-- Integrating one circle preserves actual joint continuity in every
remaining parameter, including parameters restricted to compact boundary
factors. The SAME globally defined circle parametrization always lands on
its actual sphere; the integrand is used only there. -/
theorem continuous_circleIntegral_parameter
    {X G : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (F : X → ℂ → G) (a : ℂ) (R : ℝ)
    (hF : ContinuousOn (fun p : X × ℂ ↦ F p.1 p.2)
      (Set.univ ×ˢ Metric.sphere a |R|)) :
    Continuous (fun x ↦ circleIntegral (F x) a R) := by
  have hp : Continuous (fun p : X × ℝ ↦ (p.1, circleMap a R p.2)) :=
    continuous_fst.prodMk ((continuous_circleMap a R).comp continuous_snd)
  have hm : Set.MapsTo (fun p : X × ℝ ↦ (p.1, circleMap a R p.2)) Set.univ
      (Set.univ ×ˢ Metric.sphere a |R|) :=
    fun p _ ↦ ⟨Set.mem_univ _, circleMap_mem_sphere' a R p.2⟩
  have hc : Continuous (fun p : X × ℝ ↦ F p.1 (circleMap a R p.2)) :=
    continuousOn_univ.mp (hF.comp hp.continuousOn hm)
  have hw : Continuous (fun p : X × ℝ ↦ circleMap 0 R p.2 * Complex.I) :=
    ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
  have hi := continuous_parametric_integral_of_continuous (μ := MeasureTheory.volume)
    (f := fun x t ↦ (circleMap 0 R t * Complex.I) • F x (circleMap a R t))
    (hw.smul hc) (isCompact_Icc : IsCompact (Set.Icc 0 (2 * Real.pi)))
  simpa only [circleIntegral_def_Icc, deriv_circleMap] using hi

/-- The same native ordered integral for a normed complex target, needed for
its actual continuous-linear-map derivative. This short recursion has no
admitted data; scalar specialization agrees with the published operator. -/
def nativeIntegral {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T] :
    (n : ℕ) → (Fin n → ℂ) → (Fin n → ℝ) → ((Fin n → ℂ) → T) → T
  | 0, _, _, F => F (fun j ↦ Fin.elim0 j)
  | n + 1, a, R, F => circleIntegral
      (fun ζ ↦ nativeIntegral n (Fin.tail a) (Fin.tail R) (fun w ↦ F (Fin.cons ζ w))) (a 0) (R 0)

/-- Scalar specialization uses the actual published operator, not an
alternative integral convention. -/
theorem nativeIntegral_scalar (n : ℕ) (a : Fin n → ℂ) (R : Fin n → ℝ)
    (F : (Fin n → ℂ) → ℂ) : nativeIntegral n a R F =
      HolomorphicAnosov.PolydiscBoundaryCauchySeries.iteratedCircleIntegral n a R F := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [nativeIntegral, HolomorphicAnosov.PolydiscBoundaryCauchySeries.iteratedCircleIntegral]
      congr 1
      funext ζ
      exact ih _ _ _


/-- Repeated actual boundary integration preserves joint continuity in the
remaining parameters. This finite induction retains the original circle order;
it applies also to parameters which already contain boundary-circle factors. -/
theorem continuous_nativeBoundaryIntegral_parameter
    (n : ℕ) {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] (F : X → (Fin n → ℂ) → T)
    (a : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 ≤ R j)
    (hF : ContinuousOn (fun p : X × (Fin n → ℂ) ↦ F p.1 p.2)
      (Set.univ ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R)) :
    Continuous (fun x ↦ nativeIntegral
      n a R (F x)) := by
  induction n generalizing X with
  | zero =>
      exact hF.comp_continuous (continuous_id.prodMk continuous_const)
        (fun x ↦ ⟨Set.mem_univ x, fun j ↦ Fin.elim0 j⟩)
  | succ n ih =>
      let B := Metric.sphere (a 0) |R 0|
      have : LocallyCompactSpace B := Metric.isClosed_sphere.locallyCompactSpace
      have htail : ContinuousOn
          (fun p : (X × B) × (Fin n → ℂ) ↦ F p.1.1 (Fin.cons p.1.2.val p.2))
          (Set.univ ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary
            (Fin.tail a) (Fin.tail R)) := by
        apply hF.comp (f := fun p : (X × B) × (Fin n → ℂ) ↦
          (p.1.1, Fin.cons p.1.2.val p.2))
        · fun_prop
        · intro p hp
          refine ⟨Set.mem_univ _, ?_⟩
          intro j
          refine Fin.cases ?_ (fun k ↦ ?_) j
          · simpa only [B, Fin.cons_zero, Metric.mem_sphere, dist_eq_norm, abs_of_nonneg (hR 0)]
              using p.1.2.property
          · exact hp.2 k
      have hinner := ih
        (fun p : X × B ↦ fun w ↦ F p.1 (Fin.cons p.2.val w))
        (Fin.tail a) (Fin.tail R) (fun j ↦ hR j.succ) htail
      have houter : ContinuousOn
          (fun p : X × ℂ ↦ nativeIntegral
            n (Fin.tail a) (Fin.tail R) (fun w ↦ F p.1 (Fin.cons p.2 w)))
          (Set.univ ×ˢ Metric.sphere (a 0) |R 0|) := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact hinner.comp (show Continuous
          (fun p : (Set.univ ×ˢ Metric.sphere (a 0) |R 0| : Set (X × ℂ)) ↦
            (p.val.1, (⟨p.val.2, p.property.2⟩ : B))) by fun_prop)
      exact continuous_circleIntegral_parameter _ (a 0) (R 0) houter


/-- Full complex differentiation passes through the actual ordered finite
boundary integral. The induction retains every source and receiving-circle
guard and integrates the actual continuous-linear-map derivative. -/
theorem nativeIntegral_hasFDerivAt (n : ℕ)
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    (G : (Fin d → ℂ) → (Fin n → ℂ) → T)
    (D : (Fin d → ℂ) → (Fin n → ℂ) → (Fin d → ℂ) →L[ℂ] T)
    {U : Set (Fin d → ℂ)} (hU : IsOpen U) {z : Fin d → ℂ} (hz : z ∈ U)
    (a : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 ≤ R j)
    (hG : ContinuousOn (fun p : (Fin d → ℂ) × (Fin n → ℂ) ↦ G p.1 p.2)
      (U ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R))
    (hD : ContinuousOn (fun p : (Fin d → ℂ) × (Fin n → ℂ) ↦ D p.1 p.2)
      (U ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R))
    (hderiv : ∀ w ∈ U, ∀ ζ ∈ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R,
      HasFDerivAt (fun y ↦ G y ζ) (D w ζ) w) :
    HasFDerivAt (fun w ↦ nativeIntegral n a R (G w))
      (nativeIntegral n a R (D z)) z := by
  induction n generalizing z with
  | zero => exact hderiv z hz _ (fun j ↦ Fin.elim0 j)
  | succ n ih =>
      let B := Metric.sphere (a 0) |R 0|
      have : LocallyCompactSpace B := Metric.isClosed_sphere.locallyCompactSpace
      have : LocallyCompactSpace U := hU.locallyCompactSpace
      have hcons : ∀ (b : B) w,
          w ∈ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary
            (Fin.tail a) (Fin.tail R) →
          Fin.cons b.val w ∈ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R := by
        intro b w hw j
        refine Fin.cases ?_ (fun k ↦ hw k) j
        simpa only [B, Fin.cons_zero, Metric.mem_sphere, dist_eq_norm, abs_of_nonneg (hR 0)]
          using b.property
      have hcont (F : (Fin d → ℂ) → (Fin (n+1) → ℂ) → T)
          (hF : ContinuousOn (fun p : (Fin d → ℂ) × (Fin (n+1) → ℂ) ↦ F p.1 p.2)
            (U ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R)) :
          ContinuousOn (fun p : (Fin d → ℂ) × ℂ ↦ nativeIntegral n (Fin.tail a) (Fin.tail R)
            (fun w ↦ F p.1 (Fin.cons p.2 w))) (U ×ˢ B) := by
        have ht : ContinuousOn
            (fun p : (U × B) × (Fin n → ℂ) ↦ F p.1.1.val (Fin.cons p.1.2.val p.2))
            (Set.univ ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary
              (Fin.tail a) (Fin.tail R)) := by
          apply hF.comp (f := fun p : (U × B) × (Fin n → ℂ) ↦
            (p.1.1.val, Fin.cons p.1.2.val p.2))
          · fun_prop
          · intro p hp
            exact ⟨p.1.1.property, hcons p.1.2 p.2 hp.2⟩
        have hc := continuous_nativeBoundaryIntegral_parameter n
          (fun p : U × B ↦ fun w ↦ F p.1.val (Fin.cons p.2.val w))
          (Fin.tail a) (Fin.tail R) (fun j ↦ hR j.succ) ht
        rw [continuousOn_iff_continuous_domRestrict]
        exact hc.comp (show Continuous
          (fun p : (U ×ˢ B : Set ((Fin d → ℂ) × ℂ)) ↦
            ((⟨p.val.1, p.property.1⟩ : U), (⟨p.val.2, p.property.2⟩ : B))) by fun_prop)
      have hcontD (F : (Fin d → ℂ) → (Fin (n+1) → ℂ) → (Fin d → ℂ) →L[ℂ] T)
          (hF : ContinuousOn (fun p : (Fin d → ℂ) × (Fin (n+1) → ℂ) ↦ F p.1 p.2)
            (U ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R)) :
          ContinuousOn (fun p : (Fin d → ℂ) × ℂ ↦ nativeIntegral n (Fin.tail a) (Fin.tail R)
            (fun w ↦ F p.1 (Fin.cons p.2 w))) (U ×ˢ B) := by
        have ht : ContinuousOn
            (fun p : (U × B) × (Fin n → ℂ) ↦ F p.1.1.val (Fin.cons p.1.2.val p.2))
            (Set.univ ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary
              (Fin.tail a) (Fin.tail R)) := by
          apply hF.comp (f := fun p : (U × B) × (Fin n → ℂ) ↦
            (p.1.1.val, Fin.cons p.1.2.val p.2))
          · fun_prop
          · intro p hp
            exact ⟨p.1.1.property, hcons p.1.2 p.2 hp.2⟩
        have hc := continuous_nativeBoundaryIntegral_parameter n
          (fun p : U × B ↦ fun w ↦ F p.1.val (Fin.cons p.2.val w))
          (Fin.tail a) (Fin.tail R) (fun j ↦ hR j.succ) ht
        rw [continuousOn_iff_continuous_domRestrict]
        exact hc.comp (show Continuous
          (fun p : (U ×ˢ B : Set ((Fin d → ℂ) × ℂ)) ↦
            ((⟨p.val.1, p.property.1⟩ : U), (⟨p.val.2, p.property.2⟩ : B))) by fun_prop)
      apply compact_circle_parameter_derivative _ _ hU hz (a 0) (R 0) (hcont G hG)
      · exact hcontD D hD
      · intro w hw b hb
        apply ih _ _ hw (Fin.tail a) (Fin.tail R) (fun j ↦ hR j.succ)
        · apply hG.comp (f := fun p : (Fin d → ℂ) × (Fin n → ℂ) ↦
            (p.1, Fin.cons b p.2))
          · fun_prop
          · intro p hp
            exact ⟨hp.1, hcons ⟨b, hb⟩ p.2 hp.2⟩
        · apply hD.comp (f := fun p : (Fin d → ℂ) × (Fin n → ℂ) ↦
            (p.1, Fin.cons b p.2))
          · fun_prop
          · intro p hp
            exact ⟨hp.1, hcons ⟨b, hb⟩ p.2 hp.2⟩
        · intro y hy ζ hζ
          exact hderiv y hy _ (hcons ⟨b, hb⟩ ζ hζ)

/-- A continuous linear map commutes with the actual finite ordered integral
when the actual boundary integrand is continuous. -/
theorem nativeIntegral_comp_clm (n : ℕ)
    {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T] [CompleteSpace T]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (L : T →L[ℂ] V) (F : (Fin n → ℂ) → T)
    (a : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 ≤ R j)
    (hF : ContinuousOn F
      (HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R)) :
    nativeIntegral n a R (fun ζ ↦ L (F ζ)) = L (nativeIntegral n a R F) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let B := Metric.sphere (a 0) |R 0|
      have : LocallyCompactSpace B := Metric.isClosed_sphere.locallyCompactSpace
      have hcons : ∀ (b : B) w,
          w ∈ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary
            (Fin.tail a) (Fin.tail R) →
          Fin.cons b.val w ∈ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R := by
        intro b w hw j
        refine Fin.cases ?_ (fun k ↦ hw k) j
        simpa only [B, Fin.cons_zero, Metric.mem_sphere, dist_eq_norm, abs_of_nonneg (hR 0)]
          using b.property
      have ht : ContinuousOn
          (fun p : B × (Fin n → ℂ) ↦ F (Fin.cons p.1.val p.2))
          (Set.univ ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary
            (Fin.tail a) (Fin.tail R)) := by
        apply hF.comp (f := fun p : B × (Fin n → ℂ) ↦ Fin.cons p.1.val p.2)
        · fun_prop
        · intro p hp
          exact hcons p.1 p.2 hp.2
      have hc := continuous_nativeBoundaryIntegral_parameter n
        (fun b : B ↦ fun w ↦ F (Fin.cons b.val w))
        (Fin.tail a) (Fin.tail R) (fun j ↦ hR j.succ) ht
      have hinner : ContinuousOn
          (fun b ↦ nativeIntegral n (Fin.tail a) (Fin.tail R) (fun w ↦ F (Fin.cons b w))) B :=
        continuousOn_iff_continuous_domRestrict.mpr hc
      simp only [nativeIntegral]
      calc
        _ = circleIntegral (fun b ↦ L (nativeIntegral n (Fin.tail a) (Fin.tail R)
              (fun w ↦ F (Fin.cons b w)))) (a 0) (R 0) := by
          apply circleIntegral.integral_congr (hR 0)
          intro b hb
          apply ih _ (Fin.tail a) (Fin.tail R) (fun j ↦ hR j.succ)
          apply hF.comp (f := fun w : Fin n → ℂ ↦ Fin.cons b w)
          · fun_prop
          · intro w hw
            exact hcons ⟨b, by simpa only [B, abs_of_nonneg (hR 0)] using hb⟩ w hw
        _ = _ := by
          simp only [circleIntegral]
          have hi := hinner.circleIntegrable'
          have h := L.intervalIntegral_comp_comm hi.out
          simpa only [map_smul] using h

/-- The explicit finite-product differential used in the proved kernel
chain rule, with its actual projection operators. -/
def kernelDifferential (f : (Fin d → ℂ) → ℂ) (α : Fin d → ℕ)
    (z ζ : Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] ℂ :=
  (f ζ) • ∑ j : Fin d,
    (∏ k ∈ Finset.univ.erase j, (ζ k - z k) ^ (-((α k : ℤ) + 1))) •
      (((-((α j : ℤ) + 1) : ℤ) : ℂ) *
        (ζ j - z j) ^ (-((α j : ℤ) + 1) - 1)) •
          (-(ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ))

/-- The original open polydisc is open in its native finite-product topology. -/
theorem isOpen_openPolydisc (a : Fin d → ℂ) (R : Fin d → ℝ) :
    IsOpen (openPolydisc a R) := by
  have h : openPolydisc a R = ⋂ j, {z | ‖z j - a j‖ < R j} := by
    ext z
    simp only [openPolydisc, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite (fun j ↦ isOpen_lt
    ((continuous_apply j).sub continuous_const).norm continuous_const)


/-- No actual boundary coordinate is a pole for an interior parameter. -/
theorem boundary_pole_ne (a : Fin d → ℂ) (R : Fin d → ℝ)
    {z ζ : Fin d → ℂ} (hz : z ∈ openPolydisc a R)
    (hζ : ζ ∈ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R)
    (j : Fin d) : ζ j - z j ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  have := hz j
  rw [← he, hζ j] at this
  exact lt_irrefl _ this

/-- The actual kernel and its full differential are jointly continuous on
interior-parameter times distinguished-boundary, independently of any
regularity of f away from that boundary. -/
theorem kernel_joint_continuity (f : (Fin d → ℂ) → ℂ) (α : Fin d → ℕ)
    (a : Fin d → ℂ) (R : Fin d → ℝ)
    (hf : ContinuousOn f
      (HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R)) :
    ContinuousOn (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ cauchyKernel f α p.1 p.2)
      (openPolydisc a R ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R) ∧
    ContinuousOn (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ kernelDifferential f α p.1 p.2)
      (openPolydisc a R ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R) := by
  let S := openPolydisc a R ×ˢ HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R
  have hfc : ContinuousOn (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ f p.2) S :=
    hf.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hpow (j : Fin d) (m : ℤ) : ContinuousOn
      (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ (p.2 j - p.1 j) ^ m) S := by
    apply ContinuousOn.zpow₀
    · fun_prop
    · intro p hp
      exact Or.inl (boundary_pole_ne a R hp.1 hp.2 j)
  constructor
  · change ContinuousOn (fun p ↦ f p.2 * ∏ j, ((p.2 j - p.1 j) ^ (α j + 1))⁻¹) S
    apply hfc.mul
    apply continuousOn_finsetProd
    intro j hj
    convert hpow j (-((α j + 1 : ℕ) : ℤ)) using 1
    simp only [zpow_neg, zpow_natCast]
  · unfold kernelDifferential
    apply hfc.smul
    apply continuousOn_finsetSum
    intro j hj
    have hp : ContinuousOn (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦
        ∏ k ∈ Finset.univ.erase j, (p.2 k - p.1 k) ^ (-((α k : ℤ) + 1))) S :=
      continuousOn_finsetProd _ (fun k hk ↦ hpow k (-((α k : ℤ) + 1)))
    have hb : ContinuousOn (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦
        (((-((α j : ℤ) + 1) : ℤ) : ℂ) * (p.2 j - p.1 j) ^ (-((α j : ℤ) + 1) - 1))) S :=
      continuousOn_const.mul (hpow j (-((α j : ℤ) + 1) - 1))
    exact hp.smul (hb.smul (continuousOn_const : ContinuousOn
      (fun _ : (Fin d → ℂ) × (Fin d → ℂ) ↦
        -(ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ)) S))

/-- The genuine boundary values suffice to identify the ordered integral. -/
theorem nativeIntegral_congr (n : ℕ)
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    (a : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 ≤ R j)
    {F G : (Fin n → ℂ) → T}
    (h : Set.EqOn F G (HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R)) :
    nativeIntegral n a R F = nativeIntegral n a R G := by
  induction n with
  | zero => exact h (fun j ↦ Fin.elim0 j)
  | succ n ih =>
      apply circleIntegral.integral_congr (hR 0)
      intro b hb
      apply ih (Fin.tail a) (Fin.tail R) (fun j ↦ hR j.succ)
      intro w hw
      apply h
      intro j
      refine Fin.cases ?_ (fun k ↦ hw k) j
      simpa only [Fin.cons_zero, Metric.mem_sphere, dist_eq_norm] using hb

/-- Scalar linearity holds at each literal circle, hence at every finite order. -/
theorem nativeIntegral_smul (n : ℕ)
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    (c : ℂ) (a : Fin n → ℂ) (R : Fin n → ℝ) (F : (Fin n → ℂ) → T) :
    nativeIntegral n a R (fun ζ ↦ c • F ζ) = c • nativeIntegral n a R F := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [nativeIntegral, ih, circleIntegral.integral_smul]

/-- The actual boundary integral gains the coordinate exponent and its
positive multiplier when differentiated. Full-parameter differentiation,
then actual continuous-linear evaluation, supplies the coordinate derivative. -/
theorem boundaryIntegral_coordinateDerivative (f : (Fin d → ℂ) → ℂ)
    (α : Fin d → ℕ) (a : Fin d → ℂ) (R : Fin d → ℝ)
    (hR : ∀ j, 0 < R j)
    (hf : ContinuousOn f
      (HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R))
    {z : Fin d → ℂ} (hz : z ∈ openPolydisc a R) (j : Fin d) :
    coordinateDerivative j (fun w ↦ distinguishedBoundaryIntegral a R (cauchyKernel f α w)) z =
      (α j + 1 : ℂ) * distinguishedBoundaryIntegral a R
        (cauchyKernel f (α + Pi.single j 1) z) := by
  obtain ⟨hG, hD⟩ := kernel_joint_continuity f α a R hf
  have hderiv := nativeIntegral_hasFDerivAt d (cauchyKernel f α) (kernelDifferential f α)
    (isOpen_openPolydisc a R) hz a R (fun j ↦ (hR j).le) hG hD
    (fun w hw ζ hζ ↦ cauchyKernel_hasFDerivAt f α ζ w
      (fun j ↦ boundary_pole_ne a R hw hζ j))
  have hDζ : ContinuousOn (kernelDifferential f α z)
      (HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R) :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn (fun ζ hζ ↦ ⟨hz, hζ⟩)
  have heval := nativeIntegral_comp_clm d
    (ContinuousLinearMap.apply ℂ ℂ (coordinateVector j)) (kernelDifferential f α z)
    a R (fun j ↦ (hR j).le) hDζ
  have hpoint : Set.EqOn
      (fun ζ ↦ kernelDifferential f α z ζ (coordinateVector j))
      (fun ζ ↦ (α j + 1 : ℂ) • cauchyKernel f (α + Pi.single j 1) z ζ)
      (HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R) := by
    intro ζ hζ
    have hk := cauchyKernel_hasFDerivAt f α ζ z
      (fun j ↦ boundary_pole_ne a R hz hζ j)
    have hc := cauchyKernel_coordinateDerivative f α ζ z
      (fun j ↦ boundary_pole_ne a R hz hζ j) j
    simpa only [coordinateDerivative, hk.fderiv, kernelDifferential, smul_eq_mul] using hc
  have hin := nativeIntegral_congr d a R (fun j ↦ (hR j).le) hpoint
  have hs := nativeIntegral_smul d (α j + 1 : ℂ) a R
    (cauchyKernel f (α + Pi.single j 1) z)
  simp only [coordinateDerivative]
  have hfun : (fun w ↦ distinguishedBoundaryIntegral a R (cauchyKernel f α w)) =
      (fun w ↦ nativeIntegral d a R (cauchyKernel f α w)) := by
    funext w
    rw [distinguishedBoundaryIntegral_eq_native, nativeIntegral_scalar]
  simp only [ContinuousLinearMap.apply_apply] at heval
  rw [hfun, hderiv.fderiv, ← heval, hin, hs, nativeIntegral_scalar,
    ← distinguishedBoundaryIntegral_eq_native]
  rfl

/-- Finite natural multi-indices are built from zero by actual unit increments. -/
private theorem multiIndex_induction (P : (Fin d → ℕ) → Prop) (h0 : P 0)
    (hs : ∀ α j, P α → P (α + Pi.single j 1)) : ∀ α, P α := by
  have hall : ∀ k α, (∑ j, α j) = k → P α := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro α hα
      by_cases hz : ∀ j, α j = 0
      · have he : α = 0 := funext hz
        simpa only [he] using h0
      · obtain ⟨j, hj⟩ := not_forall.mp hz
        let β := Function.update α j (α j - 1)
        have he : α = β + Pi.single j 1 := by
          funext i
          by_cases hi : i = j
          · subst i
            simp only [β, Function.update_self, Pi.add_apply, Pi.single_eq_same]
            omega
          · simp [β, hi]
        have hlt : (∑ i, β i) < k := by
          rw [← hα]
          apply Finset.sum_lt_sum
          · intro i hi
            by_cases hij : i = j
            · subst i; simp [β]
            · simp [β, hij]
          · exact ⟨j, Finset.mem_univ j, by simp only [β, Function.update_self]; omega⟩
        rw [he]
        exact hs β j (ih _ hlt β rfl)
  intro α
  exact hall _ α rfl

/-- The exact finite factorial acquires the positive coordinate multiplier. -/
theorem multiIndexFactorial_increment (α : Fin d → ℕ) (j : Fin d) :
    multiIndexFactorial (α + Pi.single j 1) = (α j + 1) * multiIndexFactorial α := by
  unfold multiIndexFactorial
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j),
    ← Finset.prod_erase_mul Finset.univ (fun i ↦ (α i).factorial) (Finset.mem_univ j)]
  have he : (∏ i ∈ Finset.univ.erase j, ((α + (Pi.single j 1 : Fin d → ℕ)) i).factorial) =
      ∏ i ∈ Finset.univ.erase j, (α i).factorial := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [(Finset.mem_erase.mp hi).1]
  rw [he]
  simp only [Pi.add_apply, Pi.single_eq_same, Nat.factorial_succ]
  ring

/-- The SAME kernel integral is complex differentiable at every original
interior point, by its proved full derivative and actual boundary continuity. -/
theorem boundaryIntegral_differentiableAt (f : (Fin d → ℂ) → ℂ)
    (α : Fin d → ℕ) (a : Fin d → ℂ) (R : Fin d → ℝ)
    (hR : ∀ j, 0 < R j)
    (hf : ContinuousOn f
      (HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R))
    {z : Fin d → ℂ} (hz : z ∈ openPolydisc a R) :
    DifferentiableAt ℂ (fun w ↦ distinguishedBoundaryIntegral a R (cauchyKernel f α w)) z := by
  obtain ⟨hG, hD⟩ := kernel_joint_continuity f α a R hf
  have h := nativeIntegral_hasFDerivAt d (cauchyKernel f α) (kernelDifferential f α)
    (isOpen_openPolydisc a R) hz a R (fun j ↦ (hR j).le) hG hD
    (fun w hw ζ hζ ↦ cauchyKernel_hasFDerivAt f α ζ w
      (fun j ↦ boundary_pole_ne a R hw hζ j))
  have he : (fun w ↦ distinguishedBoundaryIntegral a R (cauchyKernel f α w)) =
      (fun w ↦ nativeIntegral d a R (cauchyKernel f α w)) := by
    funext w
    rw [distinguishedBoundaryIntegral_eq_native, nativeIntegral_scalar]
  rw [he]
  exact h.differentiableAt

/-- Constant scalar multiplication preserves the actual coordinate derivative. -/
theorem coordinateDerivative_const_smul (j : Fin d) (c : ℂ)
    {g : (Fin d → ℂ) → ℂ} {z : Fin d → ℂ} (hg : DifferentiableAt ℂ g z) :
    coordinateDerivative j (fun w ↦ c • g w) z = c • coordinateDerivative j g z := by
  have h : HasFDerivAt (fun w ↦ c • g w) (c • fderiv ℂ g z) z := by
    convert! hg.hasFDerivAt.const_smul c using 1
  rw [coordinateDerivative, h.fderiv]
  rfl

end LeblPolydisc

open LeblPolydisc

/-- Holomorphic coordinate derivatives are smooth, depend only on their count
multi-index, satisfy the distinguished-boundary Cauchy formula with factorials,
and determine the zero germ.

Source: Lebl, *Tasty Bits of Several Complex Variables*, version 3.4,
Proposition 1.1.3, pp.12–13; Proposition 1.2.2, pp.19–20; the all-zero-jet
argument in the proof of Theorem 1.2.6, p.21. DAG node:
`analysis.lebl_polydisc_holomorphic_coordinate_derivatives_g1`.

Natural-language proof:
1. Define P_j by the complex Fréchet derivative evaluated on the coordinate
   unit vector, and define Q_J by the displayed left fold. Holomorphy supplies
   continuity and separate holomorphy on U. The separate-holomorphy regularity
   theorem gives complex C-infinity on U, as in Lebl Proposition 1.1.3. On the
   same open set, smoothness of the derivative field and continuous-linear
   evaluation at a fixed vector preserve C-infinity. Induct over the finite
   list. Complex smoothness gives complex differentiability there. Symmetry
   of the actual second Fréchet derivative gives adjacent-coordinate swaps;
   finite-list permutation and equal counts give order independence. No
   derivative value outside U is used.
2. Choose positive radii with the closed polydisc contained in U. Lebl's
   successive Cauchy formula gives the order-zero identity. On a smaller closed
   polydisc, every factor has a fixed positive pole margin
   delta_j = R_j - r_j. On the compact distinguished boundary f is bounded.
   At each interior point choose a parameter neighbourhood whose closure is
   inside that smaller polydisc. These choices are made for each finite order.
3. For K_beta(z,zeta)=f(zeta) product_j(zeta_j-z_j)^(-beta_j), its parameter
   derivative is v mapped to K_beta times sum_j beta_j v_j/(zeta_j-z_j).
   The product-norm operator bound is M product_j delta_j^(-beta_j) times
   sum_j beta_j/delta_j. Parametrize circle j by a_j+R_j exp(i theta),
   theta from zero to two pi; its complex integration weight is i R_j exp(i theta).
   The weighted kernels and their derivative kernels are continuous on the
   compact circle-parameter products. Thus the parameter carrier is a
   neighbourhood; the kernels are strongly measurable; the base integrand
   is interval integrable; its derivative is strongly measurable; the bound
   holds at every parameter in the carrier; the constant bound is integrable;
   and the stated Fréchet derivative holds everywhere. These are the seven
   dominated-differentiation guards. Integrate the innermost circle first.
   Compact uniform continuity and the circle-integral norm bound give
   continuity and the same guards for each remaining outer integral, with
   its bound multiplied by two pi R_inner. Target continuous-linear-map
   spaces are complete finite-dimensional complex spaces. Finite sum and
   scalar linearity identify the integrated derivative without changing order.
4. Appending coordinate j differentiates its reciprocal power with multiplier
   alpha_j+1. The already-proved count identity identifies the increasing
   list followed by j with the list of alpha+e_j. Induction on the sum of
   the natural coordinates gives the displayed formula for every alpha,
   starting at zero. The exact factorial product gains alpha_j+1 at each
   increment. Local equality on the open polydisc identifies the actual
   Fréchet derivatives; no derivative outside that set is used. Commutation
   was proved from actual second-derivative symmetry, not assumed as data.
5. At the centre, the integral is exactly the displayed Cauchy coefficient.
   Every natural factorial is positive, so its complex scalar is nonzero.
   If every coordinate jet at a is zero, all Cauchy coefficients are zero.
   The convergent polydisc Cauchy power-series representation therefore makes
   f zero on an open polydisc around a. This is the local part of Lebl's
   identity-theorem proof and needs no connectedness of U.

The hypothesis d >= 1 is explicit. The zero multi-index includes f itself;
the empty open set gives vacuous local conclusions. No regularity outside U,
power-series input hypothesis, Euclidean replacement norm, or connectedness
assumption is introduced. -/
theorem lebl_polydisc_holomorphic_coordinate_derivatives
    {d : ℕ} (hd : 1 ≤ d) (U : Set (Fin d → ℂ)) (hU : IsOpen U)
    (f : (Fin d → ℂ) → ℂ) (hf : DifferentiableOn ℂ f U) :
    (∀ J : List (Fin d),
      ContDiffOn ℂ ∞ (orderedDerivative f J) U ∧
        DifferentiableOn ℂ (orderedDerivative f J) U) ∧
    (∀ J K : List (Fin d), (∀ j, J.count j = K.count j) →
      Set.EqOn (orderedDerivative f J) (orderedDerivative f K) U) ∧
    (∀ (α : Fin d → ℕ) (j : Fin d),
      Set.EqOn (coordinateDerivative j (multiIndexDerivative f α))
        (multiIndexDerivative f (α + Pi.single j 1)) U) ∧
    (∀ (a : Fin d → ℂ) (R : Fin d → ℝ),
      (∀ j, 0 < R j) → closedPolydisc a R ⊆ U →
      (∀ (α : Fin d → ℕ) (z : Fin d → ℂ), z ∈ openPolydisc a R →
        multiIndexDerivative f α z = (multiIndexFactorial α : ℂ) *
          ((2 * (Real.pi : ℂ) * Complex.I) ^ d)⁻¹ *
            distinguishedBoundaryIntegral a R (cauchyKernel f α z)) ∧
      (∀ α : Fin d → ℕ,
        (multiIndexFactorial α : ℂ) * cauchyCoefficient f a R α =
          multiIndexDerivative f α a)) ∧
    (∀ a ∈ U, (∀ α : Fin d → ℕ, multiIndexDerivative f α a = 0) →
      ∃ V : Set (Fin d → ℂ), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
        ∀ z ∈ V, f z = 0) := by
  suffices hC : ∀ (a : Fin d → ℂ) (R : Fin d → ℝ),
      (∀ j, 0 < R j) → closedPolydisc a R ⊆ U →
      ∀ (α : Fin d → ℕ) (z : Fin d → ℂ), z ∈ openPolydisc a R →
        multiIndexDerivative f α z = (multiIndexFactorial α : ℂ) *
          ((2 * (Real.pi : ℂ) * Complex.I) ^ d)⁻¹ *
            distinguishedBoundaryIntegral a R (cauchyKernel f α z) by
    have hcoef : ∀ a R, (∀ j, 0 < R j) → closedPolydisc a R ⊆ U →
        ∀ α, (multiIndexFactorial α : ℂ) * cauchyCoefficient f a R α =
          multiIndexDerivative f α a := by
      intro a R hR hclosed α
      have ha : a ∈ openPolydisc a R := fun j ↦ by simpa using hR j
      simpa only [cauchyCoefficient, mul_assoc] using (hC a R hR hclosed α a ha).symm
    have hs := contDiffOn_of_holomorphic hU hf
    refine ⟨fun J ↦ orderedDerivative_regular hU hs J,
      fun J K hcount ↦ orderedDerivative_eq_of_count hU hs J K hcount,
      multiIndexDerivative_increment hU hs,
      (fun a R hR hclosed ↦ ⟨hC a R hR hclosed, hcoef a R hR hclosed⟩), ?_⟩
    intro a ha hzero
    exact zeroJet_germ_of_coefficients hd hU hf hcoef ha hzero
  intro a R hR hclosed
  have hP := isOpen_openPolydisc a R
  have hPU : openPolydisc a R ⊆ U := fun z hz ↦ hclosed (fun j ↦ (hz j).le)
  have hboundary : HolomorphicAnosov.PolydiscBoundaryCauchySeries.distinguishedBoundary a R ⊆ U :=
    fun ζ hζ ↦ hclosed (fun j ↦ (hζ j).le)
  have hfb := hf.continuousOn.mono hboundary
  have hs := contDiffOn_of_holomorphic hU hf
  apply multiIndex_induction
  · intro z hz
    exact cauchy_formula_zero hd hU hf a R hR hclosed hz
  · intro α j ih z hz
    have heq : Set.EqOn (multiIndexDerivative f α)
        (fun w ↦ ((multiIndexFactorial α : ℂ) *
          ((2 * (Real.pi : ℂ) * Complex.I) ^ d)⁻¹) •
            distinguishedBoundaryIntegral a R (cauchyKernel f α w)) (openPolydisc a R) := by
      intro w hw
      exact ih w hw
    calc
      multiIndexDerivative f (α + Pi.single j 1) z =
          coordinateDerivative j (multiIndexDerivative f α) z :=
        (multiIndexDerivative_increment hU hs α j (hPU hz)).symm
      _ = coordinateDerivative j
          (fun w ↦ ((multiIndexFactorial α : ℂ) *
            ((2 * (Real.pi : ℂ) * Complex.I) ^ d)⁻¹) •
              distinguishedBoundaryIntegral a R (cauchyKernel f α w)) z :=
        coordinateDerivative_congr hP heq j hz
      _ = ((multiIndexFactorial α : ℂ) *
            ((2 * (Real.pi : ℂ) * Complex.I) ^ d)⁻¹) *
          ((α j + 1 : ℂ) * distinguishedBoundaryIntegral a R
            (cauchyKernel f (α + Pi.single j 1) z)) := by
        rw [coordinateDerivative_const_smul j _ (boundaryIntegral_differentiableAt f α a R hR hfb hz),
          boundaryIntegral_coordinateDerivative f α a R hR hfb hz j]
        rfl
      _ = _ := by
        rw [multiIndexFactorial_increment]
        push_cast
        ring


end

end HolomorphicAnosov.Analysis.Complex
