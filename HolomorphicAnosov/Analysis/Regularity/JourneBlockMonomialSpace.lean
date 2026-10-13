import HolomorphicAnosov.Analysis.Regularity.GraphFoliationData
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import HolomorphicAnosov.Analysis.Regularity.JourneFiniteSampling
import HolomorphicAnosov.Analysis.Regularity.JourneWeightedInterpolation
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Whole-block polynomial sampling

Source: Journé (1988), Lemma 1, pp. 188–189, in the arbitrary-block formulation
of the parent construction. The finite coefficient space contains every exponent
of whole-block total degree at most `n`. Its monomial expansion reconstructs
every such polynomial, and evaluation at suitable finitely many points is an
isomorphism. The stable evaluation inverse controls perturbed sample grids.
-/

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- All exponent vectors of total degree at most n in one Euclidean block. -/
abbrev BlockDegreeIndex (d n : ℕ) :=
  {m : Fin d →₀ ℕ // m.sum (fun _ e ↦ e) ≤ n}

instance (d n : ℕ) : Fintype (BlockDegreeIndex d n) := by
  have : Module.Finite ℝ (MvPolynomial.restrictSupport ℝ
      {m : Fin d →₀ ℕ | m.sum (fun _ e ↦ e) ≤ n}) :=
    inferInstanceAs (Module.Finite ℝ (MvPolynomial.restrictTotalDegree (Fin d) ℝ n))
  have : Finite (BlockDegreeIndex d n) := Module.Finite.finite_basis
    (MvPolynomial.basisRestrictSupport ℝ {m : Fin d →₀ ℕ | m.sum (fun _ e ↦ e) ≤ n})
  exact Fintype.ofFinite _

/-- The finite whole-block total-degree support; it is not a coordinate-degree box. -/
def blockDegreeSupport (d n : ℕ) : Finset (Fin d →₀ ℕ) :=
  @Set.toFinset (Fin d →₀ ℕ) {m | m.sum (fun _ e ↦ e) ≤ n}
    (inferInstance : Fintype (BlockDegreeIndex d n))

@[simp] theorem mem_blockDegreeSupport {d n : ℕ} (m : Fin d →₀ ℕ) :
    m ∈ blockDegreeSupport d n ↔ m.sum (fun _ e ↦ e) ≤ n := by
  simp [blockDegreeSupport]

/-- A coefficient array on the whole-block degree support defines its actual
multivariate polynomial by the finite monomial expansion. -/
def blockPolynomial {d n : ℕ} (c : BlockDegreeIndex d n → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ i, MvPolynomial.monomial i.val (c i)

@[simp] theorem blockPolynomial_coeff {d n : ℕ}
    (c : BlockDegreeIndex d n → ℝ) (m : Fin d →₀ ℕ) :
    (blockPolynomial c).coeff m = if hm : m.sum (fun _ e ↦ e) ≤ n then c ⟨m,hm⟩ else 0 := by
  classical
  simp only [blockPolynomial,MvPolynomial.coeff_sum]
  by_cases hm : m.sum (fun _ e ↦ e) ≤ n
  · rw [dite_eq_left hm,Finset.sum_eq_single ⟨m,hm⟩]
    · simp
    · intro j _ hne
      have hval : j.val ≠ m := fun h ↦ hne (Subtype.ext h)
      simp [MvPolynomial.coeff_monomial,hval]
    · simp
  · rw [dite_eq_right hm]
    apply Finset.sum_eq_zero
    intro j _
    have hval : j.val ≠ m := fun h ↦ hm (h ▸ j.property)
    simp [MvPolynomial.coeff_monomial,hval]

/-- Every polynomial of total degree at most n has exactly the coefficients
in this whole-block support, with no discarded monomials. -/
theorem blockPolynomial_coeff_reconstruct {d n : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ n) : blockPolynomial (fun i : BlockDegreeIndex d n ↦ P.coeff i.val) = P := by
  ext m
  rw [blockPolynomial_coeff]
  split_ifs with hm
  · rfl
  · symm
    exact MvPolynomial.coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hP (lt_of_not_ge hm))

/-- Homogeneous scalar scaling of a genuine multivariate monomial evaluated
in the original Euclidean block. -/
theorem block_monomial_homogeneous {d : ℕ} (m : Fin d →₀ ℕ) (t : ℝ) (z : Block d) :
    MvPolynomial.eval (fun i ↦ (t • z) i) (MvPolynomial.monomial m (1:ℝ)) =
      t^(m.sum fun _ e ↦ e)*MvPolynomial.eval (fun i ↦ z i) (MvPolynomial.monomial m (1:ℝ)) := by
  classical
  simp only [MvPolynomial.eval_monomial,one_mul,PiLp.smul_apply,smul_eq_mul,
    Finsupp.prod,mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finsupp.sum]

/-- Exact evaluation of the finite coefficient expansion. -/
theorem blockPolynomial_eval {d n : ℕ} (c : BlockDegreeIndex d n → ℝ) (z : Block d) :
    MvPolynomial.eval (fun k ↦ z k) (blockPolynomial c) =
      ∑ i, c i * MvPolynomial.eval (fun k ↦ z k) (MvPolynomial.monomial i.val (1:ℝ)) := by
  classical
  simp [blockPolynomial,MvPolynomial.eval_monomial]

/-- Total-degree block monomials admit unisolvent Euclidean samples. This
includes the zero-dimensional block, where the sole monomial is the constant. -/
theorem block_unisolvent_samples (d n : ℕ) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → Block d)
      (E : (BlockDegreeIndex d n → ℝ) ≃L[ℝ] (κ → ℝ)),
        ∀ c k, E c k = ∑ i, c i * MvPolynomial.eval (fun j ↦ a k j)
          (MvPolynomial.monomial i.val (1:ℝ)) := by
  classical
  let L : MvPolynomial (Fin d) ℝ →ₗ[ℝ] ((Fin d → ℝ) → ℝ) :=
    LinearMap.pi fun x ↦ (MvPolynomial.aeval x).toLinearMap
  have hL : Function.Injective L := by
    intro P Q h
    apply MvPolynomial.funext
    intro x
    exact congrFun h x
  let f : BlockDegreeIndex d n → (Fin d → ℝ) → ℝ :=
    fun i x ↦ MvPolynomial.eval x (MvPolynomial.monomial i.val (1:ℝ))
  have hf : LinearIndependent ℝ f :=
    (L.linearIndependent_iff_of_injOn hL.injOn).mpr
      ((MvPolynomial.basisMonomials (Fin d) ℝ).linearIndependent.comp
        (fun i : BlockDegreeIndex d n ↦ i.val) Subtype.val_injective)
  obtain ⟨κ,inst,a,_,_,E,hE⟩ := finite_unisolvent_samples f hf ∅ (by simp)
  exact ⟨κ,inst,fun k ↦ WithLp.toLp 2 (a k),E,hE⟩

/-- Monomial evaluation is continuous on the actual Euclidean block. -/
theorem block_monomial_continuous {d : ℕ} (m : Fin d →₀ ℕ) :
    Continuous (fun z : Block d ↦ MvPolynomial.eval (fun k ↦ z k)
      (MvPolynomial.monomial m (1:ℝ))) :=
  (MvPolynomial.continuous_eval (MvPolynomial.monomial m (1:ℝ))).comp (continuous_pi fun k ↦ PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) k)

/-- Polynomial sample values control evaluation uniformly on a fixed normalized
ball, at every real physical scale and every sufficiently perturbed grid.

Source: Journé (1988), Lemma 1, pp. 188–189. The stable sampling inverse bounds
coefficients uniformly near the original grid. Continuity of the finite monomial
vector gives a uniform bound on the compact normalized closed ball, so its finite
pairing with those coefficients bounds evaluation throughout the ball. Expand
the polynomial in all monomials of total degree at most `n`; multiplying each
coefficient by `t` to its monomial degree transfers this normalized estimate to
the physical scale. Homogeneity justifies both sample and target evaluations.
No division by the scale is used, so zero and negative scales are included;
negative radii give a vacuous target region, and dimension zero is included. -/
theorem block_polynomial_sampling_bound {d n : ℕ} {κ : Type*} [Fintype κ]
    (a : κ → Block d) (E : (BlockDegreeIndex d n → ℝ) ≃L[ℝ] (κ → ℝ))
    (hE : ∀ c k, E c k = ∑ i, c i * MvPolynomial.eval (fun j ↦ a k j)
      (MvPolynomial.monomial i.val (1:ℝ))) (R : ℝ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧ ∀ b : κ → Block d, ‖b-a‖ < δ →
      ∀ (t : ℝ) (P : MvPolynomial (Fin d) ℝ), P.totalDegree ≤ n →
      ∀ M : ℝ, 0 ≤ M →
      (∀ k, |MvPolynomial.eval (fun j ↦ (t • b k) j) P| ≤ M) →
      ∀ y : Block d, ‖y‖ ≤ R → |MvPolynomial.eval (fun j ↦ (t • y) j) P| ≤ L*M := by
  classical
  let f : BlockDegreeIndex d n → Block d → ℝ :=
    fun i z ↦ MvPolynomial.eval (fun j ↦ z j) (MvPolynomial.monomial i.val (1:ℝ))
  obtain ⟨δ,L,hδ,hL,H⟩ := stable_interpolation_evaluation_bound f
    (fun i ↦ block_monomial_continuous i.val) a E hE
    (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
  refine ⟨δ,L,hδ,hL,?_⟩
  intro b hb t P hP M hM hs y hy
  let c : BlockDegreeIndex d n → ℝ := fun i ↦ P.coeff i.val*t^(i.val.sum fun _ e ↦ e)
  have heval (z : Block d) : MvPolynomial.eval (fun j ↦ (t • z) j) P =
      ∑ i, c i*f i z := by
    conv_lhs => rw [← blockPolynomial_coeff_reconstruct P hP]
    rw [blockPolynomial_eval]
    simp_rw [block_monomial_homogeneous]
    apply Finset.sum_congr rfl
    intro i _
    exact (mul_assoc _ _ _).symm
  rw [heval]
  exact H b hb c M hM (fun k ↦ by rw [← heval]; exact hs k) y
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)

/-- Expand an exponent vector into a list of repeated coordinate factors. The
list length is exactly the whole-block total degree, including degree zero. -/
theorem monomial_coordinate_factors {d : ℕ} (m : Fin d →₀ ℕ) :
    ∃ l : List (Fin d), l.length = m.sum (fun _ e ↦ e) ∧
      ∀ z : Fin d → ℝ, MvPolynomial.eval z (MvPolynomial.monomial m (1:ℝ)) =
        ∏ j : Fin l.length, z (l.get j) := by
  classical
  let l := m.toMultiset.toList
  refine ⟨l,by simp [l,Function.id_def],?_⟩
  intro z
  rw [MvPolynomial.eval_monomial,one_mul]
  have hl : (∏ j : Fin l.length, z (l.get j)) = (l.map z).prod :=
    Fin.prod_univ_fun_getElem l z
  rw [hl]
  dsimp [l]
  rw [Multiset.prod_map_toList,Finsupp.toMultiset_map,Finsupp.prod_toMultiset]
  exact (Finsupp.prod_mapDomain_index (f := z) (s := m) (h := fun a n ↦ a^n)
    (fun a ↦ pow_zero a) (fun a j k ↦ pow_add a j k)).symm

/-- Tensor monomials use a separate total-degree cutoff in each block. -/
abbrev BlockBidegreeIndex (p q n : ℕ) := BlockDegreeIndex p n × BlockDegreeIndex q n

def blockBimonomial {p q n : ℕ} (i : BlockBidegreeIndex p q n) (z : Block p × Block q) : ℝ :=
  MvPolynomial.eval (fun j ↦ z.1 j) (MvPolynomial.monomial i.1.val (1:ℝ)) *
    MvPolynomial.eval (fun j ↦ z.2 j) (MvPolynomial.monomial i.2.val (1:ℝ))

def blockBidegree {p q n : ℕ} (i : BlockBidegreeIndex p q n) : ℕ :=
  (i.1.val.sum fun _ e ↦ e)+(i.2.val.sum fun _ e ↦ e)

theorem block_bimonomial_continuous {p q n : ℕ} (i : BlockBidegreeIndex p q n) :
    Continuous (blockBimonomial i) :=
  ((block_monomial_continuous i.1.val).comp continuous_fst).mul
    ((block_monomial_continuous i.2.val).comp continuous_snd)

theorem block_bimonomial_homogeneous {p q n : ℕ} (i : BlockBidegreeIndex p q n)
    (t : ℝ) (z : Block p × Block q) :
    blockBimonomial i (t • z) = t^(blockBidegree i)*blockBimonomial i z := by
  simp only [blockBimonomial,Prod.smul_fst,Prod.smul_snd,block_monomial_homogeneous,
    blockBidegree,pow_add]
  ring

/-- The two genuine block sampling grids yield the tensor evaluation inverse
for all monomials having total degree at most n in each block. -/
theorem block_tensor_grid_evaluation {p q n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (a : I → Block p) (b : J → Block q)
    (E₁ : (BlockDegreeIndex p n → ℝ) ≃L[ℝ] (I → ℝ))
    (E₂ : (BlockDegreeIndex q n → ℝ) ≃L[ℝ] (J → ℝ))
    (hE₁ : ∀ c k, E₁ c k = ∑ i, c i * MvPolynomial.eval (fun j ↦ a k j)
      (MvPolynomial.monomial i.val (1:ℝ)))
    (hE₂ : ∀ c k, E₂ c k = ∑ i, c i * MvPolynomial.eval (fun j ↦ b k j)
      (MvPolynomial.monomial i.val (1:ℝ))) :
    ∃ E : (BlockBidegreeIndex p q n → ℝ) ≃L[ℝ] ((I × J) → ℝ),
      ∀ c k, E c k = ∑ i, c i*blockBimonomial i (a k.1,b k.2) :=
  product_grid_flat_evaluation_equiv _ _ E₁ E₂ hE₁ hE₂

end HolomorphicAnosov.JourneLeafPolynomialApproximation
