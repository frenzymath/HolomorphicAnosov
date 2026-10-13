import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.LeblHolomorphicHypersurfaceRegularPointsG9
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Injective holomorphic maps in equal complex dimension

Source: Jiří Lebl, *Tasty Bits of Several Complex Variables*, version 3.4
(December 23, 2020), §1.6 Theorem 1.6.5, printed pages 37–38.

Holomorphicity on an open subset is expressed by `DifferentiableOn ℂ`.
Maps and inverses are total functions whose values outside the stated open
sets are irrelevant. The derivative determinant is taken over ℂ.
-/

namespace HolomorphicAnosov

open Set Filter
open scoped Topology _root_.Topology ContDiff

/-- The vector-valued specialization of Lebl's coordinate regularity provider
(source proof I1 below). Apply the existing scalar theorem to each literal output
coordinate and its empty derivative list, then reassemble the same map by
`contDiffOn_pi`. This lemma retains the supplier's named admission. -/
theorem lebl_vector_contDiffOn {n : ℕ} (hn : 0 < n)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {F : (Fin n → ℂ) → (Fin n → ℂ)} (hF : DifferentiableOn ℂ F U) :
    ContDiffOn ℂ ∞ F U := by
  apply contDiffOn_pi.mpr
  intro i
  have hi : DifferentiableOn ℂ (fun z ↦ F z i) U := differentiableOn_pi.mp hF i
  simpa [Analysis.Complex.LeblPolydisc.orderedDerivative] using
    (Analysis.Complex.lebl_polydisc_holomorphic_coordinate_derivatives
      hn U hU (fun z ↦ F z i) hi).1 [] |>.1

/-- The actual Jacobian determinant is holomorphic on the same original open
domain (Lebl source proof I1). Complex smoothness gives differentiability of the
actual Fréchet derivative. Its matrix entries in the literal coordinate basis
are holomorphic by evaluation, and the determinant is their finite signed sum
of finite products. No analyticity or regularity of values off U is assumed. -/
theorem lebl_jacobian_differentiableOn {n : ℕ} (hn : 0 < n)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {F : (Fin n → ℂ) → (Fin n → ℂ)} (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (fun z ↦ LinearMap.det (fderiv ℂ F z).toLinearMap) U := by
  have hs := lebl_vector_contDiffOn hn hU hF
  have hd : DifferentiableOn ℂ (fderiv ℂ F) U :=
    (hs.fderiv_of_isOpen hU (m := 1) (by simp)).differentiableOn (by simp)
  have he (i j : Fin n) : DifferentiableOn ℂ
      (fun z ↦ (fderiv ℂ F z) (Pi.single j 1) i) U := by
    have h := hd.clm_apply (differentiableOn_const (c := Pi.single j (1 : ℂ)))
    exact differentiableOn_pi.mp h i
  have heq : (fun z ↦ LinearMap.det (fderiv ℂ F z).toLinearMap) =
      (fun z ↦ ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
        ∏ j, (fderiv ℂ F z) (Pi.single j 1) (σ j)) := by
    funext z
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin n)), Matrix.det_apply']
    simp
  rw [heq]
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.const_mul
  have hp : ∀ s : Finset (Fin n), DifferentiableOn ℂ
      (fun z ↦ ∏ j ∈ s, (fderiv ℂ F z) (Pi.single j 1) (σ j)) U := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact fun z hz ↦ (he (σ a) a z hz).mul (ih z hz)
  exact hp Finset.univ

/-- The final inverse-function passage in Lebl Theorem 1.6.5 (source proof I7).
This is conditional only on its separately asserted nonzero-Jacobian conclusion;
it does not prove or assume that conclusion in the injective theorem. At each
original point construct the finite-order complex IFT homeomorphism. Its image
of the open source intersected with U is open. The literal `invFunOn F U` agrees
with this local inverse on that image by original injectivity. The complex C¹
inverse theorem at the center therefore proves holomorphy of the same totalized
global inverse. All source, image and inverse equations use the actual sets.
Empty U is included and no connectedness or prescribed inverse is assumed. -/
theorem lebl_inverse_of_nonzero_jacobian {n : ℕ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {F : (Fin n → ℂ) → (Fin n → ℂ)}
    (hF : ContDiffOn ℂ 1 F U) (hFinj : Set.InjOn F U)
    (hdet : ∀ z ∈ U, LinearMap.det (fderiv ℂ F z).toLinearMap ≠ 0) :
    IsOpen (F '' U) ∧
      ∃ G : (Fin n → ℂ) → (Fin n → ℂ),
        DifferentiableOn ℂ G (F '' U) ∧
          (∀ z ∈ U, G (F z) = z) ∧
          (∀ w ∈ F '' U, G w ∈ U ∧ F (G w) = w) := by
  classical
  let G := Function.invFunOn F U
  have hlocal (z : Fin n → ℂ) (hz : z ∈ U) :
      ∃ e : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ),
        (e : (Fin n → ℂ) → (Fin n → ℂ)) = F ∧ z ∈ e.source ∧
        ContDiffAt ℂ 1 e.symm (F z) := by
    have hf := hF.contDiffAt (hU.mem_nhds hz)
    let A := ((fderiv ℂ F z).toLinearMap.equivOfDetNeZero (hdet z hz)).toContinuousLinearEquiv
    have hA : (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F z := by
      ext v
      rfl
    have hdf : HasFDerivAt F (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) z := by
      rw [hA]
      exact (hf.differentiableAt (by simp)).hasFDerivAt
    let e := hf.toOpenPartialHomeomorph F hdf (by simp)
    refine ⟨e, rfl, hf.mem_toOpenPartialHomeomorph_source hdf (by simp), ?_⟩
    have hi := hf.to_localInverse hdf (by simp)
    exact hi
  have hopen : IsOpen (F '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨e, he, hze, _⟩ := hlocal z hz
    have ho : IsOpen (F '' (e.source ∩ U)) := by
      rw [← he]
      exact e.isOpen_image_of_subset_source (e.open_source.inter hU) inter_subset_left
    exact Filter.mem_of_superset (ho.mem_nhds ⟨z, ⟨hze, hz⟩, rfl⟩)
      (Set.image_mono inter_subset_right)
  refine ⟨hopen, G, ?_, hFinj.leftInvOn_invFunOn, ?_⟩
  · rintro w ⟨z, hz, rfl⟩
    obtain ⟨e, he, hze, hi⟩ := hlocal z hz
    have ho : IsOpen (F '' (e.source ∩ U)) := by
      rw [← he]
      exact e.isOpen_image_of_subset_source (e.open_source.inter hU) inter_subset_left
    have hagree : G =ᶠ[𝓝 (F z)] e.symm := by
      filter_upwards [ho.mem_nhds ⟨z, ⟨hze, hz⟩, rfl⟩] with w hw
      obtain ⟨a, ha, rfl⟩ := hw
      have hleft : G (F a) = a := hFinj.leftInvOn_invFunOn ha.2
      rw [hleft, ← he]
      exact (e.left_inv ha.1).symm
    exact (hi.congr_of_eventuallyEq hagree).differentiableAt (by simp)
      |>.differentiableWithinAt
  · intro w hw
    exact Function.invFunOn_pos hw

/-- The one-variable open-image part of Lebl's base case. Cauchy analyticity and
Mathlib's local open mapping dichotomy apply at each point of the actual open
domain. An eventually constant germ would contradict original injectivity on a
neighborhood, since a complex singleton is not open. Thus every open subdomain
has open image. No connectedness of the whole domain is needed. -/
theorem lebl_scalar_open_image {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {S : Set ℂ} (hS : IsOpen S) (hSU : S ⊆ U) : IsOpen (f '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z, hz, rfl⟩
  have ha := hf.analyticOnNhd hU z (hSU hz)
  have hnot : ¬ ∀ᶠ a in 𝓝 z, f a = f z := by
    intro hc
    have hs : ({z} : Set ℂ) ∈ 𝓝 z := by
      filter_upwards [hc, hU.mem_nhds (hSU hz)] with a hfa ha
      exact hinj ha (hSU hz) hfa
    exact not_isOpen_singleton z
      (isOpen_singleton_of_finite_mem_nhds z hs (Set.finite_singleton z))
  exact ha.eventually_constant_or_nhds_le_map_nhds.resolve_left hnot
    (image_mem_map (hS.mem_nhds hz))

/-- Scalar nonvanishing in Lebl's one-dimensional base (source proof I2).
The preceding open mapping argument constructs a homeomorphism of the ORIGINAL
open source onto its ORIGINAL image before invoking the published scalar
holomorphic-homeomorphism theorem. Its coordinate formula agrees with the same
total f near the marked point, so nonvanishing is about the actual derivative of
f. The scalar provider remains a named lower admission, not a new local sorry. -/
theorem lebl_scalar_deriv_ne_zero {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) :
    ∀ z ∈ U, deriv f z ≠ 0 := by
  classical
  intro z hz
  let S : TopologicalSpace.Opens ℂ := ⟨U, hU⟩
  let T : TopologicalSpace.Opens ℂ :=
    ⟨f '' U, lebl_scalar_open_image hU hf hinj hU Subset.rfl⟩
  have hpe : Set.BijOn f U (f '' U) :=
    ⟨fun _ hx ↦ ⟨_, hx, rfl⟩, hinj, Set.surjOn_image f U⟩
  let p := hpe.toPartialEquiv f U (f '' U)
  have hop : IsOpenMap (p.source.domRestrict p) := by
    intro W hW
    have hs : IsOpen ((Subtype.val : S → ℂ) '' W) :=
      hU.isOpenEmbedding_subtypeVal.isOpenMap W hW
    have heq : p.source.domRestrict p '' W = f '' ((Subtype.val : S → ℂ) '' W) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
    rw [heq]
    exact lebl_scalar_open_image hU hf hinj hs (Subtype.coe_image_subset _ _)
  let e0 := OpenPartialHomeomorph.ofContinuousOpenRestrict p hf.continuousOn hop hU
  let e : S ≃ₜ T := e0.toHomeomorphSourceTarget
  let a : S := ⟨z, hz⟩
  have hsmooth : ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun x : S ↦ f x) := by
    intro x
    apply contMDiffAt_subtype_iff.mpr
    exact ((hf.contDiffOn hU).contDiffAt (hU.mem_nhds x.property)).contMDiffAt
  have hesmooth : ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞ e := by
    apply (ContMDiff.subtypeVal_comp_iff T e).mp
    exact hsmooth
  have H := (Analysis.Complex.holomorphicEmbeddingInverse T e
    (hesmooth.mdifferentiable (by simp))).2
      (chartAt ℂ a) (OpenPartialHomeomorph.refl ℂ)
      (IsManifold.chart_mem_maximalAtlas a)
      (IsManifold.chart_mem_maximalAtlas (f z)) a (mem_chart_source ℂ a) (by simp)
  dsimp only at H
  rcases H with ⟨_, _, hzΩ, _, _, _, _, _, hder, _, _⟩
  have hne := (hder _ hzΩ).2
  have hagree : (fun w : ℂ ↦
      (OpenPartialHomeomorph.refl ℂ) (e ((chartAt ℂ a).symm w) : ℂ)) =ᶠ[𝓝 z] f := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hi : ((chartAt ℂ a).symm w).val = w := by
      have hleft := congrArg Subtype.val ((chartAt ℂ a).left_inv
        (show (⟨w, hw⟩ : S) ∈ (chartAt ℂ a).source from
          mem_chart_source ℂ (⟨w, hw⟩ : S)))
      have hforward : chartAt ℂ a (⟨w, hw⟩ : S) = w := rfl
      rwa [hforward] at hleft
    change f ((chartAt ℂ a).symm w).val = f w
    rw [hi]
  have hc : chartAt ℂ a a = z := rfl
  rw [hc] at hne
  exact hagree.deriv_eq.symm ▸ hne

/-- Lebl's base case on the exact `Fin 1 → ℂ` coordinate model. The fixed
continuous complex-linear coordinate evaluation and its constant-vector inverse
identify the original map with a scalar holomorphic injection. The chain rule
identifies its scalar derivative with the single actual Jacobian matrix entry;
the one-by-one determinant formula gives the stated nonvanishing. -/
theorem lebl_jacobian_ne_zero_dimension_one
    {U : Set (Fin 1 → ℂ)} (hU : IsOpen U)
    {F : (Fin 1 → ℂ) → (Fin 1 → ℂ)}
    (hF : DifferentiableOn ℂ F U) (hinj : Set.InjOn F U) :
    ∀ z ∈ U, LinearMap.det (fderiv ℂ F z).toLinearMap ≠ 0 := by
  let e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  let S : Set ℂ := e.symm ⁻¹' U
  let f : ℂ → ℂ := fun w ↦ e (F (e.symm w))
  have hS : IsOpen S := hU.preimage e.symm.continuous
  have hf : DifferentiableOn ℂ f S := by
    intro w hw
    exact (e.differentiableAt.comp w
      ((hF _ hw).differentiableAt (hU.mem_nhds hw) |>.comp w
        e.symm.differentiableAt)).differentiableWithinAt
  have hinjf : Set.InjOn f S := by
    intro w hw v hv h
    exact e.symm.injective (hinj hw hv (e.injective h))
  intro z hz
  have hs : e z ∈ S := by simpa [S] using hz
  have hne := lebl_scalar_deriv_ne_zero hS hf hinjf (e z) hs
  have hFz : HasFDerivAt F (fderiv ℂ F z) (e.symm (e z)) := by
    simpa using ((hF z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hdf := e.hasFDerivAt.comp (e z) (hFz.comp (e z) e.symm.hasFDerivAt)
  have hder : deriv f (e z) = (fderiv ℂ F z) (Pi.single (0 : Fin 1) 1) 0 := by
    have hd : HasDerivAt f ((fderiv ℂ F z) (Pi.single (0 : Fin 1) 1) 0) (e z) := by
      convert hdf.hasDerivAt using 1
      · rfl
      · change (fderiv ℂ F z) (Pi.single (0 : Fin 1) 1) 0 =
          (fderiv ℂ F z) (fun _ ↦ 1) 0
        have hv : (Pi.single (0 : Fin 1) (1 : ℂ) : Fin 1 → ℂ) = fun _ ↦ 1 := by
          ext i
          simp [Subsingleton.elim i (0 : Fin 1)]
        rw [hv]
    exact hd.deriv
  rw [hder] at hne
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 1)), Matrix.det_unique]
  simpa using hne

/-- Lebl's reduced-slice step I5, with the literal first coordinate fixed at its
original marked value. The slice domain is the actual preimage of U under that
insertion, hence open. The original first-output identity supplies injectivity
of the tail map and makes the first derivative row `(1,0,…,0)`. The complex chain
rule identifies its tail derivative matrix with the lower-right minor of DH;
expansion along row zero gives equality of the two actual determinants. This
lemma contains no induction assumption, Jacobian nonvanishing, inverse premise
or admission; it provides the exact input and algebra for applying induction. -/
theorem lebl_reduced_slice {n : ℕ}
    {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {H : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)}
    (hH : DifferentiableOn ℂ H U) (hinj : Set.InjOn H U)
    (hfirst : ∀ z ∈ U, H z 0 = z 0)
    (p : Fin (n + 1) → ℂ) (hp : p ∈ U) :
    let V := (fun y : Fin n → ℂ ↦ Fin.cons (p 0) y) ⁻¹' U
    let φ := fun y : Fin n → ℂ ↦ Fin.tail (H (Fin.cons (p 0) y))
    IsOpen V ∧ Fin.tail p ∈ V ∧ DifferentiableOn ℂ φ V ∧ Set.InjOn φ V ∧
      LinearMap.det (fderiv ℂ φ (Fin.tail p)).toLinearMap =
        LinearMap.det (fderiv ℂ H p).toLinearMap := by
  classical
  let insert : (Fin n → ℂ) → (Fin (n + 1) → ℂ) := fun y ↦ Fin.cons (p 0) y
  let V := insert ⁻¹' U
  let φ := fun y : Fin n → ℂ ↦ Fin.tail (H (insert y))
  let L : (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
    (0 : (Fin n → ℂ) →L[ℂ] ℂ).finCons (ContinuousLinearMap.id ℂ (Fin n → ℂ))
  have hi (y : Fin n → ℂ) : HasFDerivAt insert L y :=
    (hasFDerivAt_const (p 0) y).finCons (hasFDerivAt_id y)
  have hVp : Fin.tail p ∈ V := by simpa [V, insert] using hp
  have hdφ (y : Fin n → ℂ) (hy : y ∈ V) : HasFDerivAt φ
      (ContinuousLinearMap.pi (fun i : Fin n ↦
        (ContinuousLinearMap.proj i.succ).comp ((fderiv ℂ H (insert y)).comp L))) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    exact (hasFDerivAt_apply i.succ (H (insert y))).comp y
      (((hH (insert y) hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt.comp y (hi y))
  have hinjφ : Set.InjOn φ V := by
    intro y hy z hz heq
    have hh : H (insert y) = H (insert z) := by
      ext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [hfirst _ hy, hfirst _ hz]
        rfl
      · exact congrFun heq j
    have h := hinj hy hz hh
    exact congrArg Fin.tail h
  refine ⟨hU.preimage (continuous_const.finCons continuous_id), hVp,
    fun y hy ↦ (hdφ y hy).differentiableAt.differentiableWithinAt, hinjφ, ?_⟩
  have hdf := (hdφ (Fin.tail p) hVp).fderiv
  have hrow : ∀ j : Fin (n + 1), (fderiv ℂ H p) (Pi.single j 1) 0 =
      (Pi.single j (1 : ℂ) : Fin (n + 1) → ℂ) 0 := by
    intro j
    have heq : (fun z ↦ H z 0) =ᶠ[𝓝 p] (fun z ↦ z 0) := by
      filter_upwards [hU.mem_nhds hp] with z hz
      exact hfirst z hz
    have hd := (hasFDerivAt_apply (0 : Fin (n + 1)) (H p)).comp p
      ((hH p hp).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
    have hh := hd.fderiv
    change fderiv ℂ (fun z ↦ H z 0) p = _ at hh
    rw [heq.fderiv_eq, (hasFDerivAt_apply (0 : Fin (n + 1)) p).fderiv] at hh
    exact congrArg (fun A : (Fin (n + 1) → ℂ) →L[ℂ] ℂ ↦ A (Pi.single j 1)) hh.symm
  have hminor : LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))
      (fderiv ℂ φ (Fin.tail p)).toLinearMap =
      (LinearMap.toMatrix (Pi.basisFun ℂ (Fin (n + 1)))
        (Pi.basisFun ℂ (Fin (n + 1))) (fderiv ℂ H p).toLinearMap).submatrix
          Fin.succ Fin.succ := by
    ext i j
    rw [hdf]
    simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
      Matrix.submatrix_apply, ContinuousLinearMap.coe_pi]
    have hv : L (Pi.single j 1) = Pi.single j.succ 1 := by
      ext k
      refine Fin.cases ?_ (fun l ↦ ?_) k <;> simp [L, Pi.single_apply]
    simpa [insert] using congrArg (fun v ↦ (fderiv ℂ H p) v i.succ) hv
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin n)), hminor,
    ← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin (n + 1))), Matrix.det_succ_row_zero]
  simp [hrow, Fin.sum_univ_succ]

/-- The explicit triangular graph straightening in Lebl's source proof I3.
For the actual holomorphic graph g on an open V, the forward map is
`(y,w) ↦ (y,w-g y)` and the inverse is `(y,t) ↦ (y,t+g y)`. The source is the
original product V×D, and the target is its precise transformed domain, rather
than an assumed product neighborhood. Both inverse equations and complex
differentiability are proved on these exact domains. Graph points with g(y)∈D
go to the literal hyperplane with final coordinate zero. This is genuine chart
data and requires no nonzero derivative of the original defining function. -/
theorem lebl_graph_straightening {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V : Set E} {D : Set ℂ} (hV : IsOpen V) (hD : IsOpen D)
    (g : E → ℂ) (hg : DifferentiableOn ℂ g V) :
    ∃ e : OpenPartialHomeomorph (E × ℂ) (E × ℂ),
      e.source = V ×ˢ D ∧
      e.target = {p | p.1 ∈ V ∧ p.2 + g p.1 ∈ D} ∧
      (∀ p, e p = (p.1, p.2 - g p.1)) ∧
      (∀ p, e.symm p = (p.1, p.2 + g p.1)) ∧
      DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target ∧
      ∀ y ∈ V, g y ∈ D → e (y, g y) ∈ e.target ∧ e (y, g y) = (y, 0) := by
  let Ω : Set (E × ℂ) := V ×ˢ (Set.univ : Set ℂ)
  let Ψ : E × ℂ → E × ℂ := fun p ↦ (p.1, p.2 - g p.1)
  let Φ : E × ℂ → E × ℂ := fun p ↦ (p.1, p.2 + g p.1)
  have hgp : DifferentiableOn ℂ (fun p : E × ℂ ↦ g p.1) Ω :=
    hg.comp differentiableOn_fst (fun _ hp ↦ hp.1)
  have hΨ : DifferentiableOn ℂ Ψ Ω :=
    differentiableOn_fst.prodMk (differentiableOn_snd.sub hgp)
  have hΦ : DifferentiableOn ℂ Φ Ω :=
    differentiableOn_fst.prodMk (differentiableOn_snd.add hgp)
  have hΩ : IsOpen Ω := hV.prod isOpen_univ
  have htarget : IsOpen {p : E × ℂ | p.1 ∈ V ∧ p.2 + g p.1 ∈ D} := by
    have h := hΦ.snd.continuousOn.isOpen_inter_preimage hΩ hD
    convert h using 1
    ext p
    simp [Ω, Φ]
  let e : OpenPartialHomeomorph (E × ℂ) (E × ℂ) :=
    { toFun := Ψ
      invFun := Φ
      source := V ×ˢ D
      target := {p | p.1 ∈ V ∧ p.2 + g p.1 ∈ D}
      map_source' := by
        intro p hp
        simpa [Ψ] using hp
      map_target' := by intro p hp; exact hp
      left_inv' := by intro p _; simp [Ψ, Φ]
      right_inv' := by intro p _; simp [Ψ, Φ]
      continuousOn_toFun := hΨ.continuousOn.mono (fun _ hp ↦ ⟨hp.1, mem_univ _⟩)
      continuousOn_invFun := hΦ.continuousOn.mono (fun _ hp ↦ ⟨hp.1, mem_univ _⟩)
      open_source := hV.prod hD
      open_target := htarget }
  refine ⟨e, rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl,
    hΨ.mono (fun _ hp ↦ ⟨hp.1, mem_univ _⟩),
    hΦ.mono (fun _ hp ↦ ⟨hp.1, mem_univ _⟩), ?_⟩
  intro y hy hgy
  exact ⟨e.map_source ⟨hy, hgy⟩, by simp [e, Ψ]⟩

/-- The exact permuted graph-coordinate identification used by the published
regular-zero-set predicate. This constructs a genuine continuous complex-linear
equivalence, including the zero-dimensional parameter space. It identifies
product coordinates with `leblUnpermuteGraphCoordinates σ`, and its inverse
reads the SAME original coordinates selected by σ; it is not an unrelated
finite-dimensional model identification. -/
theorem lebl_graph_coordinates_equiv {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    ∃ e : ((Fin n → ℂ) × ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ),
      (∀ y w, e (y, w) = Analysis.leblUnpermuteGraphCoordinates σ y w) ∧
      ∀ z, e.symm z = (fun i ↦ z (σ i.castSucc), z (σ (Fin.last n))) := by
  let e : ((Fin n → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) :=
    { toFun := fun p ↦ Analysis.leblUnpermuteGraphCoordinates σ p.1 p.2
      invFun := fun z ↦ (fun i ↦ z (σ i.castSucc), z (σ (Fin.last n)))
      left_inv := by
        intro p
        ext i <;> simp [Analysis.leblUnpermuteGraphCoordinates]
      right_inv := by
        intro z
        ext i
        have hi : i = σ (σ.symm i) := by simp
        rw [hi]
        simp only [Analysis.leblUnpermuteGraphCoordinates, Equiv.symm_apply_apply]
        refine Fin.lastCases ?_ (fun j ↦ ?_) (σ.symm i) <;> simp
      map_add' := by
        intro p q
        ext i
        simp only [Analysis.leblUnpermuteGraphCoordinates, Prod.fst_add, Prod.snd_add,
          Pi.add_apply]
        refine Fin.lastCases ?_ (fun j ↦ ?_) (σ.symm i) <;> simp
      map_smul' := by
        intro a p
        ext i
        simp only [Analysis.leblUnpermuteGraphCoordinates, Prod.smul_fst, Prod.smul_snd,
          Pi.smul_apply, RingHom.id_apply]
        refine Fin.lastCases ?_ (fun j ↦ ?_) (σ.symm i) <;> simp }
  exact ⟨e.toContinuousLinearEquiv, fun _ _ ↦ rfl, fun _ ↦ rfl⟩

/-- Complex coordinate changes preserve the vanishing of the actual determinant
at every marked inverse image, by the chain rule and determinant composition
(Lebl I3). Only the forward original map and the actual chart inverse need
differentientiability at the relevant points; no conclusion about injective
maps is assumed. The source/target membership guards give the genuine inverse
point inside the original open domain. -/
theorem lebl_jacobian_zero_after_coordinate_change {n : ℕ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {F : (Fin n → ℂ) → (Fin n → ℂ)} (hF : DifferentiableOn ℂ F U)
    (e : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
    (hei : DifferentiableOn ℂ e.symm e.target)
    (hsource : e.source ⊆ U) (w : Fin n → ℂ) (hw : w ∈ e.target)
    (hzero : LinearMap.det (fderiv ℂ F (e.symm w)).toLinearMap = 0) :
    LinearMap.det (fderiv ℂ (F ∘ e.symm) w).toLinearMap = 0 := by
  have ha := e.map_target hw
  rw [fderiv_comp w ((hF _ (hsource ha)).differentiableAt (hU.mem_nhds (hsource ha)))
    ((hei w hw).differentiableAt (e.open_target.mem_nhds hw))]
  change LinearMap.det ((fderiv ℂ F (e.symm w)).toLinearMap.comp
    (fderiv ℂ e.symm w).toLinearMap) = 0
  rw [LinearMap.det_comp, hzero, zero_mul]

/-- The actual G map from Lebl I4: replace the first input coordinate by the
first output component of F and retain every other original coordinate. The
chain rule gives its derivative; expansion along column zero proves that its
determinant is exactly that marked component's first partial derivative.
Thus the source's nonzero tangential partial really supplies the complex IFT
invertibility guard for this same G, without assuming any Jacobian of F nonzero. -/
theorem lebl_coordinate_replacement_det {n : ℕ}
    {F : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)}
    (p : Fin (n + 1) → ℂ) (hF : DifferentiableAt ℂ F p) :
    LinearMap.det (fderiv ℂ (fun z ↦ Fin.cons (F z 0) (Fin.tail z)) p).toLinearMap =
      (fderiv ℂ F p) (Pi.single (0 : Fin (n + 1)) 1) 0 := by
  let T : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi (fun i : Fin n ↦ ContinuousLinearMap.proj i.succ)
  let A : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
    ((ContinuousLinearMap.proj (0 : Fin (n + 1))).comp (fderiv ℂ F p)).finCons T
  have h0 : HasFDerivAt (fun z ↦ F z 0)
      ((ContinuousLinearMap.proj (0 : Fin (n + 1))).comp (fderiv ℂ F p)) p :=
    (ContinuousLinearMap.proj (0 : Fin (n + 1)) :
      (Fin (n + 1) → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp p hF.hasFDerivAt
  have ht : HasFDerivAt Fin.tail T p := T.hasFDerivAt
  have hd : HasFDerivAt (fun z ↦ Fin.cons (F z 0) (Fin.tail z)) A p := h0.finCons ht
  rw [hd.fderiv, ← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin (n + 1))),
    Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have htail : ∀ i : Fin n, LinearMap.toMatrix (Pi.basisFun ℂ (Fin (n + 1)))
      (Pi.basisFun ℂ (Fin (n + 1))) A.toLinearMap i.succ 0 = 0 := by
    intro i
    simp [A, T]
  simp only [htail, mul_zero, Fin.val_zero,
    pow_zero, one_mul, Fin.succAbove_zero]
  have hminor : (LinearMap.toMatrix (Pi.basisFun ℂ (Fin (n + 1)))
      (Pi.basisFun ℂ (Fin (n + 1))) A.toLinearMap).submatrix Fin.succ Fin.succ =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp [A, T, Matrix.one_apply, Pi.single_apply]
  rw [hminor, Matrix.det_one, mul_one]
  simp [A]

/-- The fully guarded local inverse of the SAME coordinate-replacement G in
Lebl I4. Its sole nonvanishing input is the one tangential partial of F used by
the source contradiction, not the Jacobian of F. A continuous nonzero-Jacobian
neighborhood for G is cut out inside the actual U and IFT source. At EVERY point
of its open image, the inverse is complex C¹, hence holomorphic, by the same
original IFT homeomorphism's inverse-regularity theorem. The first-coordinate
identity for F∘G⁻¹ holds throughout that entire open image. This supplies exact
guards for the reduced-slice induction, not an assumed smooth inverse. -/
theorem lebl_coordinate_replacement_local_inverse {n : ℕ}
    {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {F : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)}
    (hF : DifferentiableOn ℂ F U)
    (p : Fin (n + 1) → ℂ) (hp : p ∈ U)
    (hpartial : (fderiv ℂ F p) (Pi.single (0 : Fin (n + 1)) 1) 0 ≠ 0) :
    ∃ (e : OpenPartialHomeomorph (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ))
      (V : Set (Fin (n + 1) → ℂ)),
      (e : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)) =
        (fun z ↦ Fin.cons (F z 0) (Fin.tail z)) ∧
      IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ e.source ∧ IsOpen (e '' V) ∧
      DifferentiableOn ℂ e.symm (e '' V) ∧
      ∀ w ∈ e '' V, e.symm w ∈ V ∧ F (e.symm w) 0 = w 0 := by
  classical
  let G := fun z : Fin (n + 1) → ℂ ↦ Fin.cons (F z 0) (Fin.tail z)
  have hG : DifferentiableOn ℂ G U := by
    intro z hz
    apply DifferentiableWithinAt.finCons
    · exact differentiableWithinAt_pi.mp (hF z hz) 0
    · apply differentiableWithinAt_pi.mpr
      intro i
      exact (differentiableAt_apply i.succ z).differentiableWithinAt
  have hs := lebl_vector_contDiffOn (Nat.zero_lt_succ n) hU hG
  have hj := lebl_jacobian_differentiableOn (Nat.zero_lt_succ n) hU hG
  have hdetp : LinearMap.det (fderiv ℂ G p).toLinearMap ≠ 0 := by
    rw [lebl_coordinate_replacement_det p ((hF p hp).differentiableAt (hU.mem_nhds hp))]
    exact hpartial
  have hc : ContDiffAt ℂ 1 G p := (hs.of_le (by simp)).contDiffAt (hU.mem_nhds hp)
  let A := ((fderiv ℂ G p).toLinearMap.equivOfDetNeZero hdetp).toContinuousLinearEquiv
  have hA : (A : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)) = fderiv ℂ G p := by
    ext v
    rfl
  have hd : HasFDerivAt G (A : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)) p := by
    rw [hA]
    exact (hc.differentiableAt (by simp)).hasFDerivAt
  let e := hc.toOpenPartialHomeomorph G hd (by simp)
  have hep : p ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  let W := U ∩ (fun z ↦ LinearMap.det (fderiv ℂ G z).toLinearMap) ⁻¹' ({0} : Set ℂ)ᶜ
  have hW : IsOpen W := hj.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  let V := W ∩ e.source
  have hV : IsOpen V := hW.inter e.open_source
  have hpV : p ∈ V := ⟨⟨hp, hdetp⟩, hep⟩
  have hVs : V ⊆ e.source := inter_subset_right
  refine ⟨e, V, rfl, hV, hpV, fun _ hz ↦ ⟨hz.1.1, hz.2⟩,
    e.isOpen_image_of_subset_source hV hVs, ?_, ?_⟩
  · rintro w ⟨z, hz, rfl⟩
    have hleft := e.left_inv (hVs hz)
    have hzU : z ∈ U := hz.1.1
    have hzdet : LinearMap.det (fderiv ℂ G z).toLinearMap ≠ 0 := hz.1.2
    let B := ((fderiv ℂ G z).toLinearMap.equivOfDetNeZero hzdet).toContinuousLinearEquiv
    have hB : (B : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)) = fderiv ℂ G z := by
      ext v
      rfl
    have hdf : HasFDerivAt e (B : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ))
        (e.symm (e z)) := by
      rw [hleft, hB]
      exact (hG z hzU).differentiableAt (hU.mem_nhds hzU) |>.hasFDerivAt
    have hc1 : ContDiffAt ℂ 1 e (e.symm (e z)) := by
      rw [hleft]
      exact (hs.of_le (by simp)).contDiffAt (hU.mem_nhds hzU)
    exact (e.contDiffAt_symm (e.map_source (hVs hz)) hdf hc1).differentiableAt (by simp)
      |>.differentiableWithinAt
  · rintro w ⟨z, hz, rfl⟩
    rw [e.left_inv (hVs hz)]
    exact ⟨hz, rfl⟩

/-- The contradiction of Lebl I4–I5 at the marked first partial. The induction
operand is exactly the lower-dimensional Jacobian theorem, applied to the
literal open slice supplied by `lebl_reduced_slice`. The same coordinate
replacement inverse makes H's first component the first coordinate. Original
injectivity gives slice injectivity, and the actual chain rule makes DH's
determinant zero at the original marked image. Expansion along the first row
contradicts lower-dimensional nonvanishing. No graph or new helper admission is
assumed in this step; coordinate permutations extend it to any partial entry. -/
theorem lebl_first_partial_zero_at_singular {n : ℕ} (_hn : 0 < n)
    (ih : ∀ {V : Set (Fin n → ℂ)}, IsOpen V →
      ∀ {φ : (Fin n → ℂ) → (Fin n → ℂ)}, DifferentiableOn ℂ φ V →
        Set.InjOn φ V → ∀ z ∈ V, LinearMap.det (fderiv ℂ φ z).toLinearMap ≠ 0)
    {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {F : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)}
    (hF : DifferentiableOn ℂ F U) (hinj : Set.InjOn F U)
    (p : Fin (n + 1) → ℂ) (hp : p ∈ U)
    (hzero : LinearMap.det (fderiv ℂ F p).toLinearMap = 0) :
    (fderiv ℂ F p) (Pi.single (0 : Fin (n + 1)) 1) 0 = 0 := by
  by_contra hpartial
  obtain ⟨e, V, he, hV, hpV, hVU, hW, hei, hfirst⟩ :=
    lebl_coordinate_replacement_local_inverse hU hF p hp hpartial
  let W := e '' V
  let H := F ∘ e.symm
  have hWt : W ⊆ e.target := fun _ hw ↦ by
    obtain ⟨z, hz, rfl⟩ := hw
    exact e.map_source (hVU hz).2
  have hmaps : MapsTo e.symm W U := fun w hw ↦ (hVU ((hfirst w hw).1)).1
  have hH : DifferentiableOn ℂ H W := hF.comp hei hmaps
  have hinjH : Set.InjOn H W := by
    intro w hw v hv hh
    have h := hinj (hmaps hw) (hmaps hv) hh
    have hh' := congrArg e h
    simpa only [e.right_inv (hWt hw), e.right_inv (hWt hv)] using hh'
  have hHfirst : ∀ w ∈ W, H w 0 = w 0 := fun w hw ↦ (hfirst w hw).2
  have hpW : e p ∈ W := ⟨p, hpV, rfl⟩
  obtain ⟨hS, hpS, hφ, hinjφ, hdet⟩ := lebl_reduced_slice hW hH hinjH hHfirst (e p) hpW
  have hne := ih hS hφ hinjφ _ hpS
  apply hne
  rw [hdet]
  have hleft := e.left_inv (hVU hpV).2
  change LinearMap.det (fderiv ℂ (F ∘ e.symm) (e p)).toLinearMap = 0
  rw [fderiv_comp (e p) (by
    rw [hleft]
    exact (hF p hp).differentiableAt (hU.mem_nhds hp))
      ((hei (e p) hpW).differentiableAt (hW.mem_nhds hpW))]
  change LinearMap.det ((fderiv ℂ F (e.symm (e p))).toLinearMap.comp
    (fderiv ℂ e.symm (e p)).toLinearMap) = 0
  rw [LinearMap.det_comp, hleft, hzero, zero_mul]

/-- Permute the original source and target coordinates in Lebl I4. These are
actual continuous complex-linear equivalences; chain rule and determinant
composition preserve singularity. The first-partial contradiction therefore
applies to every original matrix entry. Consequently the WHOLE actual derivative
vanishes at a singular point, conditional only on the same lower-dimensional
induction assertion. This is the source's coordinate-permutation argument. -/
theorem lebl_fderiv_zero_at_singular {n : ℕ} (hn : 0 < n)
    (ih : ∀ {V : Set (Fin n → ℂ)}, IsOpen V →
      ∀ {φ : (Fin n → ℂ) → (Fin n → ℂ)}, DifferentiableOn ℂ φ V →
        Set.InjOn φ V → ∀ z ∈ V, LinearMap.det (fderiv ℂ φ z).toLinearMap ≠ 0)
    {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {F : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)}
    (hF : DifferentiableOn ℂ F U) (hinj : Set.InjOn F U)
    (p : Fin (n + 1) → ℂ) (hp : p ∈ U)
    (hzero : LinearMap.det (fderiv ℂ F p).toLinearMap = 0) : fderiv ℂ F p = 0 := by
  classical
  have hentry (i j : Fin (n + 1)) : (fderiv ℂ F p) (Pi.single j 1) i = 0 := by
    let a : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
      (LinearEquiv.piCongrLeft' ℂ (fun _ : Fin (n + 1) ↦ ℂ)
        (Equiv.swap 0 j)).toContinuousLinearEquiv
    let b : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
      (LinearEquiv.piCongrLeft' ℂ (fun _ : Fin (n + 1) ↦ ℂ)
        (Equiv.swap 0 i)).toContinuousLinearEquiv
    let V := a ⁻¹' U
    let H := b ∘ F ∘ a
    let q := a.symm p
    have hV : IsOpen V := hU.preimage a.continuous
    have hq : q ∈ V := by simpa [q, V] using hp
    have hH : DifferentiableOn ℂ H V := by
      intro z hz
      exact (b.differentiableAt.comp z
        (((hF _ hz).differentiableAt (hU.mem_nhds hz)).comp z a.differentiableAt))
          |>.differentiableWithinAt
    have hinjH : Set.InjOn H V := by
      intro z hz w hw hh
      exact a.injective (hinj hz hw (b.injective hh))
    have hd : fderiv ℂ H q = b.toContinuousLinearMap.comp
        ((fderiv ℂ F p).comp a.toContinuousLinearMap) := by
      have hf : HasFDerivAt F (fderiv ℂ F p) (a q) := by
        simpa [q] using ((hF p hp).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
      exact (b.hasFDerivAt.comp q (hf.comp q a.hasFDerivAt)).fderiv
    have hz : LinearMap.det (fderiv ℂ H q).toLinearMap = 0 := by
      rw [hd]
      change LinearMap.det (b.toLinearEquiv.toLinearMap.comp
        ((fderiv ℂ F p).toLinearMap.comp a.toLinearEquiv.toLinearMap)) = 0
      rw [LinearMap.det_comp, LinearMap.det_comp, hzero, zero_mul, mul_zero]
    have h := lebl_first_partial_zero_at_singular hn ih hV hH hinjH q hq hz
    rw [hd] at h
    change b ((fderiv ℂ F p) (a (Pi.single (0 : Fin (n + 1)) 1))) 0 = 0 at h
    have ha : a (Pi.single (0 : Fin (n + 1)) 1) = Pi.single j 1 := by
      ext k
      change (Pi.single (0 : Fin (n + 1)) (1 : ℂ) : Fin (n + 1) → ℂ)
        ((Equiv.swap 0 j).symm k) = (Pi.single j (1 : ℂ) : Fin (n + 1) → ℂ) k
      by_cases hk : k = 0
      · subst k
        simp [Pi.single_apply, eq_comm]
      · by_cases hkj : k = j
        · subst k
          simp [Pi.single_apply]
        · simp [Equiv.swap_apply_of_ne_of_ne hk hkj, hk, hkj]
    have hb (z : Fin (n + 1) → ℂ) : b z 0 = z i := by
      change z ((Equiv.swap 0 i).symm 0) = z i
      simp
    rw [ha, hb] at h
    exact h
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℂ (Fin (n + 1))).ext
  intro j
  ext i
  simpa using hentry i j

/-- Lebl I6's contradiction on any nonempty original open parameter domain:
a holomorphic injection cannot have derivative zero everywhere. Restrict to
an actual positive-radius ball inside the domain. Mathlib's real mean-value
theorem makes the SAME map constant on that convex ball. Original injectivity
would make the ball a singleton neighborhood, impossible in positive complex
dimension. No connectedness of the whole domain is imposed. -/
theorem lebl_no_open_injection_with_zero_derivative {n m : ℕ} (hn : 0 < n)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    {F : (Fin n → ℂ) → (Fin m → ℂ)}
    (hF : DifferentiableOn ℂ F U) (hinj : Set.InjOn F U)
    (hzero : ∀ p ∈ U, fderiv ℂ F p = 0) : False := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hp
  have hconst (z : Fin n → ℂ) (hz : z ∈ Metric.ball p r) : F z = F p :=
    Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball p r).isPreconnected
      (hF.mono hball) (fun z hz ↦ hzero z (hball hz)) hz (Metric.mem_ball_self hr)
  have hs : ({p} : Set (Fin n → ℂ)) ∈ 𝓝 p := by
    filter_upwards [Metric.ball_mem_nhds p hr] with z hz
    exact hinj (hball hz) hp (hconst z hz)
  exact not_isOpen_singleton p
    (isOpen_singleton_of_finite_mem_nhds p hs (Set.finite_singleton p))

/-- Lebl's zero-set graph contradiction (I3 and I6), kept on the original
permuted graph instead of changing its carrier. Every original graph point is
singular. The proved I4–I5 kernel makes DF vanish at each such point. Composing
with the actual holomorphic graph and its original coordinate equivalence gives
derivative zero on the nonempty open parameter polydisc. Its first coordinates
make the graph injective, so original F injectivity contradicts I6. This is
equivalent to the source's explicit triangular straightening and uses precisely
the published graph predicate, without requiring a nonzero original gradient. -/
theorem lebl_singular_graph_contradiction {n : ℕ} (hn : 0 < n)
    (ih : ∀ {V : Set (Fin n → ℂ)}, IsOpen V →
      ∀ {φ : (Fin n → ℂ) → (Fin n → ℂ)}, DifferentiableOn ℂ φ V →
        Set.InjOn φ V → ∀ z ∈ V, LinearMap.det (fderiv ℂ φ z).toLinearMap ≠ 0)
    {U : Set (Fin (n + 1) → ℂ)} (hU : IsOpen U)
    {F : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)}
    (hF : DifferentiableOn ℂ F U) (hinj : Set.InjOn F U)
    {p : Fin (n + 1) → ℂ}
    (hgraph : Analysis.leblHolomorphicZeroSetGraphAt U
      (fun z ↦ LinearMap.det (fderiv ℂ F z).toLinearMap) p) : False := by
  classical
  obtain ⟨_, σ, c, r, d, s, g, _hr, _hs, hp, _, hg, hmaps, hUgraph, hzero⟩ := hgraph
  obtain ⟨e, he, hei⟩ := lebl_graph_coordinates_equiv σ
  let A := Analysis.leblCoordinatePolydisc c r
  have hA : IsOpen A := by
    have heq : A = ⋂ i : Fin n, (fun z : Fin n → ℂ ↦ z i) ⁻¹' Metric.ball (c i) (r i) := by
      ext z
      simp [A, Analysis.leblCoordinatePolydisc, Metric.mem_ball, dist_eq_norm]
    rw [heq]
    exact isOpen_iInter_of_finite (fun i ↦ Metric.isOpen_ball.preimage (continuous_apply i))
  let graph := fun y : Fin n → ℂ ↦ e (y, g y)
  have hgraphdiff : DifferentiableOn ℂ graph A :=
    e.differentiable.comp_differentiableOn (differentiableOn_id.prodMk hg)
  have hgraphU : MapsTo graph A U := by
    intro y hy
    rw [show graph y = Analysis.leblUnpermuteGraphCoordinates σ y (g y) from he y (g y)]
    exact hUgraph y hy (g y) (hmaps hy)
  have hgraphzero (y : Fin n → ℂ) (hy : y ∈ A) :
      LinearMap.det (fderiv ℂ F (graph y)).toLinearMap = 0 := by
    rw [show graph y = Analysis.leblUnpermuteGraphCoordinates σ y (g y) from he y (g y)]
    exact (hzero y hy (g y) (hmaps hy)).mpr rfl
  have hdiff : DifferentiableOn ℂ (F ∘ graph) A := hF.comp hgraphdiff hgraphU
  have hif : Set.InjOn (F ∘ graph) A := by
    intro y hy z hz h
    have heq := hinj (hgraphU hy) (hgraphU hz) h
    exact congrArg Prod.fst (e.injective heq)
  have hz : ∀ y ∈ A, fderiv ℂ (F ∘ graph) y = 0 := by
    intro y hy
    rw [fderiv_comp y ((hF _ (hgraphU hy)).differentiableAt (hU.mem_nhds (hgraphU hy)))
      ((hgraphdiff y hy).differentiableAt (hA.mem_nhds hy)),
      lebl_fderiv_zero_at_singular hn ih hU hF hinj _ (hgraphU hy) (hgraphzero y hy)]
    simp
  exact lebl_no_open_injection_with_zero_derivative hn hA ⟨_, hp⟩ hdiff hif hz

/-- Lebl Theorem 1.6.5's actual dimension induction (I2–I6). The scalar base
uses the original-source scalar inverse provider. In dimension n+1, the reduced
slice/coordinate-replacement contradiction and actual coordinate permutations
make DF zero at every singular point, conditional on the induction assertion
in dimension n. Work on an actual connected ball inside U. If its Jacobian is
identically zero, the whole original map has zero derivative there, contradicting
injectivity by the mean-value argument. Otherwise apply the published dense
regular-zero-set theorem to its actual holomorphic Jacobian, obtain a graph point
in the nonempty zero set, and apply the proved original-graph contradiction.
Thus every marked original Jacobian is nonzero. This follows Lebl's printed
induction with the graph kept in original coordinates, avoiding an unnecessary
carrier replacement. Lower named source-provider admissions remain exposed. -/
theorem lebl_jacobian_ne_zero {n : ℕ} (hn : 0 < n)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {F : (Fin n → ℂ) → (Fin n → ℂ)}
    (hF : DifferentiableOn ℂ F U) (hinj : Set.InjOn F U) :
    ∀ p ∈ U, LinearMap.det (fderiv ℂ F p).toLinearMap ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ m =>
      by_cases hm : m = 0
      · subst m
        exact lebl_jacobian_ne_zero_dimension_one hU hF hinj
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have ih' : ∀ {V : Set (Fin m → ℂ)}, IsOpen V →
            ∀ {φ : (Fin m → ℂ) → (Fin m → ℂ)}, DifferentiableOn ℂ φ V →
              Set.InjOn φ V → ∀ z ∈ V, LinearMap.det (fderiv ℂ φ z).toLinearMap ≠ 0 := by
          intro V hV φ hφ hiφ
          exact ih m (Nat.lt_succ_self m) hmpos hV hφ hiφ
        intro p hp hzero
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hp
        let V := Metric.ball p r
        have hpV : p ∈ V := Metric.mem_ball_self hr
        have hV : IsOpen V := Metric.isOpen_ball
        have hFc : DifferentiableOn ℂ F V := hF.mono hball
        have hinjc : Set.InjOn F V := hinj.mono hball
        let J := fun z ↦ LinearMap.det (fderiv ℂ F z).toLinearMap
        have hJ : DifferentiableOn ℂ J V :=
          (lebl_jacobian_differentiableOn hn hU hF).mono hball
        by_cases hnonzero : ∃ z ∈ V, J z ≠ 0
        · have hconn : IsConnected V := (convex_ball p r).isConnected ⟨p, hpV⟩
          have hregular := Analysis.lebl_holomorphic_hypersurface_regular_points_g9
            m hV hconn hJ hnonzero
          have : Nonempty (Analysis.leblHolomorphicZeroSet V J) := ⟨⟨p, hpV, hzero⟩⟩
          obtain ⟨q, hq⟩ := hregular.2.nonempty
          exact lebl_singular_graph_contradiction hmpos ih' hV hFc hinjc hq
        · push Not at hnonzero
          have hDF : ∀ z ∈ V, fderiv ℂ F z = 0 := fun z hz ↦
            lebl_fderiv_zero_at_singular hmpos ih' hV hFc hinjc z hz (hnonzero z hz)
          exact lebl_no_open_injection_with_zero_derivative hn hV ⟨p, hpV⟩ hFc hinjc hDF

/--
An injective holomorphic map on an open subset of ℂⁿ, for n > 0, has nonzero complex Jacobian
everywhere and a holomorphic inverse on its open image. This also gives the bijective-open-set
specialization by identifying the specified target with the image. Neither the domain nor its
image is assumed connected.

Source: Lebl, Tasty Bits of Several Complex Variables, version 3.4 (December 23, 2020), Theorem
1.6.5, printed pp.37–38.

Natural-language proof:

I1. Work locally on connected polydiscs contained in U, so disconnected U causes no issue.
Identify the finite-dimensional source and output with Fin n→C, using the fixed complex-linear
coordinate identifications and their finite-product norms. For each output index i apply
analysis.lebl_polydisc_holomorphic_coordinate_derivatives_g1 with d=n≥1, the SAME open U, and
scalar f_i=π_i∘F. A continuous complex-linear projection preserves holomorphy; the chain rule
identifies P_j(f_i)(z) with the i-th coordinate of DF(z)e_j, hence with the (i,j) Jacobian entry.
The supplier proves all these first coordinate derivatives holomorphic on U, and more generally
its deterministic derivatives obey the factorial coefficient identity α!c_α=D^αf_i(a) on each
closed polydisc contained in U. Its α=0 conclusion gives complex ContDiffOn infinity of each f_i
on the SAME U. The finite-output contDiffOn_pi theorem therefore gives ContDiffOn infinity of the
literal F on U, not merely a collection of unrelated point germs. The finite Leibniz formula
J(z)=sum_σ sign(σ) product_i P_(σ(i))(f_i)(z) proves J=det_C DF holomorphic: differentiate each
finite product by the product rule and add the finitely many derivatives. The determinant matrix
identification is the existing exact leaf. No termwise differentiation of a new series is used. At
every point of U, its openness supplies the neighborhood premise for ContDiffOn.contDiffAt;
downgrade the available order to1 for the inverse-function steps.

I2. For n=1 restrict to any connected open disk D about the point in U. An injective holomorphic
scalar map is nonconstant on D. Its holomorphic-to-analytic and open-mapping providers show F(D)
is open. The continuous injective open map D→F(D) is a homeomorphism: the inverse exists by
injectivity and image-surjectivity, and for every open A⊂D the preimage of A under this inverse is
F(A), which is open by the open-map provider. Thus inverse continuity is proved before applying
the scalar inverse theorem. The existing Riemann-surface holomorphic-homeomorphism theorem now
proves its coordinate derivative is nonzero. Both D and F(D) carry their standard complex curve
structures. This application is only one-dimensional; it is not used as a several-variable inverse
theorem.

I3. Inductively assume the assertion det≠0 for every injective holomorphic map on an open subset
of C^(n−1), where n>1. Suppose J vanishes somewhere, and choose a connected polydisc neighborhood
of such a point. If J is not identically zero on that neighborhood, the regular-zero-set core
supplies a point q of {J=0} and, after a coordinate permutation, a graph z_n=g(z′) for its zero
set near q. Translate q and F(q) to zero. The triangular coordinate change
Ψ(z′,z_n)=(z′,z_n−g(z′)) has the explicit holomorphic inverse (w′,w_n)↦(w′,w_n+g(w′)); it carries
the graph to w_n=0. Replace F by F∘Ψ⁻¹ on the actual open image of this chart. Its derivative
determinant is still zero on w_n=0 by the chain rule and determinant composition. If J is
identically zero on the chosen neighborhood, omit Ψ and translate only. In both cases we have an
injective holomorphic map on a neighborhood of0 whose derivative determinant vanishes on the local
hyperplane z_n=0.

I4. We show every tangential partial derivative ∂F_i/∂z_j, j<n, vanishes at every point of a small
polydisc in the hyperplane z_n=0. Suppose one were nonzero at p in that hyperplane. Translate p
and F(p) to0 while preserving z_n=0, and permute only the first n−1 source coordinates and the
target components, so ∂F_1/∂z_1(0)≠0. Define the literal G(z)=(F_1(z),z_2,…,z_n). Apply I1 on its
actual open domain: G is complex C1 there and det DG is holomorphic, hence continuous. Its
triangular matrix has determinant ∂F_1/∂z_1(0)≠0 at0. This derivative is a continuous
complex-linear equivalence in finite dimensions. Use ContDiffOn.contDiffAt at0, then the complex
local inverse constructor at FINITE order1 and its center-membership theorem, with the HasFDerivAt
of this same total G. It gives e whose forward function is literally G, with0∈e.source and the two
inverse equations on its open source and target. The finite-C1 neighborhood primitive gives a
neighborhood A of0 on which this same G is ContDiffOn C1. By continuity of det DG, choose an open
V about0 inside A, the original domain and e.source, where det DG never vanishes. The restriction
e:V→G(V) is a homeomorphism and G(V) is open, because V is open in the source of e. For EVERY
b∈G(V), a=e.symm(b) belongs to V by the inverse equations. The C1-on-A hypothesis, restricted to
the open V, gives ContDiffAt C1 G at a; differentiability gives its actual HasFDerivAt DG(a), and
the nonzero determinant makes that derivative a continuous complex-linear equivalence. Apply
OpenPartialHomeomorph.contDiffAt_symm to the original e at this b∈e.target, with this derivative
and order1. It proves C1 of the SAME e.symm at b, and ContDiffAt.differentiableAt at nonzero
order1 gives complex differentiability there. Thus the inverse is holomorphic throughout G(V). All
later compositions are restricted to this actual open target. No common C-infinity neighborhood is
inferred from pointwise C-infinity. G preserves the last coordinate z_n and fixes0.

I5. On an open polydisc about0 contained in G’s target, H=F∘G⁻¹ has the form H(w)=(w_1,h(w)),
where h takes values in C^(n−1). Set φ(w_2,…,w_n)=h(0,w_2,…,w_n) on the open slice polydisc in
C^(n−1). It is holomorphic and injective: equality of its values makes the two H-values equal,
then injectivity of F and G⁻¹ forces equality of the slice points. The induction hypothesis yields
det Dφ(0)≠0. But the first row of DH is (1,0,…,0), so expansion by that row gives det DH(0)=det
Dφ(0). The chain rule and determinant composition give det DH(0)=det DF(0) det D(G⁻¹)(0)=0. This
contradiction proves the tangential derivative in I4 could not be nonzero.

I6. All tangential derivatives therefore vanish on a connected polydisc of the hyperplane z_n=0.
Fix every variable but one among z_1,…,z_(n−1). On its convex complex disc the derivative of each
scalar component is zero; integrating along a straight segment, or applying the real fundamental
theorem of calculus to that segment, makes the component constant in that coordinate. Changing
coordinates one at a time makes F(z′,0) constant throughout the polydisc. Since n>1 this polydisc
has two distinct points, contradicting injectivity. Thus J has no zero. This completes induction
on n without presuming nonvanishing of the original Jacobian.

I7. At each z∈U, det DF(z)≠0 makes the actual DF(z) a complex-linear equivalence; in finite
dimensions it and its inverse are continuous. I1 gives complex C1 of the literal F on the SAME
open U, hence C1 at z by ContDiffOn.contDiffAt. Apply the complex local-inverse constructor at
order1 to this F and DF(z), and its center-membership theorem, obtaining e with forward function
literally F and z∈e.source. The finite-order neighborhood primitive also supplies a neighborhood A
of z on which this same F is ContDiffOn C1. Choose an open V about z inside A∩U∩e.source. Its
image F(V) is open by the homeomorphism e on its open source. For every b∈F(V), a=e.symm(b) lies
in V, so F is C1 at a and has its actual complex derivative DF(a). That derivative is a continuous
complex-linear equivalence because its determinant is nonzero throughout U, as already proved by
induction. At each such b apply the inverse-regularity leaf to THIS e, b∈e.target, its actual
source point a, derivative equivalence DF(a), and order1. Nonzero-order differentiability
conversion makes the same e.symm holomorphic at every b∈F(V). No infinity-order neighborhood claim
occurs. The union of these open image neighborhoods is F(U), hence F(U) is open. By injectivity
and the local inverse equations, the local holomorphic inverse agrees there with the literal
set-theoretic inverse of F:U→F(U). Therefore that global inverse is holomorphic throughout F(U).
If F maps bijectively onto a specified open V0, its image is V0 and this is the literal inverse.

-/
theorem lebl_injective_holomorphic_biholomorphism
    {n : ℕ} (hn : 0 < n) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {F : (Fin n → ℂ) → (Fin n → ℂ)}
    (hF : DifferentiableOn ℂ F U) (hFinj : Set.InjOn F U) :
    (∀ z ∈ U, LinearMap.det (fderiv ℂ F z).toLinearMap ≠ 0) ∧
      IsOpen (F '' U) ∧
      ∃ G : (Fin n → ℂ) → (Fin n → ℂ),
        DifferentiableOn ℂ G (F '' U) ∧
          (∀ z ∈ U, G (F z) = z) ∧
          (∀ w ∈ F '' U, G w ∈ U ∧ F (G w) = w) := by
  have hdet := lebl_jacobian_ne_zero hn hU hF hFinj
  exact ⟨hdet, lebl_inverse_of_nonzero_jacobian hU
    ((lebl_vector_contDiffOn hn hU hF).of_le (by simp)) hFinj hdet⟩


end HolomorphicAnosov
