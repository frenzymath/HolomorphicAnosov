import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import HolomorphicAnosov.Topology.Homology.ModTwoSupportRestrictionComparison

/-!
# Mod-two compact-support Mayer–Vietoris prerequisite

This public interface is the coefficient-`ZMod 2` form of Hatcher's
compact-support Mayer–Vietoris sequence (Algebraic Topology, pp.152–153 and
Lemma 3.27, step (1), p.237).  It is separated from the section-realization
theorem because the existing project sequence is fixed to `ModuleCat ℤ`.

DAG node: `topo.mod_two_support_mayer_vietoris_g18`.
-/

noncomputable section

open CategoryTheory
open HolomorphicAnosov.Topology _root_.Topology HolomorphicAnosov.Topology.Homology

namespace HolomorphicAnosov.HatcherCompactSupport

universe u

/-- The signed restriction map from a union support to its two pieces. -/
def modTwoSupportMVPhi (M : Type u) [TopologicalSpace M]
    (A B : Set M) (k : ℕ) :
    SupportHomology (A ∪ B) k →ₗ[ZMod 2]
      SupportHomology A k × SupportHomology B k :=
  (supportRestriction (M := M) (A := A ∪ B) (B := A)
      Set.subset_union_left k).prod
    (-(supportRestriction (M := M) (A := A ∪ B) (B := B)
      Set.subset_union_right k))

/-- The intersection restriction sum map from the two pieces. -/
def modTwoSupportMVPsi (M : Type u) [TopologicalSpace M]
    (A B : Set M) (k : ℕ) :
    SupportHomology A k × SupportHomology B k →ₗ[ZMod 2]
      SupportHomology (A ∩ B) k :=
  (supportRestriction (M := M) (A := A) (B := A ∩ B)
      Set.inter_subset_left k).coprod
    (supportRestriction (M := M) (A := B) (B := A ∩ B)
      Set.inter_subset_right k)

/-- The compact-support Mayer–Vietoris sequence with coefficients in `ZMod 2`.

Source: Hatcher, *Algebraic Topology*, relative Mayer–Vietoris pp.152–153,
coefficient groups p.153, and Lemma 3.27 step (1), p.237.

Complete natural-language proof. Put U=M\A and V=M\B. Hausdorffness
and compactness make U and V open. Work throughout over ZMod 2. In the
ambient singular chain complex C=C_*(M), let E=C_*(U) and F=C_*(V).
The subcomplex intersection E∩F is C_*(U∩V): degreewise each is the direct
sum of coefficient copies indexed by the simplices supported in its set.
Thus the signed diagonal and sum induce a short exact sequence
0 → C/(E∩F) → C/E ⊕ C/F → C/(E+F) → 0.
Indeed the diagonal kernel is E∩F. If representatives a,b have a+b=e+f
with e∈E,f∈F, then c=a-e=f-b represents a in C/E and -b in C/F,
proving exactness in the middle. Every last quotient class is the image
of (c,0), proving surjectivity. These maps commute with the differential.

The inclusion E+F → C_*(U∪V) induces a homology isomorphism by the
small-chain theorem for the open cover U,V of U∪V. More explicitly,
barycentric subdivision makes each simplex small after sufficiently many
iterations, and the subdivision homotopy stays within each simplex image.
The resulting small-chain inclusion is a chain homotopy equivalence.
Compare the short exact sequences with first terms E+F and C_*(U∪V),
common middle term C, and quotient last terms. Their homology sequences
and the five lemma show that C/(E+F) → C/C_*(U∪V) induces homology
isomorphisms. Degree zero uses the terminal zero in each exact sequence.

The four quotients are therefore the support groups for A∪B, A, B,
and A∩B, respectively. Apply the long homology sequence to the displayed
short exact sequence and use this comparison for its last term. The first
map is precisely the signed pair of support restrictions, and the second
is their sum; this follows directly on every relative chain representative.
The connecting maps give δ. The three consecutive exactness assertions
and terminal degree-zero surjectivity follow. Empty supports satisfy the
same quotient calculation; no positive-dimensional assumption is used.

The Lean proof applies the integer-module MV sequence with the underlying integer module
of the lifted mod-two coefficient module. The public relative homology comparison identifies
its groups with these mod-two groups; restriction naturality identifies both displayed maps.
Conjugating the connecting maps then transports exactness and degree-zero surjectivity.
-/

theorem modTwo_compact_support_mayer_vietoris
    (M : Type u) [TopologicalSpace M] [T2Space M] (A B : Set M)
    (hA : IsCompact A) (hB : IsCompact B) :
    ∃ δ : ∀ k : ℕ,
        SupportHomology (A ∩ B) (k + 1) →+
          SupportHomology (A ∪ B) k,
      (∀ k : ℕ,
        Function.Exact (δ k) (modTwoSupportMVPhi M A B k) ∧
        Function.Exact (modTwoSupportMVPhi M A B k)
          (modTwoSupportMVPsi M A B k) ∧
        Function.Exact (modTwoSupportMVPsi M A B (k + 1)) (δ k)) ∧
      Function.Surjective (modTwoSupportMVPsi M A B 0) := by
  let f := Int.castRingHom (ZMod 2)
  let F := ModuleCat.restrictScalars.{u} f
  let V := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  let W := F.obj V
  let D : CompactSupportMVData.{u} :=
    { space := TopCat.of M, hausdorff := inferInstance, left := A, right := B,
      compact_left := hA, compact_right := hB, coefficients := W }
  let e (K : Set M) (k : ℕ) : SupportHomology K k ≃+
      supportSingularHomology (TopCat.of M) K W k :=
    (ssetPairRestrictScalarsHomologyIso f
      (supportSingularPair (TopCat.of M) K) V k).toLinearEquiv.toAddEquiv
  obtain ⟨δ, hseq, _hNat⟩ := hatcher_compact_support_mayer_vietoris
  obtain ⟨hExact, hSurj⟩ := hseq D
  let d (k : ℕ) : SupportHomology (A ∩ B) (k + 1) →+ SupportHomology (A ∪ B) k :=
    (e (A ∪ B) k).symm.toAddMonoidHom.comp
      ((δ D k).comp (e (A ∩ B) (k + 1)).toAddMonoidHom)
  let em (k : ℕ) := (e A k).prodCongr (e B k)
  have hphi (k : ℕ) :
      (supportMayerVietorisPhi D.space W A B k).comp (e (A ∪ B) k).toAddMonoidHom =
      (em k).toAddMonoidHom.comp (modTwoSupportMVPhi M A B k).toAddMonoidHom := by
    ext x
    · exact (modTwoSupportRestriction_comparison M (A ∪ B) A Set.subset_union_left k x).symm
    · change -(supportSingularHomologyRestrict D.space W Set.subset_union_right k)
          ((e (A ∪ B) k) x) = (e B k) (-(supportRestriction Set.subset_union_right k) x)
      rw [map_neg]
      exact congrArg Neg.neg
        (modTwoSupportRestriction_comparison M (A ∪ B) B Set.subset_union_right k x).symm
  have hpsi (k : ℕ) :
      (supportMayerVietorisPsi D.space W A B k).comp (em k).toAddMonoidHom =
      (e (A ∩ B) k).toAddMonoidHom.comp (modTwoSupportMVPsi M A B k).toAddMonoidHom := by
    ext x
    change (supportSingularHomologyRestrict D.space W Set.inter_subset_left k) ((e A k) x.1) +
      (supportSingularHomologyRestrict D.space W Set.inter_subset_right k) ((e B k) x.2) =
      (e (A ∩ B) k) ((supportRestriction Set.inter_subset_left k) x.1 +
        (supportRestriction Set.inter_subset_right k) x.2)
    rw [map_add]
    exact congrArg₂ (· + ·)
      (modTwoSupportRestriction_comparison M A (A ∩ B) Set.inter_subset_left k x.1).symm
      (modTwoSupportRestriction_comparison M B (A ∩ B) Set.inter_subset_right k x.2).symm
  have hd (k : ℕ) : (δ D k).comp (e (A ∩ B) (k + 1)).toAddMonoidHom =
      (e (A ∪ B) k).toAddMonoidHom.comp (d k) := by
    ext x
    simp [d]
  refine ⟨d, ?_, ?_⟩
  · intro k
    refine ⟨?_, ?_, ?_⟩
    · exact (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
        (d k) (modTwoSupportMVPhi M A B k).toAddMonoidHom
        (δ D k) (supportMayerVietorisPhi D.space W A B k)
        (e (A ∩ B) (k + 1)).toAddMonoidHom (e (A ∪ B) k).toAddMonoidHom
        (em k).toAddMonoidHom (hd k) (hphi k)
        (e _ _).surjective (e _ _).bijective (em k).injective).mpr (hExact k).1
    · exact (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
        (modTwoSupportMVPhi M A B k).toAddMonoidHom
        (modTwoSupportMVPsi M A B k).toAddMonoidHom
        (supportMayerVietorisPhi D.space W A B k) (supportMayerVietorisPsi D.space W A B k)
        (e (A ∪ B) k).toAddMonoidHom (em k).toAddMonoidHom (e (A ∩ B) k).toAddMonoidHom
        (hphi k) (hpsi k) (e _ _).surjective (em k).bijective
        (e _ _).injective).mpr (hExact k).2.1
    · exact (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
        (modTwoSupportMVPsi M A B (k + 1)).toAddMonoidHom (d k)
        (supportMayerVietorisPsi D.space W A B (k + 1)) (δ D k)
        (em (k + 1)).toAddMonoidHom (e (A ∩ B) (k + 1)).toAddMonoidHom
        (e (A ∪ B) k).toAddMonoidHom (hpsi (k + 1)) (hd k)
        (em _).surjective (e _ _).bijective (e _ _).injective).mpr (hExact k).2.2
  · intro x
    obtain ⟨y, hy⟩ := hSurj (e (A ∩ B) 0 x)
    refine ⟨(em 0).symm y, (e (A ∩ B) 0).injective ?_⟩
    have hx := DFunLike.congr_fun (hpsi 0) ((em 0).symm y)
    exact hx.symm.trans (by simpa using hy)

end HolomorphicAnosov.HatcherCompactSupport


