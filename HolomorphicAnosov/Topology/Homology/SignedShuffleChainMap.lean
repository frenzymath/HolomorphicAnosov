import HolomorphicAnosov.Topology.Homology.SignedShufflePositiveBoundary

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

namespace HolomorphicAnosov.SignedShuffle

universe u

/-- The prescribed shuffle is natural, is a chain map for the signed tensor-total
boundary, and has the point-insertion initialization in every zero-degree row.

Sources: Hatcher, Algebraic Topology, §3.B printed pp.277–278 (literature/hatcher-at.pdf/.txt), for the exact monotone-grid formula; Eilenberg–Mac Lane, On the Groups H(Π,n), I, Annals of Mathematics 58(1) (1953), 55–106, supplied original literature/On the Groups H(Π, n), I (Samuel Eilenberg and Saunders Mac Lane) (z-library.sk, 1lib.sk, z-lib.sk).pdf and extracted literature/G2-EM1953-full-supplied.txt: §2 pp.56–58, §3 pp.58–60, §5 pp.63–68, especially Theorem5.1/recurrences (5.7),(5.7a) p.65 and the written Theorem5.2 boundary proof (5.8),(5.11),(5.12) pp.66–67. Printed p.66 is PDF page13. The proof is on unnormalized FD-complexes; normalized products begin only at (5.15) p.67. No Eilenberg–Zilber equivalence is used.

Complete natural-language proof:

S1: Hatcher labels the simplex vertices and defines ℓ_λ affinely from the ordered grid vertices. Since both target simplices are convex, ℓ_λ has values in their product and is continuous. There are finitely many monotone paths, so the displayed signed sum defines a finite singular chain and extends Q-bilinearly. Postcomposition with f×g commutes term by term with this formula, proving naturality. When p=0 or q=0 there is a unique path and I(λ)=0; its map is the identity in the nonpoint coordinate, yielding the specified point initialization.

S2: Use the actual singular-simplex continuous-map model and alternating face boundary. Let K_n and L_n be the free abelian groups on all singular n-simplices of X and Y, including degenerates. The faces F_i precompose with the affine vertex-deletion map; D_i precomposes with the affine map merging barycentric coordinates i and i+1. These give the FD-complexes S(X), S(Y) of EM §2 pp.56–58. The existing ModuleCat.FreeMonoidal.μIso at R=Z identifies the degreewise, diagonal product K_n⊗Z L_n with the free module on pairs of singular n-simplices. Its forward/inverse generator formulas, followed by the continuous-map product/coordinate-projection bijection, identify it with the free abelian group on singular n-simplices of X×Y: a pair (a,b) maps to t↦(a(t),b(t)); coordinate projections give its inverse. This is not the tensor-total complex ⊕_{p+q=n}K_p⊗L_q. Its F_i and D_i act on both coordinates, exactly (5.1) p.63. For horizontal slots μ_1<⋯<μ_p and complementary vertical slots ν_1<⋯<ν_q in {0,…,p+q−1}, the term (D_{ν_q}⋯D_{ν_1}a)×(D_{μ_p}⋯D_{μ_1}b) has affine coordinate maps sending vertex k to the numbers of horizontal and vertical steps before k. Hence it equals (a×b)∘ℓ_λ. EM pp.63–64 explicitly makes this geometric identification. Exactly μ_i−(i−1) vertical slots precede horizontal slot μ_i, so ε(μ)=Σ_i(μ_i−(i−1)) is I(λ), with no degree-dependent sign correction. Thus EM product ∇ in (5.3) is precisely the integral version of sh.

S3: Record the derived-operator mechanism written in EM §3 pp.58–60. Precomposition of affine simplex maps is functorial. Therefore the elementary monotone vertex maps satisfy F_iF_j=F_{j−1}F_i for i<j; D_iD_j=D_{j+1}D_i for i≤j; and F_iD_j=D_{j−1}F_i for i<j, identity for i=j or j+1, D_jF_{i−1} for i>j+1. These are (2.3)–(2.5), before normalization. Set δ=∂*=F_1−F_2+⋯+(−1)^{n−1}F_n on degree n≥1 and δ=0 on degree0; set F_0=0 on degree0. Then ∂=F_0−δ. A derived operator raises each F_i,D_i and source/target degree by one, equivalently replaces a monotone map β by β′ with β′(0)=0 and β′(j+1)=β(j)+1. EM Theorem3.1 proves coefficient identities can be checked on the free monotone-map model: the value on its identity generator determines a natural operator, because every chain c is the image of that generator under β↦β*c. Distinct monotone maps form its free basis. In detail, the free model K(r) has basis all monotone γ:[m]→[r] in degree m and basic generator u_r=id:[r]→[r]. For M:K_r→K_s natural in K, write M_{K(r)}(u_r)=Σ_β n_β[β] uniquely, with finitely many nonzero integers. For every c∈K_r, X_c([γ])=γ*c is an FD-map because precomposition composes; it sends u_r to c. Naturality gives M_K(c)=X_c(M_{K(r)}u_r)=Σ_β n_ββ*c. Evaluation on K(r),u_r also proves uniqueness. For a natural bilinear operation K_r×L_t→K_s⊗L_s, evaluate instead on the paired models K(r),K(t) and u_r⊗u_t: the result has the unique finite basis expression Σ_{β,γ}n_{β,γ}[β]⊗[γ]. The two FD-maps X_c,X_d then give Σ n_{β,γ}(β*c)⊗(γ*d) for arbitrary c,d. The model tensor has exactly this paired free basis by the existing free-tensor isomorphism. The map β↦β′ is injective, since β(i)=β′(i+1)−1, and (βγ)′=β′γ′ by checking 0 and j+1 separately. Therefore replacing each basis operator by its primed operator preserves zero coefficient identities, sums and compositions, and does so in each independent variable for the paired coefficients. This proves the identity transport (3.5) used below rather than assuming a general representation theorem without its model proof. In particular ∂′ on degree n≥2 is δ, while ∂′ on degree1 is ZERO, not δ=F_1. The FD rules give F_0M′=MF_0 and D_0M=M′D_0 for frontal M, and δD_0 c=c−D_0δc for positive-degree c, (3.7)–(3.11). For the last identity the i=1 term is c, and each remaining i≥2 term is D_0F_{i−1}c with the opposite alternating sign.

S4: Follow the shuffle recursion proved on EM p.65. Define a∇′b for input degrees p,q>0 by the shuffle formula for degrees p−1,q−1 with every degeneracy subscript raised by one, (5.3′). Partition the (p,q)-shuffles according to which slot is zero. If μ_1=0, remove it and subtract one from all other slots; this bijects to (p−1,q)-shuffles and preserves ε. Its sum is a∇′D_0b. If ν_1=0, remove it and subtract one; each of the p horizontal slots loses one preceding vertical step, so the sign contributes (−1)^p. Its sum is (−1)^p D_0a∇′b. Consequently a∇b=a∇′D_0b+(−1)^p D_0a∇′b for p,q>0, (5.7). The unique-shuffle formulas a_p∇b_0=a_p×D_{p−1}⋯D_0b_0 and a_0∇b_q=D_{q−1}⋯D_0a_0×b_q give (5.7a); a_0∇b_0=a_0×b_0. Applying F_0 to a derived shuffle term lowers all its positive degeneracy indices: F_0(a∇′b)=F_0a∇F_0b, (5.6). Apply this to the recursion, using F_0D_0=id. It yields F_0(a∇b)=F_0a∇b+(−1)^p a∇F_0b for positive p,q, and the unique-shuffle formulas prove the same identity when a degree is zero. At (0,0) both sides vanish because their output degree is −1. This is exactly (5.12), with degree-zero F_0 interpreted as zero. Whenever F_0 is applied to a degree-zero input, its term on the right is omitted as zero rather than forming a product with a negative-degree input.

S5: Supply the finite base calculations explicitly requested in EM Theorem5.2 pp.66–67. If p=0, every face of D_{q−1}⋯D_0a_0 is the same repeated vertex in one lower degree. Thus applying δ to a_0∇b_q gives a_0∇δb_q term by term. If q=0 the identical argument in the other coordinate gives δ(a_p∇b_0)=δa_p∇b_0; p=q=0 is zero. Combining with S4 proves the full boundary rule for these degrees; derive its p=0 identity to get ∂′(a_1∇′b)=a_1∇′∂′b for b of degree at least2, (5.13). For b of degree1 its derived boundary equation is 0=0; omit the term whose boundary has degree0, since ∇′ is defined only on positive input degrees. For p=q=1, (5.4) is a∇b=D_1a×D_0b−D_0a×D_1b. F_1 of the two summands is a×b and cancels, whereas their F_2 values are a×D_0F_1b and D_0F_1a×b. Therefore δ(a∇b)=D_0F_1a×b−a×D_0F_1b=(δa)∇b−a∇δb. For p=1,q>1, induct on q: the boundary rule at (1,q−1) derives to ∂′(A_2∇′B_q)=∂′A_2∇′B_q−A_2∇′∂′B_q, (5.14). Using S4, (5.13), (5.14), and δD_0=id−D_0δ, the expansion is δ(a_1∇b_q)=a_1∇′(b_q−D_0δb_q)−(a_1−D_0δa_1)∇′b_q+D_0a_1∇′δb_q=D_0δa_1∇′b_q−a_1∇′D_0δb_q+D_0a_1∇′δb_q=(δa_1)∇b_q−a_1∇δb_q. The first equality uses ∂′ only at output/input degrees where it equals δ; (5.13) has zero ∂′a_1, never δa_1=0. For q=1,p>1, induct on p, starting with the (1,1) calculation. The already proved rule at (p−1,1) derives to the rule on a_p∇′D_0b_1. Deriving the q=0 rule gives the one-sided identity ∂′(A_r∇′b_1)=∂′A_r∇′b_1 for r≥2, with ∂′b_1=0 (at r=1 the equation is 0=0); there is no derived product with a degree-zero boundary input. Put e=(−1)^p. The recursion then expands to δ(a_p∇b_1)=δa_p∇′D_0b_1−e a_p∇′(b_1−D_0F_1b_1)+e(a_p−D_0δa_p)∇′b_1. Cancel −e a_p∇′b_1 with +e a_p∇′b_1, and use (5.7) on (δa_p,b_1) and (5.7a) on (a_p,F_1b_1). The remaining terms are (δa_p)∇b_1+e a_p∇F_1b_1. Thus both degree-one rows are accounted for by the source recursion itself; no commutativity theorem or alternative geometric cancellation route is invoked.

S6: Now follow the total-degree induction completing the written proof on EM p.67. For p,q>1 suppose the boundary rule has been proved in every smaller total input degree. Its derived rule for input degrees r,s is ∂′(A_r∇′B_s)=∂′A_r∇′B_s+(−1)^{r−1}A_r∇′∂′B_s, since it derives the rule at (r−1,s−1). For (r,s)=(p,q+1) and (p+1,q), these former totals are p+q−1, so the induction applies. All input degrees are at least2, so their ∂′ equals δ. Write e=(−1)^p and D=D_0. Applying the two derived identities to the recursion gives δ(a∇b)=δa∇′Db−e a∇′(b−Dδb)+e(a−Dδa)∇′b+Da∇′δb. The middle occurrences −e a∇′b and +e a∇′b cancel. The result is δa∇′Db−e Dδa∇′b+e a∇′Dδb+Da∇′δb=(δa)∇b+e a∇δb, by the recursion at (p−1,q) and (p,q−1). This proves (5.11) in the next total degree. Subtract it from the first-face identity S4 using ∂=F_0−δ to obtain ∂(a∇b)=(∂a)∇b+(−1)^p a∇∂b, (5.8), in every degree. The algebra displayed here expands the source’s instruction to expand both sides by (5.7); it is not a different oriented-face proof.

S7: The preceding identities are identities of finite integral chains on the free singular generators. Send each integer coefficient to Q. The existing freeHomEquiv extends each finite generator value linearly, and the existing free-tensor μIso on the two generator sets extends this paired-generator formula Q-bilinearly; equality is determined on the free paired basis. This yields the asserted identity on C_p(X;Q)⊗Q C_q(Y;Q), whose total differential has the factor (−1)^p. It does not identify a Z tensor product with a Q tensor product; coefficient extension of the finite generator identity suffices. S2 identifies every term and sign with the specified ℓ_λ formula, so S6 is precisely the desired singular-chain equation. S1 already proves naturality and point initialization. Degenerate singular simplices were never removed; Theorem5.2 precedes normalized complexes (5.15), Lemma5.3 and Theorem5.4, so no normalization theorem, reduced-chain convention or chain-equivalence theorem is needed. For empty X or Y there are no singular generators and the bilinear domain is zero; all assertions are vacuous. Repeated vertices/degenerate simplices remain valid under the FD identities, and p=0,q=0 were included in S5.

The pure-tensor boundary formula below is precisely the restriction of the total
Koszul differential to its (p,q) summand. Both zero-degree terms are explicitly
omitted before any index transport, so the case p=q=0 states 0=0. TensorProduct.lift
constructs the map on each native tensor component from the displayed bilinear
operation. The finite formula is already data in shuffleGenerator; neither this
statement nor its proof selects a replacement chain map. -/
theorem signedShuffle_chainMap (X Y : TopCat.{u}) :
    (∀ (p q : ℕ) (σ : Simplex X p) (τ : Simplex Y q),
      shuffle X Y p q (generator X σ ⊗ₜ[ℚ] generator Y τ) =
        shuffleGenerator X Y σ τ) ∧
    (∀ (p q : ℕ) (a : Chain X p) (b : Chain Y q),
      boundary (TopCat.of (X × Y)) (p + q) (shuffle X Y p q (a ⊗ₜ[ℚ] b)) =
        firstBoundaryTerm X Y p q a b + (-1 : ℚ) ^ p • secondBoundaryTerm X Y p q a b) ∧
    (∀ (X' Y' : TopCat.{u}) (f : C(X, X')) (g : C(Y, Y'))
      (p q : ℕ) (a : Chain X p) (b : Chain Y q),
      pushforward (f.prodMap g) (p + q) (shuffle X Y p q (a ⊗ₜ[ℚ] b)) =
        shuffle X' Y' p q (pushforward f p a ⊗ₜ[ℚ] pushforward g q b)) ∧
    (∀ (q : ℕ) (x : X) (τ : Simplex Y q),
      shuffle X Y 0 q (generator X (pointSimplex X x) ⊗ₜ[ℚ] generator Y τ) =
        regrade (TopCat.of (X × Y)) (Nat.zero_add q).symm
          (generator (TopCat.of (X × Y)) (insertLeft X Y x τ))) ∧
    (∀ (p : ℕ) (σ : Simplex X p) (y : Y),
      shuffle X Y p 0 (generator X σ ⊗ₜ[ℚ] generator Y (pointSimplex Y y)) =
        regrade (TopCat.of (X × Y)) (Nat.add_zero p).symm
          (generator (TopCat.of (X × Y)) (insertRight X Y σ y))) ∧
    (∀ (x : X) (y : Y),
      shuffle X Y 0 0 (generator X (pointSimplex X x) ⊗ₜ[ℚ]
        generator Y (pointSimplex Y y)) =
          generator (TopCat.of (X × Y)) (pointSimplex (TopCat.of (X × Y)) (x, y))) := by
  refine ⟨?_, ?_⟩
  · intro p q σ τ
    exact shuffle_tmul_generator X Y p q σ τ
  · refine ⟨?_, ?_⟩
    · intro p q a b
      by_cases hzero : p = 0 ∨ q = 0
      · exact shuffle_zero_boundary X Y p q hzero a b
      · have hp : p ≠ 0 := fun h ↦ hzero (Or.inl h)
        have hq : q ≠ 0 := fun h ↦ hzero (Or.inr h)
        simp only [firstBoundaryTerm, secondBoundaryTerm, hp, hq, dite_false]
        let L := (shuffleBilinear X Y p q).compr₂
          (boundary (TopCat.of (X × Y)) (p + q))
        let R₁ := ((shuffleBilinear X Y (p - 1) q).comp (boundary X p)).compr₂
          (regrade (TopCat.of (X × Y)) (by omega : p - 1 + q = p + q - 1))
        let R₂ := ((shuffleBilinear X Y p (q - 1)).compl₂ (boundary Y q)).compr₂
          (regrade (TopCat.of (X × Y)) (by omega : p + (q - 1) = p + q - 1))
        have h : L = R₁ + (-1 : ℚ)^p • R₂ := by
          apply chain_linearMap_ext X p (ModuleCat.of ℚ
            (Chain Y q →ₗ[ℚ] Chain (TopCat.of (X × Y)) (p + q - 1)))
          intro σ
          apply chain_linearMap_ext Y q
          intro τ
          change boundary (TopCat.of (X × Y)) (p + q)
            (shuffle X Y p q (generator X σ ⊗ₜ[ℚ] generator Y τ)) =
            regrade (TopCat.of (X × Y)) (by omega : p - 1 + q = p + q - 1)
              (shuffleBilinear X Y (p - 1) q (boundary X p (generator X σ)) (generator Y τ)) +
            (-1 : ℚ)^p • regrade (TopCat.of (X × Y))
              (by omega : p + (q - 1) = p + q - 1)
              (shuffleBilinear X Y p (q - 1) (generator X σ) (boundary Y q (generator Y τ)))
          rw [shuffle_tmul_generator]
          simpa only [firstBoundaryTerm, secondBoundaryTerm, hp, hq, dite_false] using
            shuffle_positive_boundary_generator X Y p q hp hq σ τ
        exact LinearMap.congr_fun (LinearMap.congr_fun h a) b
    · refine ⟨?_, ?_⟩
      · intro X' Y' f g p q a b
        exact shuffle_naturality X Y X' Y' f g p q a b
      · refine ⟨?_, ?_⟩
        · intro q x τ
          exact left_row_point X Y q x τ
        · refine ⟨?_, ?_⟩
          · intro p σ y
            exact right_row_point X Y p σ y
          · intro x y
            exact shuffle_point_point X Y x y


end HolomorphicAnosov.SignedShuffle
