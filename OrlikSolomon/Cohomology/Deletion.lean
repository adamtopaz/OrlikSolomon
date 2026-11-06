/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Algebra.Exact
public import OrlikSolomon.Cohomology.DeletionPair
public import OrlikSolomon.Combinatorics.Betti

/-!
# The first induction: generation, exactness and the dimension bound

This file proves, from the axioms `OrdinaryTheory` alone, that the cohomology of the complement of
every arrangement is spanned by products of logarithmic classes, vanishes outside
`0 ≤ p ≤ dim V`, and has a finite basis of such products, and that every deletion gives a short
exact sequence. It does not use the Orlik–Solomon presentation, and it does not import it.

Everything is by strong induction on the number of hyperplanes, over all finite-dimensional ambient
spaces. A restriction changes the ambient space, so an induction with `V` fixed would not supply its
own hypothesis: see `Arrangement.induction`.

The key point is why the deletion sequence, which the axioms only give as a long exact sequence,
becomes short exact. If `C(U_𝒜'')` is generated, then each of its generating monomials lifts to
`C(U_𝒜')`, so `i^*` is surjective. Then `[f_H] j^* β` lifts `i^* β` along the residue, so the
residue is surjective, the Gysin map vanishes, and `j^*` is injective. This is where the vanishing
of Gysin maps is proved. No property of the normal line is used.

## Main definitions

* `OrdinaryTheory.logMonomial 𝒜 l`: the monomial `[f_{H₁}] ⋯ [f_{Hₛ}]` of a word `l` in the
  hyperplanes of `𝒜`. Which equations are used does not matter, by
  `logClass_complementUnit_eq_logClass_equationUnit`.
* `OrdinaryTheory.Generated 𝒜`: `C(U_𝒜)` is spanned over `B` by the logarithmic monomials.
* `OrdinaryTheory.Bounded 𝒜`: the pieces of `C(U_𝒜)` vanish outside `0 ≤ p ≤ dim V`.
* `OrdinaryTheory.IsDeletionShortExact hH`: the assertion of `lem:ses` for a hyperplane `H` of `𝒜`.
* `OrdinaryTheory.LogMonomialBasis 𝒜`: a finite `B`-basis of `C(U_𝒜)` of logarithmic monomials, with
  `LogMonomialBasis.wordCount` the number of its words of a given length.

## Main results

* `lem:restriction-surj`: `OrdinaryTheory.surjective_map_complementRestriction_of_generated`.
* `lem:ses`: `OrdinaryTheory.isDeletionShortExact_of_generated`.
* `thm:generation`: `OrdinaryTheory.generated_and_bounded`, with its parts
  `OrdinaryTheory.generated`, `OrdinaryTheory.bounded`,
  `OrdinaryTheory.eq_zero_of_mem_grading_of_finrank_lt` and
  `OrdinaryTheory.eq_zero_of_mem_grading_of_neg`, and the short exact sequence of every deletion in
  `OrdinaryTheory.isDeletionShortExact`.
* `thm:cohom-basis`: `OrdinaryTheory.exists_logMonomialBasis`.
* The sentence of item C3 of `def:cohomology` that iteration gives the same conclusion for affine
  spaces: `OrdinaryTheory.affineSpaceEquiv`, `OrdinaryTheory.bijective_map_fromPoint_affineSpace`
  and `OrdinaryTheory.eq_zero_of_mem_grading_affineSpace`, and the same for the empty arrangement.

## Implementation notes

**Generated and bounded are predicates, not assumptions on a theory.** Nothing here adds a field to
`OrdinaryTheory`. They are conclusions, proved in `generated_and_bounded`.

**An element of a span is not a monomial.** The steps that lift a class work on the whole span, by
the universal property of `Submodule.span`, and never assume that a generated element is a single
monomial.

**The number of words of each length is part of `exists_logMonomialBasis`.** It cannot be read off
from a basis: over the zero coefficient ring every family is a basis, so a bare `LogMonomialBasis`
says nothing about it, and neither `finrank` nor a rank argument can recover it. The words of the
recursive basis have the numbers given by the Betti recurrence of `Combinatorics/Betti`, whichever
hyperplane is chosen at each step, and the theorem records this. This is the first sentence of
`thm:betti`. It is why this file imports `Combinatorics/Betti`, which depends only on
`Geometry/Arrangement`. For another count by the same recursion, use `LogMonomialBasis.empty`,
`LogMonomialBasis.ofDeletion` and their `wordCount` lemmas.

## Blueprint

`lem:restriction-surj`, `lem:ses`, `thm:generation`, `thm:cohom-basis`, the first sentence of
`thm:betti`, and the last sentence of item C3 of `def:cohomology`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Module
open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement

universe u v w z

namespace OrlikSolomon

namespace OrdinaryTheory

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {𝒜 : Arrangement k V} {H : AffineSubspace k V} {f : V →ᵃ[k] k}

/-! ### Affine spaces and the empty arrangement -/

section Empty

/-- The conclusion of item C3 of `def:cohomology` for the point: the structure map is bijective, and
the cohomology is concentrated in cohomological degree zero. -/
private structure IsPointLike (A : SmoothAlg k) : Prop where
  /-- The structure map is bijective. -/
  bijective : Function.Bijective (algebraMap B (T.C.obj A))
  /-- The cohomology is concentrated in cohomological degree zero. -/
  eq_zero {p w : ℤ} (hp : p ≠ 0) {x : T.C.obj A} (hx : x ∈ T.grading A (p, w)) : x = 0

private lemma isPointLike_point : IsPointLike T (point k) :=
  ⟨T.bijective_algebraMap_point, T.eq_zero_of_mem_grading_point⟩

variable {T} in
private lemma IsPointLike.of_bijective_map {A D : SmoothAlg k} {g : A ⟶ D}
    (hg : Function.Bijective (T.C.map g)) (h : IsPointLike T A) : IsPointLike T D where
  bijective := by
    have heq : (algebraMap B (T.C.obj D) : B → T.C.obj D) =
        T.C.map g ∘ algebraMap B (T.C.obj A) :=
      funext fun b ↦ (T.map_algebraMap g b).symm
    rw [heq]
    exact hg.comp h.bijective
  eq_zero hp x hx := by
    obtain ⟨y, hy, rfl⟩ := (T.isHomogeneousOfShift_map g).exists_mem_preimage_of_surjective hg.2
      (add_zero _) hx
    rw [h.eq_zero hp hy, map_zero]

/-- Pullback along an isomorphism is bijective. -/
lemma bijective_map_hom {A D : SmoothAlg k} (e : A ≅ D) : Function.Bijective (T.C.map e.hom) :=
  Function.bijective_iff_has_inverse.2 ⟨T.C.map e.inv, fun x ↦ by simp [T.map_map],
    fun x ↦ by simp [T.map_map]⟩

variable {T} in
private lemma IsPointLike.of_iso {A D : SmoothAlg k} (e : A ≅ D) (h : IsPointLike T A) :
    IsPointLike T D :=
  h.of_bijective_map (T.bijective_map_hom e)

variable {T} in
/-- The structure map reflects weights, as soon as it is injective. -/
private lemma IsPointLike.algebraMap_mem_grading_iff {A : SmoothAlg k} (h : IsPointLike T A) {w : ℤ}
    {b : B} : algebraMap B (T.C.obj A) b ∈ T.grading A (0, w) ↔ b ∈ ℬ w := by
  refine ⟨fun hb ↦ ?_, T.algebraMap_mem_grading _⟩
  have hd := T.coe_decompose_algebraMap A b w
  rw [DirectSum.decompose_of_mem_same _ hb] at hd
  rw [h.bijective.1 hd]
  exact (DirectSum.decompose ℬ b w).2

variable (V) in
private lemma isPointLike_affineSpace : IsPointLike T (affineSpace k V) :=
  affineSpace_induction (T.isPointLike_point)
    (fun A h ↦ h.of_bijective_map (T.bijective_map_polynomialC A)) IsPointLike.of_iso V

variable (V) in
private lemma isPointLike_complement_empty : IsPointLike T (complement (∅ : Arrangement k V)) :=
  complement_empty_induction (T.isPointLike_point)
    (fun A h ↦ h.of_bijective_map (T.bijective_map_polynomialC A)) IsPointLike.of_iso V

variable (V) in
/-- The structure map `B → C(V)` is bijective, for every finite-dimensional `V`, including dimension
zero. Blueprint: item C3 of `def:cohomology`. -/
theorem bijective_algebraMap_affineSpace :
    Function.Bijective (algebraMap B (T.C.obj (affineSpace k V))) :=
  (T.isPointLike_affineSpace V).bijective

variable (V) in
/-- Iterating affine-line invariance: pullback along `V → pt` is bijective. It preserves bidegrees
by `isHomogeneousOfShift_map`. Blueprint: item C3 of `def:cohomology`. -/
theorem bijective_map_fromPoint_affineSpace :
    Function.Bijective (T.C.map (fromPoint (affineSpace k V))) := by
  refine (Function.Bijective.of_comp_iff _ T.bijective_algebraMap_point).1 ?_
  have heq : T.C.map (fromPoint (affineSpace k V)) ∘ algebraMap B (T.C.obj (point k)) =
      algebraMap B (T.C.obj (affineSpace k V)) :=
    funext fun b ↦ T.map_algebraMap _ b
  rw [heq]
  exact T.bijective_algebraMap_affineSpace V

/-- The cohomology of an affine space is concentrated in cohomological degree zero. Blueprint: item
C3 of `def:cohomology`. -/
theorem eq_zero_of_mem_grading_affineSpace {p w : ℤ} (hp : p ≠ 0) {x : T.C.obj (affineSpace k V)}
    (hx : x ∈ T.grading (affineSpace k V) (p, w)) : x = 0 :=
  (T.isPointLike_affineSpace V).eq_zero hp hx

variable (V) in
/-- The identification of the cohomology of an affine space with `B`. It sends `ℬ w` into degree
`(0, w)` by `algebraMap_mem_grading`. Blueprint: item C3 of `def:cohomology`. -/
def affineSpaceEquiv : B ≃ₐ[B] T.C.obj (affineSpace k V) :=
  AlgEquiv.ofBijective (Algebra.ofId B _) (T.bijective_algebraMap_affineSpace V)

@[simp] lemma affineSpaceEquiv_apply (b : B) :
    T.affineSpaceEquiv V b = algebraMap B (T.C.obj (affineSpace k V)) b := rfl

/-- The identification of `B` with `C(V)` carries `ℬ w` onto degree `(0, w)`: it sends `ℬ w` into
that degree, by `algebraMap_mem_grading`, and it reflects weights by this lemma. Blueprint: item C3
of `def:cohomology`. -/
theorem algebraMap_mem_grading_affineSpace_iff {w : ℤ} {b : B} :
    algebraMap B (T.C.obj (affineSpace k V)) b ∈ T.grading (affineSpace k V) (0, w) ↔ b ∈ ℬ w :=
  (T.isPointLike_affineSpace V).algebraMap_mem_grading_iff

variable (V) in
/-- The structure map `B → C(U_∅)` is bijective. Blueprint: the base case of `thm:generation`. -/
theorem bijective_algebraMap_complement_empty :
    Function.Bijective (algebraMap B (T.C.obj (complement (∅ : Arrangement k V)))) :=
  (T.isPointLike_complement_empty V).bijective

/-- The cohomology of the empty arrangement is concentrated in cohomological degree zero.
Blueprint: the base case of `thm:generation`. -/
theorem eq_zero_of_mem_grading_complement_empty {p w : ℤ} (hp : p ≠ 0)
    {x : T.C.obj (complement (∅ : Arrangement k V))}
    (hx : x ∈ T.grading (complement (∅ : Arrangement k V)) (p, w)) : x = 0 :=
  (T.isPointLike_complement_empty V).eq_zero hp hx

/-- The structure map `B → C(U_∅)` reflects weights. Blueprint: the base case of
`thm:generation`. -/
theorem algebraMap_mem_grading_complement_empty_iff {w : ℤ} {b : B} :
    algebraMap B (T.C.obj (complement (∅ : Arrangement k V))) b ∈
        T.grading (complement (∅ : Arrangement k V)) (0, w) ↔ b ∈ ℬ w :=
  (T.isPointLike_complement_empty V).algebraMap_mem_grading_iff

end Empty

/-! ### Logarithmic monomials -/

section Monomial

/-- The logarithm of any equation of a hyperplane of `𝒜` is the logarithm of its chosen equation,
since the two differ by a nonzero constant. So nothing below depends on the chosen equations.

Blueprint: `lem:log-mul`. -/
theorem logClass_complementUnit_eq_logClass_equationUnit (hH : H ∈ 𝒜) (hf : IsEquation f H) :
    T.logClass (complementUnit 𝒜 f (hf.covers hH)) = T.logClass (equationUnit 𝒜 ⟨H, hH⟩) := by
  obtain ⟨c, hc⟩ := exists_complementUnit_eq_constUnit_mul_equationUnit hH hf
  rw [hc]
  exact T.logClass_units_map_algebraMap_mul c _

variable (𝒜) in
/-- The logarithmic monomial `[f_{H₁}] ⋯ [f_{Hₛ}]` of a word `[H₁, …, Hₛ]` in the hyperplanes of
`𝒜`. The empty word gives `1`. A word has bidegree `(s, s)`, by `logMonomial_mem_grading`. The
logarithms of the chosen equations are used, but any others give the same classes, by
`logClass_complementUnit_eq_logClass_equationUnit`.

Blueprint: `thm:generation`, `thm:cohom-basis`. -/
def logMonomial (l : List 𝒜) : T.C.obj (complement 𝒜) :=
  word (fun K ↦ T.logClass (equationUnit 𝒜 K)) l

lemma logMonomial_eq_word (l : List 𝒜) :
    T.logMonomial 𝒜 l = word (fun K ↦ T.logClass (equationUnit 𝒜 K)) l := rfl

@[simp] lemma logMonomial_nil : T.logMonomial 𝒜 [] = 1 := word_nil _

@[simp] lemma logMonomial_cons (K : 𝒜) (l : List 𝒜) :
    T.logMonomial 𝒜 (K :: l) = T.logClass (equationUnit 𝒜 K) * T.logMonomial 𝒜 l :=
  word_cons _ _ _

/-- A logarithmic monomial of length `q` has bidegree `(q, q)`. Blueprint: `thm:cohom-basis`. -/
theorem logMonomial_mem_grading (l : List 𝒜) :
    T.logMonomial 𝒜 l ∈ T.grading (complement 𝒜) ((l.length : ℤ), (l.length : ℤ)) :=
  T.word_logClass_mem_grading _ l

/-- A monomial of a sub-arrangement pulls back to the same monomial. -/
@[simp] theorem map_complementInclusion_logMonomial {ℬ : Arrangement k V} (h : 𝒜 ≤ ℬ) (l : List 𝒜) :
    T.C.map (complementInclusion h) (T.logMonomial 𝒜 l) =
      T.logMonomial ℬ (l.map (Arrangement.inclusion h)) := by
  simp [logMonomial, word_map]

/-- The logarithm of the chosen equation of the old representative of a retained hyperplane
restricts to the logarithm of the chosen equation of that hyperplane, since the two equations differ
by a nonzero constant on `U_𝒜''`.

Blueprint: `lem:restriction-surj`. -/
theorem map_complementRestriction_logClass_equationUnit_representative (hH : IsHyperplane H)
    (L : 𝒜.restriction H) :
    T.C.map (complementRestriction 𝒜 hH)
        (T.logClass (equationUnit (𝒜.deletion H) (representative L))) =
      T.logClass (equationUnit (𝒜.restriction H) L) := by
  obtain ⟨c, hc⟩ := exists_mapUnits_complementRestriction_equationUnit_representative hH L
  rw [T.map_logClass, hc]
  exact T.logClass_units_map_algebraMap_mul c _

/-- A restricted monomial is the restriction of the old monomial of the representatives.

Blueprint: `lem:restriction-surj`. -/
@[simp] theorem map_complementRestriction_logMonomial_map_representative (hH : IsHyperplane H)
    (l : List (𝒜.restriction H)) :
    T.C.map (complementRestriction 𝒜 hH)
        (T.logMonomial (𝒜.deletion H) (l.map representative)) =
      T.logMonomial (𝒜.restriction H) l := by
  rw [logMonomial, T.map_word_logClass, word_map, logMonomial]
  congr 1
  funext L
  rw [← T.map_logClass, T.map_complementRestriction_logClass_equationUnit_representative]

/-- A monomial pulled back from `U_𝒜'` has zero residue. -/
@[simp] theorem deletionResidue_logMonomial_map_inclusion (hH : H ∈ 𝒜)
    (l : List (𝒜.deletion H)) :
    T.deletionResidue hH (T.logMonomial 𝒜 (l.map (Arrangement.inclusion (𝒜.deletion_le H)))) =
      0 := by
  rw [← T.map_complementInclusion_logMonomial, deletionResidue_map_complementInclusion]

/-- The residue removes a leading `H` from a monomial and restricts the rest, as in
`lem:log-residue` with `β` a monomial. This is not a `simp` lemma, because `logMonomial_cons`
rewrites its left side first. -/
theorem deletionResidue_logMonomial_cons (hH : H ∈ 𝒜) (l : List (𝒜.deletion H)) :
    T.deletionResidue hH
        (T.logMonomial 𝒜 (⟨H, hH⟩ :: l.map (Arrangement.inclusion (𝒜.deletion_le H)))) =
      T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)) (T.logMonomial (𝒜.deletion H) l) := by
  rw [logMonomial_cons, ← T.map_complementInclusion_logMonomial]
  exact T.deletionResidue_logClass_mul hH (isEquation_equation (𝒜.isHyperplane hH)) _

end Monomial

/-! ### The predicates -/

section Predicates

variable (𝒜) in
/-- `Generated 𝒜`: the cohomology `C(U_𝒜)` is spanned over `B` by finite products of the
logarithmic generators. This is a predicate, not an assumption on the theory: `generated` proves it
for every arrangement.

Blueprint: `thm:generation`. -/
def Generated : Prop :=
  Submodule.span B (Set.range (T.logMonomial 𝒜)) = ⊤

variable (𝒜) in
/-- `Bounded 𝒜`: the homogeneous pieces of `C(U_𝒜)` vanish outside `0 ≤ p ≤ dim V`. This is a
predicate, not an assumption on the theory: `bounded` proves it for every arrangement.

Blueprint: `thm:generation`. -/
def Bounded : Prop :=
  ∀ p w : ℤ, (p < 0 ∨ (finrank k V : ℤ) < p) → ∀ x ∈ T.grading (complement 𝒜) (p, w), x = 0

variable {T}

/-- In a generated arrangement, every class is a `B`-combination of logarithmic monomials. To use
this, argue on the whole span: a class is not one monomial. -/
lemma Generated.mem_span (h : T.Generated 𝒜) (x : T.C.obj (complement 𝒜)) :
    x ∈ Submodule.span B (Set.range (T.logMonomial 𝒜)) :=
  h ▸ Submodule.mem_top

end Predicates

/-! ### `lem:restriction-surj` -/

section Surjective

/-- If the restriction `𝒜''` is generated, then `i^* : C(U_𝒜') → C(U_𝒜'')` is surjective. Each
generating monomial lifts to the monomial of old representatives, and the range of `i^*` is a
`B`-submodule, so it contains the whole span. The hyperplane `H` need not belong to `𝒜`.

Blueprint: `lem:restriction-surj`. -/
theorem surjective_map_complementRestriction_of_generated (hH : IsHyperplane H)
    (h : T.Generated (𝒜.restriction H)) :
    Function.Surjective (T.C.map (complementRestriction 𝒜 hH)) := by
  have hle : Submodule.span B (Set.range (T.logMonomial (𝒜.restriction H))) ≤
      LinearMap.range (T.C.map (complementRestriction 𝒜 hH)).hom.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨_, T.map_complementRestriction_logMonomial_map_representative hH l⟩
  exact fun z ↦ hle (h.mem_span z)

end Surjective

/-! ### `lem:ses` -/

section ShortExact

/-- The short exact sequence of a deletion
`0 → C(U_𝒜') → C(U_𝒜) → C(U_𝒜'') → 0` of `B`-modules, whose maps are the `B`-algebra map `j^*` and
the `B`-linear residue, together with the vanishing of the Gysin map. The residue has shift
`(-1, -1)`.

This is a conclusion: `isDeletionShortExact` proves it for every deletion, and the structure
`OrdinaryTheory` only provides the long exact sequence.

Blueprint: `lem:ses`. -/
structure IsDeletionShortExact (hH : H ∈ 𝒜) : Prop where
  /-- The residue is surjective. -/
  surjective_residue : Function.Surjective (T.deletionResidue hH)
  /-- The Gysin map vanishes. -/
  gysin_eq_zero : T.deletionGysin hH = 0
  /-- The pullback `j^*` is injective. -/
  injective_map : Function.Injective (T.C.map (complementInclusion (𝒜.deletion_le H)))
  /-- The sequence is exact at `C(U_𝒜)`. -/
  exact : Function.Exact (T.C.map (complementInclusion (𝒜.deletion_le H))) (T.deletionResidue hH)
  /-- The residue has shift `(-1, -1)`. -/
  isHomogeneousOfShift_residue :
    IsHomogeneousOfShift (T.grading (complement 𝒜)) (T.grading (complement (𝒜.restriction H)))
      (-1, -1) (T.deletionResidue hH)

/-- If the restriction `𝒜''` is generated, then the residue of the deletion of `H` is surjective,
its Gysin map vanishes, and `0 → C(U_𝒜') → C(U_𝒜) → C(U_𝒜'') → 0` is exact. The vanishing and the
injectivity are consequences here, of the surjectivity of `i^*`.

Blueprint: `lem:ses`. -/
theorem isDeletionShortExact_of_generated (hH : H ∈ 𝒜) (h : T.Generated (𝒜.restriction H)) :
    T.IsDeletionShortExact hH :=
  have hi := T.surjective_map_complementRestriction_of_generated (𝒜.isHyperplane hH) h
  { surjective_residue := T.surjective_deletionResidue_of_surjective_map hH hi
    gysin_eq_zero := T.deletionGysin_eq_zero_of_surjective_map hH hi
    injective_map := T.injective_map_complementInclusion_of_surjective_map hH hi
    exact := T.exact_map_deletionResidue hH
    isHomogeneousOfShift_residue := T.isHomogeneousOfShift_deletionResidue hH }

end ShortExact

/-! ### `thm:generation` -/

section Generation

/-- The span of a family that spans is carried into a submodule `S` by a linear map as soon as the
members of the family are. This is what replaces a false assumption that an element of a span is a
single monomial. -/
private lemma map_mem_of_span_eq_top {B M N ι : Type*} [Semiring B] [AddCommMonoid M]
    [AddCommMonoid N] [Module B M] [Module B N] (g : M →ₗ[B] N) {v : ι → M}
    (hv : Submodule.span B (Set.range v) = ⊤) {S : Submodule B N} (h : ∀ i, g (v i) ∈ S) (y : M) :
    g y ∈ S := by
  have hle : Submodule.span B (Set.range v) ≤ S.comap g := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  exact hle (hv ▸ Submodule.mem_top)

/-- The empty arrangement is generated by the empty word, because `B → C(U_∅)` is surjective. This
holds in every dimension, including dimension zero. Blueprint: `thm:generation`. -/
theorem generated_empty : T.Generated (∅ : Arrangement k V) := by
  rw [Generated, eq_top_iff]
  rintro x -
  obtain ⟨b, rfl⟩ := (T.bijective_algebraMap_complement_empty V).2 x
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], T.logMonomial_nil⟩)

/-- The empty arrangement is bounded, because its cohomology is concentrated in degree zero. This
holds in every dimension, including dimension zero. Blueprint: `thm:generation`. -/
theorem bounded_empty : T.Bounded (∅ : Arrangement k V) := fun p _ hp _ hx ↦
  T.eq_zero_of_mem_grading_complement_empty (by omega) hx

/-- The inductive step of generation: if `𝒜'` is generated and `i^*` is surjective, then `𝒜` is
generated. A class `x` is `j^* a + [f_H] j^* β`, where `β` lifts its residue. Both `a` and `β` are
in the span of the old monomials, and each of the two maps `y ↦ j^* y` and `y ↦ [f_H] j^* y` carries
that whole span into the span of the monomials of `𝒜`.

Blueprint: `thm:generation`. -/
theorem generated_of_generated_deletion (hH : H ∈ 𝒜) (h : T.Generated (𝒜.deletion H))
    (hi : Function.Surjective (T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)))) :
    T.Generated 𝒜 := by
  set S := Submodule.span B (Set.range (T.logMonomial 𝒜))
  set a : T.C.obj (complement (𝒜.deletion H)) →ₗ[B] T.C.obj (complement 𝒜) :=
    (T.C.map (complementInclusion (𝒜.deletion_le H))).hom.toLinearMap
  have h₁ : ∀ y, a y ∈ S := map_mem_of_span_eq_top a h fun l ↦
    Submodule.subset_span ⟨_, (T.map_complementInclusion_logMonomial _ l).symm⟩
  have h₂ : ∀ y, T.logClass (equationUnit 𝒜 ⟨H, hH⟩) * a y ∈ S :=
    map_mem_of_span_eq_top (LinearMap.mulLeft B _ ∘ₗ a) h fun l ↦ Submodule.subset_span ⟨_,
      (T.logMonomial_cons _ _).trans (congrArg _ (T.map_complementInclusion_logMonomial _ l).symm)⟩
  rw [Generated, eq_top_iff]
  rintro x -
  obtain ⟨β, hβ⟩ := hi (T.deletionResidue hH x)
  obtain ⟨y, rfl⟩ := T.exists_eq_map_complementInclusion_add_logClass_mul hH
    (isEquation_equation (𝒜.isHyperplane hH)) hβ
  exact add_mem (h₁ y) (h₂ β)

/-- The inductive step of the bound. If `p < 0` or `n < p`, then the piece `(p, w)` of `C(U_𝒜')`
and the piece `(p - 1, w - 1)` of `C(U_𝒜'')` both vanish, since `H` has dimension `n - 1`. Exactness
kills the piece `(p, w)` of `C(U_𝒜)`.

Blueprint: `thm:generation`. -/
theorem bounded_of_bounded_deletion_of_bounded_restriction (hH : H ∈ 𝒜)
    (h' : T.Bounded (𝒜.deletion H)) (h'' : T.Bounded (𝒜.restriction H)) : T.Bounded 𝒜 := by
  intro p w hp x hx
  refine T.eq_zero_of_mem_grading_complement hH (h' p w hp) (h'' _ _ ?_) hx
  have := (𝒜.isHyperplane hH).finrank_direction_add_one
  omega

/-- Every arrangement, in every finite-dimensional ambient space, is generated and bounded. This is
by strong induction on the number of hyperplanes, over all ambient spaces, since a restriction
changes the ambient space. The base case is the empty arrangement in every dimension, including
dimension zero, which has no hyperplanes.

Blueprint: `thm:generation`. -/
theorem generated_and_bounded (𝒜 : Arrangement k V) : T.Generated 𝒜 ∧ T.Bounded 𝒜 :=
  Arrangement.induction (motive := fun _ _ _ _ ℬ ↦ T.Generated ℬ ∧ T.Bounded ℬ)
    (fun _ _ _ _ ↦ ⟨T.generated_empty, T.bounded_empty⟩)
    (fun _ _ _ _ ℬ _ hH h' h'' ↦
      ⟨T.generated_of_generated_deletion hH h'.1
          (T.surjective_map_complementRestriction_of_generated (ℬ.isHyperplane hH) h''.1),
        T.bounded_of_bounded_deletion_of_bounded_restriction hH h'.2 h''.2⟩)
    V 𝒜

/-- Every arrangement is generated: `C(U_𝒜)` is spanned over `B` by logarithmic monomials.

Blueprint: `thm:generation`. -/
theorem generated (𝒜 : Arrangement k V) : T.Generated 𝒜 :=
  (T.generated_and_bounded 𝒜).1

/-- Every arrangement is bounded: `C(U_𝒜)` vanishes outside `0 ≤ p ≤ dim V`.

Blueprint: `thm:generation`. -/
theorem bounded (𝒜 : Arrangement k V) : T.Bounded 𝒜 :=
  (T.generated_and_bounded 𝒜).2

/-- The dimension bound in the form used for the relations of the Orlik–Solomon algebra: `C(U_𝒜)`
vanishes above the dimension of `V`, for every arrangement in every space.

Blueprint: `thm:generation`. -/
theorem eq_zero_of_mem_grading_of_finrank_lt (𝒜 : Arrangement k V) {p w : ℤ}
    (hp : (finrank k V : ℤ) < p) {x : T.C.obj (complement 𝒜)}
    (hx : x ∈ T.grading (complement 𝒜) (p, w)) : x = 0 :=
  T.bounded 𝒜 p w (Or.inr hp) x hx

/-- `C(U_𝒜)` vanishes in negative cohomological degree. Blueprint: `thm:generation`. -/
theorem eq_zero_of_mem_grading_of_neg (𝒜 : Arrangement k V) {p w : ℤ} (hp : p < 0)
    {x : T.C.obj (complement 𝒜)} (hx : x ∈ T.grading (complement 𝒜) (p, w)) : x = 0 :=
  T.bounded 𝒜 p w (Or.inl hp) x hx

/-- The short exact sequence of `lem:ses` holds for every deletion.

Blueprint: `thm:generation`. -/
theorem isDeletionShortExact (hH : H ∈ 𝒜) : T.IsDeletionShortExact hH :=
  T.isDeletionShortExact_of_generated hH (T.generated _)

/-- The restriction `i^*` is surjective, for every hyperplane `H`, which need not belong to `𝒜`.

Blueprint: `thm:generation`, `lem:restriction-surj`. -/
theorem surjective_map_complementRestriction (hH : IsHyperplane H) :
    Function.Surjective (T.C.map (complementRestriction 𝒜 hH)) :=
  T.surjective_map_complementRestriction_of_generated hH (T.generated _)

/-- The residue of every deletion is surjective. Blueprint: `thm:generation`, `lem:ses`. -/
theorem surjective_deletionResidue (hH : H ∈ 𝒜) : Function.Surjective (T.deletionResidue hH) :=
  (T.isDeletionShortExact hH).surjective_residue

/-- The Gysin map of every deletion vanishes. Blueprint: `thm:generation`, `lem:ses`. -/
theorem deletionGysin_eq_zero (hH : H ∈ 𝒜) : T.deletionGysin hH = 0 :=
  (T.isDeletionShortExact hH).gysin_eq_zero

/-- The pullback `j^*` of every deletion is injective. Blueprint: `thm:generation`, `lem:ses`. -/
theorem injective_map_complementInclusion (hH : H ∈ 𝒜) :
    Function.Injective (T.C.map (complementInclusion (𝒜.deletion_le H))) :=
  (T.isDeletionShortExact hH).injective_map

/-- The form of `injective_map_complementInclusion` for the underlying linear map, as
`basisOfShortExact` and `lem:comparison` need it. -/
theorem injective_toLinearMap_complementInclusion (hH : H ∈ 𝒜) :
    Function.Injective (T.C.map (complementInclusion (𝒜.deletion_le H))).hom.toLinearMap :=
  T.injective_map_complementInclusion hH

/-- The form of `exact_map_deletionResidue` for the underlying linear map, as `basisOfShortExact`
and `lem:comparison` need it. -/
theorem exact_toLinearMap_deletionResidue (hH : H ∈ 𝒜) :
    Function.Exact (T.C.map (complementInclusion (𝒜.deletion_le H))).hom.toLinearMap
      (T.deletionResidue hH) :=
  T.exact_map_deletionResidue hH

end Generation

/-! ### `thm:cohom-basis` -/

section Basis

variable (𝒜) in
/-- A *logarithmic monomial basis* of `C(U_𝒜)`: a finite index type, a word in the hyperplanes of
`𝒜` for each index, of length at most `dim V`, and a `B`-basis whose vector at each index is the
logarithmic monomial of its word. By `LogMonomialBasis.basis_mem_grading`, the vector of a word of
length `q` has bidegree `(q, q)`.

The basis is certified data, since a numerical rank would not be well defined in general: the
coefficient ring can be zero. For the same reason, the number of words of each length is not
determined by this data: over the zero ring every family is a basis. The recursive basis of
`exists_logMonomialBasis` has the right numbers.

Blueprint: `thm:cohom-basis`. -/
structure LogMonomialBasis where
  /-- The index type. -/
  Index : Type
  /-- The index type is finite. -/
  [fintype : Fintype Index]
  /-- The word of an index. -/
  word : Index → List 𝒜
  /-- The basis. -/
  basis : Basis Index B (T.C.obj (complement 𝒜))
  /-- The basis vector of an index is the logarithmic monomial of its word. -/
  basis_apply (i : Index) : basis i = T.logMonomial 𝒜 (word i)
  /-- The words have length at most the dimension of `V`. -/
  length_le (i : Index) : (word i).length ≤ finrank k V

namespace LogMonomialBasis

attribute [instance] LogMonomialBasis.fintype

attribute [simp] LogMonomialBasis.basis_apply

variable {T}

/-- The vector of a word of length `q` has bidegree `(q, q)`. Blueprint: `thm:cohom-basis`. -/
theorem basis_mem_grading (b : T.LogMonomialBasis 𝒜) (i : b.Index) :
    b.basis i ∈ T.grading (complement 𝒜) (((b.word i).length : ℤ), ((b.word i).length : ℤ)) := by
  rw [b.basis_apply]
  exact T.logMonomial_mem_grading _

/-- A logarithmic monomial basis generates. -/
theorem generated (b : T.LogMonomialBasis 𝒜) : T.Generated 𝒜 := by
  refine eq_top_iff.2 (b.basis.span_eq.symm.trans_le (Submodule.span_mono ?_))
  rintro _ ⟨i, rfl⟩
  exact ⟨_, (b.basis_apply i).symm⟩

/-- The number of words of length `q` in a logarithmic monomial basis. -/
def wordCount (b : T.LogMonomialBasis 𝒜) (q : ℕ) : ℕ :=
  Fintype.card {i // (b.word i).length = q}

variable (T) in
/-- The logarithmic monomial basis of the empty arrangement, which consists of the empty word. This
is the initial basis of `thm:cohom-basis`, in every dimension. -/
def empty : T.LogMonomialBasis (∅ : Arrangement k V) where
  Index := Unit
  word _ := []
  basis := (Basis.singleton Unit B).map
    (LinearEquiv.ofBijective (Algebra.linearMap B _) (T.bijective_algebraMap_complement_empty V))
  basis_apply _ := by
    rw [Basis.map_apply, Basis.singleton_apply, logMonomial_nil]
    exact map_one (algebraMap B _)
  length_le _ := by simp

/-- The empty word is the only word of the basis of the empty arrangement. -/
theorem wordCount_empty (q : ℕ) :
    (empty T : T.LogMonomialBasis (∅ : Arrangement k V)).wordCount q = if q = 0 then 1 else 0 := by
  change Fintype.card {_i : Unit // ([] : List (∅ : Arrangement k V)).length = q} = _
  rcases q with _ | q <;> simp

/-- The word of a restriction word in the deletion step: lift the letters to old representatives and
prepend `H`. -/
def liftedWord (hH : H ∈ 𝒜) (l : List (𝒜.restriction H)) : List 𝒜 :=
  ⟨H, hH⟩ :: (l.map representative).map (Arrangement.inclusion (𝒜.deletion_le H))

omit [FiniteDimensional k V] in
@[simp] lemma length_liftedWord (hH : H ∈ 𝒜) (l : List (𝒜.restriction H)) :
    (liftedWord hH l).length = l.length + 1 := by
  simp [liftedWord]

/-- The word `liftedWord hH l` lifts the restriction monomial of `l` along the residue. This is
`lem:log-residue` with `β` a lifted monomial. -/
theorem deletionResidue_logMonomial_liftedWord (hH : H ∈ 𝒜) (l : List (𝒜.restriction H)) :
    T.deletionResidue hH (T.logMonomial 𝒜 (liftedWord hH l)) =
      T.logMonomial (𝒜.restriction H) l := by
  rw [liftedWord, T.deletionResidue_logMonomial_cons,
    T.map_complementRestriction_logMonomial_map_representative]

/-- The inductive step of `thm:cohom-basis`. Given bases of `𝒜'` and of `𝒜''`, this is the basis of
`𝒜` obtained by preserving the words of the basis of `𝒜'`, and by lifting each word of the basis of
`𝒜''` to old representatives and prepending `H`. Since the deletion sequence is short exact, these
vectors form a basis by `lem:basis-ses`. -/
def ofDeletion (hH : H ∈ 𝒜) (b' : T.LogMonomialBasis (𝒜.deletion H))
    (b'' : T.LogMonomialBasis (𝒜.restriction H)) : T.LogMonomialBasis 𝒜 where
  Index := b'.Index ⊕ b''.Index
  word := Sum.elim (fun i ↦ (b'.word i).map (Arrangement.inclusion (𝒜.deletion_le H)))
    fun j ↦ liftedWord hH (b''.word j)
  basis := basisOfShortExact (T.injective_toLinearMap_complementInclusion hH)
    (T.exact_toLinearMap_deletionResidue hH) b'.basis b''.basis
    (fun j ↦ T.logMonomial 𝒜 (liftedWord hH (b''.word j)))
    fun j ↦ by rw [deletionResidue_logMonomial_liftedWord, b''.basis_apply]
  basis_apply i := by
    rcases i with i | j
    · simp
    · simp
  length_le i := by
    have hn := (𝒜.isHyperplane hH).finrank_direction_add_one
    rcases i with i | j
    · simpa using b'.length_le i
    · have hj := b''.length_le j
      simp only [Sum.elim_inr, length_liftedWord]
      omega

/-- In the step, old words keep their length and lifted restriction words gain one. -/
private lemma wordCount_ofDeletion (hH : H ∈ 𝒜) (b' : T.LogMonomialBasis (𝒜.deletion H))
    (b'' : T.LogMonomialBasis (𝒜.restriction H)) (q : ℕ) :
    (ofDeletion hH b' b'').wordCount q =
      b'.wordCount q + Fintype.card {j // (b''.word j).length + 1 = q} := by
  have e : {x : (ofDeletion hH b' b'').Index // ((ofDeletion hH b' b'').word x).length = q} ≃
      {i // (b'.word i).length = q} ⊕ {j // (b''.word j).length + 1 = q} :=
    Equiv.subtypeSum.trans (Equiv.sumCongr
      (Equiv.subtypeEquivRight fun i ↦ iff_of_eq (congrArg (· = q) (List.length_map _)))
      (Equiv.subtypeEquivRight fun j ↦ iff_of_eq (congrArg (· = q) (length_liftedWord hH _))))
  rw [wordCount, Fintype.card_congr e, Fintype.card_sum]
  rfl

/-- In the step, the only words of length zero are those of the basis of `𝒜'`. -/
theorem wordCount_ofDeletion_zero (hH : H ∈ 𝒜) (b' : T.LogMonomialBasis (𝒜.deletion H))
    (b'' : T.LogMonomialBasis (𝒜.restriction H)) :
    (ofDeletion hH b' b'').wordCount 0 = b'.wordCount 0 := by
  rw [wordCount_ofDeletion, Fintype.card_eq_zero_iff.2 ⟨fun j ↦ Nat.succ_ne_zero _ j.2⟩, add_zero]

/-- In the step, old words keep their length and lifted restriction words gain one. This is the
Betti recurrence on word counts. -/
theorem wordCount_ofDeletion_succ (hH : H ∈ 𝒜) (b' : T.LogMonomialBasis (𝒜.deletion H))
    (b'' : T.LogMonomialBasis (𝒜.restriction H)) (q : ℕ) :
    (ofDeletion hH b' b'').wordCount (q + 1) = b'.wordCount (q + 1) + b''.wordCount q := by
  rw [wordCount_ofDeletion, Fintype.card_congr (Equiv.subtypeEquivRight fun j ↦ Nat.succ_inj)]
  rfl

end LogMonomialBasis

/-- For every arrangement, `C(U_𝒜)` has a finite `B`-basis of logarithmic monomials, with the vector
of a word of length `q` of bidegree `(q, q)` and `q ≤ dim V`, and with exactly `b_q(𝒜)` words of
length `q`.

The proof is an induction on the number of hyperplanes, over all ambient spaces, which preserves the
deletion basis and prepends `H` to lifted restriction words. The basis is existential: there is no
globally canonical deletion tree. No rank is used, and the coefficient ring can be zero.

Blueprint: `thm:cohom-basis`, and the first sentence of `thm:betti`. -/
theorem exists_logMonomialBasis (𝒜 : Arrangement k V) :
    ∃ b : T.LogMonomialBasis 𝒜, ∀ q, b.wordCount q = 𝒜.bettiNumber q :=
  Arrangement.induction
    (motive := fun _ _ _ _ ℬ ↦ ∃ b : T.LogMonomialBasis ℬ, ∀ q, b.wordCount q = ℬ.bettiNumber q)
    (fun _ _ _ _ ↦ ⟨.empty T, fun q ↦ by rw [LogMonomialBasis.wordCount_empty, bettiNumber_empty]⟩)
    (fun _ _ _ _ ℬ _ hH ⟨b', hb'⟩ ⟨b'', hb''⟩ ↦ ⟨.ofDeletion hH b' b'', fun q ↦ by
      rcases q with _ | q
      · rw [LogMonomialBasis.wordCount_ofDeletion_zero, hb', bettiNumber_zero, bettiNumber_zero]
      · rw [LogMonomialBasis.wordCount_ofDeletion_succ, hb', hb'',
          bettiNumber_succ_deletion_restriction ℬ hH]⟩)
    V 𝒜

/-- The cohomology of the complement of an arrangement is a free `B`-module. -/
instance : Module.Free B (T.C.obj (complement 𝒜)) :=
  let ⟨b, _⟩ := T.exists_logMonomialBasis 𝒜
  .of_basis b.basis

/-- The cohomology of the complement of an arrangement is a finite `B`-module. -/
instance : Module.Finite B (T.C.obj (complement 𝒜)) :=
  let ⟨b, _⟩ := T.exists_logMonomialBasis 𝒜
  .of_basis b.basis

end Basis

end OrdinaryTheory

end OrlikSolomon
