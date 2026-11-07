/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.Schemes.Complement
public import OrlikSolomon.Presentation.Geometric.Transport
public import OrlikSolomon.Presentation.Structure

/-!
# The geometric affine structure theorem

For every arrangement `𝒜` in a finite-dimensional space, every geometric ordinary theory `T` on
every admissible domain `D` has a canonical bigrading-preserving equivalence of `B`-algebras
`Φ_𝒜 : OS_B(𝒜) ≃ C(U_𝒜)`, where `U_𝒜` is the complement as an actual open subscheme of affine
space, sending each generator `e_H` to the logarithmic class `[f_H|_{U_𝒜}]` of the restriction of
any equation of `H`. This is `Geometric.OrdinaryTheory.affineEquiv`, the main affine theorem of the
geometric refactor.

It is not proved again. It is the existing structure theorem for the algebraic theory
`T.toAlgebraic`, whose value at the coordinate ring of `U_𝒜` is `C(Spec O(U_𝒜))`, followed by
pullback along the comparison `s_𝒜 : U_𝒜 ≅ Spec O(U_𝒜)`:
`Φ_𝒜 = s_𝒜^* ∘ Φ_𝒜^{alg}` (`affineEquiv_apply`). Every lemma below is the corresponding existing
lemma composed with the laws of `transportAffineDevelopment`.

`U_𝒜` is smooth and affine, so it belongs to every admissible domain by instances, with no
hypothesis on `𝒜`. Nothing assumes that `2` is invertible, that the coefficients are nonzero, or
that `U_𝒜` has a rational point, and no characteristic is assumed.

## Main definitions

* `Geometric.OrdinaryTheory.affineEquiv 𝒜 : OSAlgebra B 𝒜 ≃ₐ[B] T.obj (D.complement 𝒜)`.
* `Geometric.OrdinaryTheory.logMonomial 𝒜 I`: the product of the logarithmic classes of the
  restricted chosen equations along a word `I`.
* `Geometric.OrdinaryTheory.affineComponentEquiv 𝒜 i`: the equivalence on the pieces of bidegree
  `i`.
* `Geometric.OrdinaryTheory.deletionResidue`, `Geometric.OrdinaryTheory.deletionGysin`: the residue
  and Gysin maps of the geometric deletion pair, which do not depend on the equation.
* `Geometric.OrdinaryTheory.residueComparison H`: the map `ψ : OS_B(𝒜) / im a → C(U_𝒜'')` induced
  by the residue, as in `lem:comparison-residue`.

## Main results

* `affineEquiv_apply`: `Φ_𝒜 = s_𝒜^* ∘ Φ_𝒜^{alg}`.
* Generators: `affineEquiv_generator_of_isEquation`, `affineEquiv_generator_zeroLocus`,
  `affineEquiv_word`.
* Independence of the equations and uniqueness on generators:
  `logClass_complementUnit_eq_of_isEquation`, `toAlgHom_affineEquiv_eq_lift`,
  `toAlgHom_affineEquiv_unique`.
* The bigrading in both directions: `isHomogeneousOfShift_affineEquiv`,
  `isHomogeneousOfShift_affineEquiv_symm`, `affineEquiv_mem_grading_iff`.
* Naturality: `affineEquiv_map` for an inclusion of arrangements, `affineEquiv_deletionMap`, and
  `affineEquiv_comapEquiv` for an affine equivalence.
* The deletion residue: `residue_deletionPair`, `transportAffineDevelopment_deletionResidue`,
  `residueComparison_cokernelMk`, `residueComparison_restrictionToCokernel` and
  `bijective_residueComparison`; and, for the presentation, `injective_deletionMap` and
  `bijective_restrictionToCokernel`.
* `ofAlgebraic_affineEquiv`: for the transport `ofAlgebraic E` of an algebraic theory, the theorem
  is the existing one for `E`.

The statements with coefficients in `R` are in `Presentation/Geometric/Ordinary`.

## Implementation notes

`affineEquiv_apply` is not a `simp` lemma, so that the generator lemmas fire. As in
`Presentation/Structure`, the generator formula for an arbitrary equation `f` cannot fire as a bare
`simp` lemma, since `f` is not on its left side: give it the equation, as in
`simp [T.affineEquiv_generator_of_isEquation H hf]`. Names that the scheme layer shares with
`SmoothAlg`, such as `complementUnit`, refer here to the geometric ones; the existing ones are
written with their namespace.

## Blueprint

`thm:geo-affine`, with `thm:affine`, `lem:comparison-residue` and the naturality of `cor:ordinary`
transported along `thm:geo-transport-all`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry DirectSum
open OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon.Geometric.OrdinaryTheory

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}
  (T : OrdinaryTheory.{u, v, w, z} D ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V] {𝒜 : Arrangement k V}

/-! ### The equivalence -/

section Affine

variable (𝒜) in
/-- **The geometric affine structure theorem.** For every arrangement `𝒜` in a finite-dimensional
space, the cohomology of the complement `U_𝒜`, an open subscheme of affine space, is the
Orlik–Solomon algebra: there is a canonical equivalence of `B`-algebras, sending the generator
`e_H` to the logarithmic class `[f_H|_{U_𝒜}]` of the restriction of any equation of `H`, by
`affineEquiv_generator_of_isEquation`. It preserves the bigrading in both directions, by
`isHomogeneousOfShift_affineEquiv` and `isHomogeneousOfShift_affineEquiv_symm`.

It holds for every geometric theory on every admissible domain, such as a theory on all smooth
schemes, for every coefficient ring, including `ℤ / 2` and the zero ring, and in dimension zero.
It is the existing equivalence for `T.toAlgebraic` followed by pullback along the comparison
`s_𝒜 : U_𝒜 ≅ Spec O(U_𝒜)` (`affineEquiv_apply`).

Blueprint: `thm:geo-affine`. -/
def affineEquiv : OSAlgebra B 𝒜 ≃ₐ[B] T.obj (D.complement 𝒜) :=
  (T.toAlgebraic.affineEquiv 𝒜).trans (transportAffineDevelopment T (D.complementIsoSpec 𝒜))

/-- The geometric structure theorem is the existing one for `T.toAlgebraic` followed by pullback
along `s_𝒜`: `Φ_𝒜 = s_𝒜^* ∘ Φ_𝒜^{alg}`. This is for `rw`, and it is not a `simp` lemma, so that
the lemmas below fire.

Blueprint: `thm:geo-affine`. -/
theorem affineEquiv_apply (x : OSAlgebra B 𝒜) :
    T.affineEquiv 𝒜 x = T.pull (D.complementIsoSpec 𝒜).hom (T.toAlgebraic.affineEquiv 𝒜 x) :=
  rfl

/-- The inverse of the geometric structure theorem is pullback along `s_𝒜⁻¹` followed by the
inverse of the existing one. -/
theorem affineEquiv_symm_apply (y : T.obj (D.complement 𝒜)) :
    (T.affineEquiv 𝒜).symm y =
      (T.toAlgebraic.affineEquiv 𝒜).symm (T.pull (D.complementIsoSpec 𝒜).inv y) :=
  rfl

/-- The equivalence sends a generator to the logarithmic class of the restriction of **any**
equation of its hyperplane. Since `f` is not on the left, `simp` needs the equation to be given,
as in `simp [T.affineEquiv_generator_of_isEquation H hf]`.

Blueprint: `thm:geo-affine`. -/
theorem affineEquiv_generator_of_isEquation {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    T.affineEquiv 𝒜 (generator B 𝒜 H) = T.logClass (complementUnit 𝒜 f (hf.covers H.2)) := by
  rw [affineEquiv_apply, T.toAlgebraic.affineEquiv_generator_of_isEquation H hf]
  exact T.pull_toAlgebraic_logClass _ _ (D.complementIsoSpec_hom_appTop_complementUnit _).symm

/-- The generator formula for a label presented by an equation: if the zero locus of `f` is a
hyperplane of `𝒜`, then its generator goes to `[f|_{U_𝒜}]`. Here `f` is on the left, so `simp`
uses this with no further input.

Blueprint: `thm:geo-affine`. -/
@[simp high]
theorem affineEquiv_generator_zeroLocus {f : V →ᵃ[k] k} (hf : zeroLocus f ∈ 𝒜) :
    T.affineEquiv 𝒜 (generator B 𝒜 ⟨zeroLocus f, hf⟩) =
      T.logClass (complementUnit 𝒜 f (.of_mem hf)) :=
  T.affineEquiv_generator_of_isEquation _ (isEquation_of_zeroLocus_mem hf)

/-- The logarithmic classes of the restrictions of two equations of a hyperplane of `𝒜` agree:
the classes do not depend on the equations.

Blueprint: `thm:geo-affine`. -/
theorem logClass_complementUnit_eq_of_isEquation {f g : V →ᵃ[k] k} (H : 𝒜)
    (hf : IsEquation f H) (hg : IsEquation g H) :
    T.logClass (X := D.complement 𝒜) (complementUnit 𝒜 f (hf.covers H.2)) =
      T.logClass (X := D.complement 𝒜) (complementUnit 𝒜 g (hg.covers H.2)) := by
  rw [← T.affineEquiv_generator_of_isEquation H hf, ← T.affineEquiv_generator_of_isEquation H hg]

/-- The inverse of the equivalence sends the logarithmic class of any equation of `H` to the
generator of `H`.

Blueprint: `thm:geo-affine`. -/
theorem affineEquiv_symm_logClass {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    (T.affineEquiv 𝒜).symm (T.logClass (complementUnit 𝒜 f (hf.covers H.2))) =
      generator B 𝒜 H := by
  rw [← T.affineEquiv_generator_of_isEquation H hf, AlgEquiv.symm_apply_apply]

/-- The logarithmic classes of the restrictions of any choice of equations satisfy the relations
of the presentation. -/
theorem isFamily_logClass_complementUnit (F : 𝒜 → V →ᵃ[k] k)
    (hF : ∀ H : 𝒜, IsEquation (F H) H) :
    IsFamily 𝒜 fun H ↦
      T.logClass (X := D.complement 𝒜) (complementUnit 𝒜 (F H) ((hF H).covers H.2)) := by
  have h : (fun H ↦
      T.logClass (X := D.complement 𝒜) (complementUnit 𝒜 (F H) ((hF H).covers H.2))) =
      fun H ↦ T.affineEquiv 𝒜 (generator B 𝒜 H) :=
    funext fun H ↦ (T.affineEquiv_generator_of_isEquation H (hF H)).symm
  rw [h]
  exact (isFamily_generator (B := B) (𝒜 := 𝒜)).map (T.affineEquiv 𝒜).toRingEquiv.toRingHom

/-- The equivalence does not depend on the equations: it is the lift of the logarithmic classes
of **any** choice of equations.

Blueprint: `thm:geo-affine`. -/
theorem toAlgHom_affineEquiv_eq_lift (F : 𝒜 → V →ᵃ[k] k) (hF : ∀ H : 𝒜, IsEquation (F H) H) :
    (T.affineEquiv 𝒜 : OSAlgebra B 𝒜 →ₐ[B] T.obj (D.complement 𝒜)) =
      OSAlgebra.lift _ (T.isFamily_logClass_complementUnit F hF) :=
  (OSAlgebra.lift_unique _ _ _).1 fun H ↦ T.affineEquiv_generator_of_isEquation H (hF H)

/-- **Uniqueness on generators.** The equivalence is the unique algebra map sending each generator
to the logarithmic class of the restriction of some equation of its hyperplane, for equations that
may be chosen arbitrarily.

Blueprint: `thm:geo-affine`. -/
theorem toAlgHom_affineEquiv_unique (F : 𝒜 → V →ᵃ[k] k) (hF : ∀ H : 𝒜, IsEquation (F H) H)
    (φ : OSAlgebra B 𝒜 →ₐ[B] T.obj (D.complement 𝒜))
    (hφ : ∀ H : 𝒜, φ (generator B 𝒜 H) = T.logClass (complementUnit 𝒜 (F H) ((hF H).covers H.2))) :
    φ = T.affineEquiv 𝒜 :=
  algHom_ext fun H ↦ (hφ H).trans (T.affineEquiv_generator_of_isEquation H (hF H)).symm

end Affine

/-! ### Logarithmic monomials -/

section Monomial

variable (𝒜) in
/-- The logarithmic monomial of a word `I` in the hyperplanes of `𝒜`: the product of the
logarithmic classes of the restrictions to `U_𝒜` of the chosen equations along `I`. By
`logMonomial_eq_word` it does not depend on the equations. It is the image of the word in the
generators (`affineEquiv_word`).

Blueprint: `thm:geo-affine`. -/
def logMonomial (I : List 𝒜) : T.obj (D.complement 𝒜) :=
  word (fun H : 𝒜 ↦ T.logClass (complementUnit 𝒜 (equation (H : AffineSubspace k V))
    ((isEquation_equation (𝒜.isHyperplane H.2)).covers H.2))) I

/-- The existing logarithmic monomial of `T.toAlgebraic` pulls back along `s_𝒜` to the geometric
one. -/
theorem pull_complementIsoSpec_logMonomial (I : List 𝒜) :
    T.pull (D.complementIsoSpec 𝒜).hom (T.toAlgebraic.logMonomial 𝒜 I) = T.logMonomial 𝒜 I := by
  rw [OrlikSolomon.OrdinaryTheory.logMonomial_eq_word, map_word]
  exact congrArg (word · I) <| funext fun H ↦
    T.pull_toAlgebraic_logClass _ _ (D.complementIsoSpec_hom_appTop_complementUnit _).symm

/-- The equivalence sends a word in the generators to its logarithmic monomial.

Blueprint: `thm:geo-affine`. -/
@[simp high]
theorem affineEquiv_word (I : List 𝒜) :
    T.affineEquiv 𝒜 (word (generator B 𝒜) I) = T.logMonomial 𝒜 I := by
  rw [affineEquiv_apply, OrlikSolomon.OrdinaryTheory.affineEquiv_word,
    pull_complementIsoSpec_logMonomial]

/-- The logarithmic monomial is the word in the logarithmic classes of **any** choice of
equations. -/
theorem logMonomial_eq_word (F : 𝒜 → V →ᵃ[k] k) (hF : ∀ H : 𝒜, IsEquation (F H) H)
    (I : List 𝒜) :
    T.logMonomial 𝒜 I =
      word (fun H ↦ T.logClass (complementUnit 𝒜 (F H) ((hF H).covers H.2))) I := by
  rw [← affineEquiv_word, map_word]
  exact congrArg (word · I) <| funext fun H ↦ T.affineEquiv_generator_of_isEquation H (hF H)

@[simp]
theorem logMonomial_nil : T.logMonomial 𝒜 [] = 1 :=
  word_nil _

/-- A logarithmic monomial of length `q` has bidegree `(q, q)`. -/
theorem logMonomial_mem_grading (I : List 𝒜) :
    T.logMonomial 𝒜 I ∈ T.grading (D.complement 𝒜) ((I.length : ℤ), (I.length : ℤ)) := by
  rw [← pull_complementIsoSpec_logMonomial]
  exact T.pull_mem_grading _ (T.toAlgebraic.logMonomial_mem_grading I)

/-- The inverse of the equivalence sends a logarithmic monomial to the word in the generators. -/
@[simp]
theorem affineEquiv_symm_logMonomial (I : List 𝒜) :
    (T.affineEquiv 𝒜).symm (T.logMonomial 𝒜 I) = word (generator B 𝒜) I := by
  rw [← T.affineEquiv_word I, AlgEquiv.symm_apply_apply]

end Monomial

/-! ### The bigrading -/

section Grading

variable (𝒜) in
/-- The equivalence preserves the bigrading of the presentation, with `e_H` in bidegree `(1, 1)`
and `B_w` in bidegree `(0, w)`.

Blueprint: `thm:geo-affine`. -/
theorem isHomogeneousOfShift_affineEquiv :
    IsHomogeneousOfShift (bigrading 𝒜 ℬ) (T.grading (D.complement 𝒜)) 0 (T.affineEquiv 𝒜) :=
  (isHomogeneousOfShift_transportAffineDevelopment T _).comp_of_add_eq
    (T.toAlgebraic.isHomogeneousOfShift_affineEquiv 𝒜) (add_zero 0)

variable (𝒜) in
/-- The inverse of the equivalence preserves the bigrading.

Blueprint: `thm:geo-affine`. -/
theorem isHomogeneousOfShift_affineEquiv_symm :
    IsHomogeneousOfShift (T.grading (D.complement 𝒜)) (bigrading 𝒜 ℬ) 0 (T.affineEquiv 𝒜).symm := by
  simpa only [neg_zero] using (T.isHomogeneousOfShift_affineEquiv 𝒜).algEquiv_symm

/-- An element has bidegree `i` exactly when its image under the equivalence has bidegree `i`.

Blueprint: `thm:geo-affine`. -/
theorem affineEquiv_mem_grading_iff {i : ℤ × ℤ} {x : OSAlgebra B 𝒜} :
    T.affineEquiv 𝒜 x ∈ T.grading (D.complement 𝒜) i ↔ x ∈ bigrading 𝒜 ℬ i :=
  (transportAffineDevelopment_mem_grading_iff T _).trans T.toAlgebraic.affineEquiv_mem_grading_iff

/-- A class has bidegree `i` exactly when its image under the inverse has bidegree `i`. -/
theorem affineEquiv_symm_mem_bigrading_iff {i : ℤ × ℤ} {y : T.obj (D.complement 𝒜)} :
    (T.affineEquiv 𝒜).symm y ∈ bigrading 𝒜 ℬ i ↔ y ∈ T.grading (D.complement 𝒜) i := by
  rw [← T.affineEquiv_mem_grading_iff, AlgEquiv.apply_symm_apply]

variable (𝒜) in
/-- The equivalence on the pieces of bidegree `i`, as an `R`-linear equivalence.
`Presentation/Geometric/Ordinary` computes these pieces.

Blueprint: `thm:geo-affine`. -/
def affineComponentEquiv (i : ℤ × ℤ) :
    bigrading 𝒜 ℬ i ≃ₗ[R] T.grading (D.complement 𝒜) i :=
  (T.isHomogeneousOfShift_affineEquiv 𝒜).componentEquiv (e := (T.affineEquiv 𝒜).toLinearEquiv)
    (add_zero i)

@[simp]
theorem coe_affineComponentEquiv_apply (i : ℤ × ℤ) (x : bigrading 𝒜 ℬ i) :
    (T.affineComponentEquiv 𝒜 i x : T.obj (D.complement 𝒜)) = T.affineEquiv 𝒜 x :=
  rfl

@[simp]
theorem coe_affineComponentEquiv_symm_apply (i : ℤ × ℤ) (y : T.grading (D.complement 𝒜) i) :
    ((T.affineComponentEquiv 𝒜 i).symm y : OSAlgebra B 𝒜) = (T.affineEquiv 𝒜).symm y :=
  rfl

end Grading

/-! ### Naturality -/

section Naturality

/-- The equivalence commutes with an inclusion of arrangements and the open pullback along the
inclusion of complements.

Blueprint: `thm:geo-affine`. -/
@[simp]
theorem affineEquiv_map {𝒟 : Arrangement k V} (h : 𝒜 ≤ 𝒟) (x : OSAlgebra B 𝒜) :
    T.affineEquiv 𝒟 (OSAlgebra.map B h x) =
      T.pull (D.complementInclusion h) (T.affineEquiv 𝒜 x) := by
  rw [affineEquiv_apply, affineEquiv_apply, OrlikSolomon.OrdinaryTheory.affineEquiv_map]
  exact transportAffineDevelopment_map T _ _ _ _
    (D.complementInclusion_comp_complementIsoSpec_hom h) _

/-- The equivalence commutes with deletion and the open pullback.

Blueprint: `thm:geo-affine`. -/
@[simp]
theorem affineEquiv_deletionMap (H : AffineSubspace k V) (x : OSAlgebra B (𝒜.deletion H)) :
    T.affineEquiv 𝒜 (deletionMap B 𝒜 H x) =
      T.pull (D.complementInclusion (𝒜.deletion_le H)) (T.affineEquiv (𝒜.deletion H) x) :=
  T.affineEquiv_map (𝒜.deletion_le H) x

/-- The equivalence commutes with a relabeling along an affine equivalence, which includes an
affine coordinate change, and the isomorphism of complements.

Blueprint: `thm:geo-affine`. -/
@[simp]
theorem affineEquiv_comapEquiv {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {𝒟 : Arrangement k W} (e : W ≃ᵃ[k] V) (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ 𝒟)
    (x : OSAlgebra B 𝒜) :
    T.affineEquiv 𝒟 (OSAlgebra.comapEquiv B e h x) =
      T.pull (D.complementIso 𝒜 𝒟 e h).hom (T.affineEquiv 𝒜 x) := by
  rw [affineEquiv_apply, affineEquiv_apply, OrlikSolomon.OrdinaryTheory.affineEquiv_comapEquiv]
  exact transportAffineDevelopment_map T _ _ _ _
    (D.complementIso_hom_comp_complementIsoSpec_hom e h) _

end Naturality

/-! ### The deletion residue -/

section Deletion

variable {H : AffineSubspace k V}

/-- The residue `C(U_𝒜) → C(U_𝒜'')` of a hyperplane `H` of `𝒜`: the residue of the geometric
deletion pair. It does not depend on an equation of `H`, by `residue_deletionPair`.

Blueprint: `thm:geo-affine`, `thm:geo-deletion`. -/
@[no_expose]
def deletionResidue (hH : H ∈ 𝒜) :
    T.obj (D.complement 𝒜) →ₗ[B] T.obj (D.complement (𝒜.restriction H)) :=
  T.residue (DivisorPair.deletionPair D 𝒜 hH (isEquation_equation (𝒜.isHyperplane hH)))

/-- The Gysin map `C(U_𝒜'') → C(U_𝒜')` of a hyperplane `H` of `𝒜`: the Gysin map of the geometric
deletion pair. It does not depend on an equation of `H`, by `gysin_deletionPair`.

Blueprint: `thm:geo-deletion`. -/
@[no_expose]
def deletionGysin (hH : H ∈ 𝒜) :
    T.obj (D.complement (𝒜.restriction H)) →ₗ[B] T.obj (D.complement (𝒜.deletion H)) :=
  T.gysin (DivisorPair.deletionPair D 𝒜 hH (isEquation_equation (𝒜.isHyperplane hH)))

/-- The deletion residue is the residue of the geometric deletion pair of every equation of `H`,
by naturality along the isomorphism of pairs given by identities.

Blueprint: `thm:geo-deletion`. -/
theorem residue_deletionPair (hH : H ∈ 𝒜) {f : V →ᵃ[k] k} (hf : IsEquation f H) :
    T.residue (DivisorPair.deletionPair D 𝒜 hH hf) = T.deletionResidue hH := by
  ext x
  have h := T.residue_pull
    (DivisorPair.deletionPairIso D hH hf (isEquation_equation (𝒜.isHyperplane hH))).hom x
  simp only [DivisorPair.deletionPairIso_hom_compl, DivisorPair.deletionPairIso_hom_closed,
    pull_id] at h
  exact h

/-- The deletion Gysin map is the Gysin map of the geometric deletion pair of every equation of
`H`.

Blueprint: `thm:geo-deletion`. -/
theorem gysin_deletionPair (hH : H ∈ 𝒜) {f : V →ᵃ[k] k} (hf : IsEquation f H) :
    T.gysin (DivisorPair.deletionPair D 𝒜 hH hf) = T.deletionGysin hH := by
  ext x
  have h := T.gysin_pull
    (DivisorPair.deletionPairIso D hH hf (isEquation_equation (𝒜.isHyperplane hH))).hom x
  simp only [DivisorPair.deletionPairIso_hom_ambient, DivisorPair.deletionPairIso_hom_closed,
    pull_id] at h
  exact h

/-- Under the comparisons `s`, the existing deletion residue of `T.toAlgebraic` is the geometric
one: this is the residue square of `thm:geo-deletion`, by naturality along
`DivisorPair.deletionPairIsoSpec`.

Blueprint: `thm:geo-affine`, `thm:geo-transport-all`. -/
theorem transportAffineDevelopment_deletionResidue (hH : H ∈ 𝒜)
    (x : T.toAlgebraic.C.obj (SmoothAlg.complement 𝒜)) :
    transportAffineDevelopment T (D.complementIsoSpec (𝒜.restriction H))
        (T.toAlgebraic.deletionResidue hH x) =
      T.deletionResidue hH (transportAffineDevelopment T (D.complementIsoSpec 𝒜) x) := by
  have h := T.residue_pull (DivisorPair.deletionPairIsoSpec D hH
    (isEquation_equation (𝒜.isHyperplane hH))).hom x
  rw [DivisorPair.deletionPairIsoSpec_hom_compl, DivisorPair.deletionPairIsoSpec_hom_closed] at h
  rw [← T.toAlgebraic.residue_deletionPair hH (isEquation_equation (𝒜.isHyperplane hH))]
  exact h.symm

/-- Under the comparisons `s`, the existing deletion Gysin map of `T.toAlgebraic` is the geometric
one.

Blueprint: `thm:geo-transport-all`. -/
theorem transportAffineDevelopment_deletionGysin (hH : H ∈ 𝒜)
    (x : T.toAlgebraic.C.obj (SmoothAlg.complement (𝒜.restriction H))) :
    transportAffineDevelopment T (D.complementIsoSpec (𝒜.deletion H))
        (T.toAlgebraic.deletionGysin hH x) =
      T.deletionGysin hH
        (transportAffineDevelopment T (D.complementIsoSpec (𝒜.restriction H)) x) := by
  have h := T.gysin_pull (DivisorPair.deletionPairIsoSpec D hH
    (isEquation_equation (𝒜.isHyperplane hH))).hom x
  rw [DivisorPair.deletionPairIsoSpec_hom_ambient, DivisorPair.deletionPairIsoSpec_hom_closed] at h
  rw [← T.toAlgebraic.gysin_deletionPair hH (isEquation_equation (𝒜.isHyperplane hH))]
  exact h.symm

variable (H : 𝒜)

/-- The map `ψ : OS_B(𝒜) / im a → C(U_𝒜'')` induced by `r Φ_𝒜`, which vanishes on the old image.
It is the existing one for `T.toAlgebraic`, followed by pullback along `s_𝒜''`. It is
characterized by `residueComparison_cokernelMk`, its composite with `s` is computed by
`residueComparison_restrictionToCokernel`, and it is bijective by `bijective_residueComparison`.

Blueprint: `thm:geo-affine`, the geometric form of `lem:comparison-residue`. -/
def residueComparison :
    DeletionCokernel B 𝒜 H →ₗ[B] T.obj (D.complement (𝒜.restriction H)) :=
  (transportAffineDevelopment T (D.complementIsoSpec (𝒜.restriction H))).toLinearMap ∘ₗ
    T.toAlgebraic.residueComparison H

/-- The map `ψ` sends the class of `x` to `r (Φ_𝒜 x)`.

Blueprint: `thm:geo-affine`. -/
@[simp]
theorem residueComparison_cokernelMk (x : OSAlgebra B 𝒜) :
    T.residueComparison H (cokernelMk B 𝒜 H x) = T.deletionResidue H.2 (T.affineEquiv 𝒜 x) :=
  T.transportAffineDevelopment_deletionResidue H.2 _

/-- The composite `ψ s` is `Φ_𝒜''`, on elements.

Blueprint: `thm:geo-affine`. -/
@[simp]
theorem residueComparison_restrictionToCokernel (x : OSAlgebra B (𝒜.restriction H)) :
    T.residueComparison H (restrictionToCokernel B 𝒜 H x) = T.affineEquiv (𝒜.restriction H) x :=
  congrArg (T.pull _) (T.toAlgebraic.residueComparison_restrictionToCokernel H x)

/-- The map `ψ` is bijective.

Blueprint: `thm:geo-affine`. -/
theorem bijective_residueComparison : Function.Bijective (T.residueComparison H) :=
  (transportAffineDevelopment T _).bijective.comp (T.toAlgebraic.bijective_residueComparison H)

include T in
/-- The deletion algebra map `a : OS_B(𝒜') → OS_B(𝒜)` is injective. This statement about the
presentation follows from any geometric theory with coefficients `B`, through `T.toAlgebraic`.

Blueprint: `thm:geo-affine`. -/
theorem injective_deletionMap : Function.Injective (deletionMap B 𝒜 H) :=
  T.toAlgebraic.injective_deletionMap H

include T in
/-- The linear map `s : OS_B(𝒜'') → OS_B(𝒜) / im a` is bijective. This statement about the
presentation follows from any geometric theory with coefficients `B`, through `T.toAlgebraic`.

Blueprint: `thm:geo-affine`. -/
theorem bijective_restrictionToCokernel : Function.Bijective (restrictionToCokernel B 𝒜 H) :=
  T.toAlgebraic.bijective_restrictionToCokernel H

end Deletion

/-! ### Compatibility with the existing theorem -/

section Compatibility

variable (E : OrlikSolomon.OrdinaryTheory.{u, v, w, z} k ℬ)

variable (𝒜) in
/-- **The two transports agree on the structure theorem.** For an algebraic theory `E`, the
geometric structure theorem of its transport `ofAlgebraic E` to smooth affine schemes is the
existing structure theorem of `E`, followed by `E` of the canonical isomorphism
`O(U_𝒜) ≅ Γ(U_𝒜, 𝒪)`, the unit of affine duality followed by global sections of `s_𝒜`. So the
transport rule produces no second, conflicting structure map. The proof is uniqueness on
generators.

Blueprint: `thm:geo-transport-all`, with `thm:geo-from-algebraic`. -/
theorem ofAlgebraic_affineEquiv (x : OSAlgebra B 𝒜) :
    (ofAlgebraic E).affineEquiv 𝒜 x =
      E.C.map ((smoothAffineUnitIso k).hom.app (SmoothAlg.complement 𝒜) ≫
          (affineGlobalSectionsFunctor k).map ((SmoothDomain.aff k).complementIsoSpec 𝒜).hom.op)
        (E.affineEquiv 𝒜 x) := by
  have h := (ofAlgebraic E).toAlgebraic.toAlgHom_affineEquiv_unique
    (fun H ↦ equation (H : AffineSubspace k V))
    (fun H ↦ isEquation_equation (𝒜.isHyperplane H.2))
    ((algebraicRoundTripEquiv E (SmoothAlg.complement 𝒜)).toAlgHom.comp
      (E.affineEquiv 𝒜 : OSAlgebra B 𝒜 →ₐ[B] E.C.obj (SmoothAlg.complement 𝒜)))
    fun H ↦ by
      change algebraicRoundTripEquiv E _ (E.affineEquiv 𝒜 (generator B 𝒜 H)) = _
      rw [E.affineEquiv_generator_of_isEquation H (isEquation_equation (𝒜.isHyperplane H.2))]
      exact algebraicRoundTripEquiv_logClass E _
  exact (congrArg ((ofAlgebraic E).pull _) (AlgHom.congr_fun h x).symm).trans (E.map_map _ _ _)

end Compatibility

end OrlikSolomon.Geometric.OrdinaryTheory
