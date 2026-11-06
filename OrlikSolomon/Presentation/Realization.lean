/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Cohomology.Deletion
public import OrlikSolomon.Geometry.RelationTargets
public import OrlikSolomon.Presentation.Grading

/-!
# The realization map

The logarithmic classes of the equations of the hyperplanes of `𝒜` satisfy the relations of the
Orlik–Solomon algebra, so `e_H ↦ [f_H]` defines an algebra map `Φ_𝒜 : OS_B(𝒜) → C(U_𝒜)`. This file
constructs it and proves what is known about it before the second induction: it preserves the
bigrading, it is surjective, it does not depend on the equations, and it is natural.

Both relations hold for the same reason. By `lem:small-targets`, the classes involved are pulled
back from the complement of an arrangement on a space of dimension smaller than their number, and
such a product vanishes there by the dimension bound of `thm:generation`. That bound holds for every
arrangement, so no comparison of the target with `𝒜` is needed: this is `word_logClass_eq_zero`,
which also makes no reference to `k`-points of `U_𝒜`.

## Main definitions

* `OrdinaryTheory.realization 𝒜`: the map `Φ_𝒜`. Its definition uses the chosen equations, which
  importers cannot see: use `realization_generator_of_isEquation` for any other equations.
* `OSAlgebra.comapHom`, `OSAlgebra.comapEquiv`: the algebra maps of a coordinate change, which send
  the generator of `K` to the generator of its preimage `K.comap e`. The corresponding isomorphism
  of complements is `SmoothAlg.complementIso`.

## Main results

* `lem:empty-relation`: `OrdinaryTheory.log_emptyRelation`,
  `OrdinaryTheory.log_emptyRelation_of_isEquation`.
* `lem:dependent-relation`: `OrdinaryTheory.log_dependentRelation`,
  `OrdinaryTheory.log_dependentRelation_of_isEquation`.
* `def:realization`: `OrdinaryTheory.realization`, with `OrdinaryTheory.realization_generator`,
  `OrdinaryTheory.realization_generator_zeroLocus`, `OrdinaryTheory.realization_word`, and
  `OrdinaryTheory.isHomogeneousOfShift_realization` for the bigrading.
* `lem:realization-basic`:
  - surjectivity: `OrdinaryTheory.surjective_realization`;
  - independence of the equations: `OrdinaryTheory.realization_generator_of_isEquation`,
    `OrdinaryTheory.realization_eq_lift`;
  - deletion and open pullback: `OrdinaryTheory.realization_comp_deletionMap`,
    `OrdinaryTheory.realization_deletionMap`, and `OrdinaryTheory.realization_map` for any
    sub-arrangement;
  - coordinate changes and relabeling: `OrdinaryTheory.realization_comp_comapEquiv`,
    `OrdinaryTheory.realization_comapEquiv`, and `OrdinaryTheory.realization_comapHom`.

## How later modules use this file

* `lem:comparison-residue`: `deletionResidue_realization_deletionMap` says that `r Φ_𝒜` vanishes on
  the old image, and `deletionResidue_realization_generator_mul_word` computes it on a restricted
  word, for any representatives. Old generators restrict through
  `map_complementRestriction_realization_generator`, which is the statement that no scalar survives,
  and through its form `map_complementRestriction_realization_word` for words.
* `thm:affine`: `surjective_realization`, `isHomogeneousOfShift_realization`,
  `realization_toLinearMap_comp_deletionMap` for the square of `lem:comparison`, and
  `bijective_realization_empty` for the base case.
* `thm:projective`: `realization_generator_of_isEquation` for the linear forms of a cone, and
  `realization_generator_sub_generator` for a difference of two generators.

## Implementation notes

**The generator lemmas.** The formula for any equation `f` of `H` is
`realization_generator_of_isEquation`. Its right side mentions an `f` that its left side does not,
so it cannot fire as a bare `simp` lemma: give it the equation, as in
`simp [T.realization_generator_of_isEquation H hf]`. There are two `simp` lemmas.
`realization_generator_zeroLocus` fires on a label `⟨zeroLocus f, _⟩`, for any `f`, and gives `[f]`.
`realization_generator` fires on every other label, and gives the logarithm of the chosen equation.
Better, avoid equations altogether: `deletionResidue_realization_generator` and the lemmas after it
take none.

**What relabeling means here.** The label of a generator of `OS_B(𝒜)` is the hyperplane itself,
so a relabeling that preserves hyperplanes is an equality `𝒜 = 𝒟`, for which `realization_map` with
`h.le` is the naturality. The content is in a relabeling along an affine equivalence `e : W ≃ V`, a
bijection between the hyperplanes of `𝒜` and those of `𝒟` that sends each `K` to `K.comap e`, and
this is what `comapEquiv` takes. It also covers a coordinate change, at `𝒟 = 𝒜.comap e`
(`comap_mem_comap_affineEquiv`), and an equality, at `e = AffineEquiv.refl k V`.

**The auxiliary coordinate choices.** The blueprint's proof mentions independence of the coordinate
choices in the restriction geometry. The library makes one choice, the base point inside `chart H`,
which is `@[no_expose]`, so no statement here can tell which point it is. Any other base point
differs from it by a translation of `H.direction`, which is an affine equivalence, so
`realization_comapEquiv` compares the two.

**Other affine maps.** Here only an affine equivalence induces a map of presentations, since that is
what the blueprint asks for and what preserves intersections and codimensions. For a general affine
map `φ`, `map_complementMap_realization_generator` and
`map_complementMap_realization_generator_of_comap_eq_bot` still describe what `φ` does to a single
generator.

## Blueprint

`lem:empty-relation`, `lem:dependent-relation`, `def:realization`, `lem:realization-basic`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement

universe u v w z

namespace OrlikSolomon

/-! ### Homogeneous algebra maps out of the presentation -/

namespace OSAlgebra

section Homogeneous

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  {R B S : Type*} [CommRing R] [CommRing B] [Algebra R B] [Ring S] [Algebra R S] [Algebra B S]
  [IsScalarTower R B S] {𝒜 : Arrangement k V} {ℬ : ℤ → Submodule R B}
  {𝒮 : ℤ × ℤ → Submodule R S} [SetLike.GradedMonoid 𝒮]

/-- An algebra map out of the presentation preserves the bigrading as soon as it does so on the
coefficients and on the generators. A generator has bidegree `(1, 1)` and a coefficient of weight
`w` has bidegree `(0, w)`, and these determine the bigrading.

Blueprint: `def:realization`, `lem:os-basic`. -/
theorem isHomogeneousOfShift_of_generator_mem (φ : OSAlgebra B 𝒜 →ₐ[B] S)
    (hb : ∀ ⦃w : ℤ⦄ ⦃b : B⦄, b ∈ ℬ w → algebraMap B S b ∈ 𝒮 (0, w))
    (hg : ∀ H, φ (generator B 𝒜 H) ∈ 𝒮 (1, 1)) :
    IsHomogeneousOfShift (bigrading 𝒜 ℬ) 𝒮 0 φ := by
  have hw (I : List 𝒜) : φ (word (generator B 𝒜) I) ∈ 𝒮 ((I.length : ℤ), (I.length : ℤ)) := by
    induction I with
    | nil =>
      have h : (1 : S) ∈ 𝒮 (0, 0) := SetLike.GradedOne.one_mem
      simpa using h
    | cons H I ih =>
      have h := SetLike.GradedMul.mul_mem (hg H) ih
      simpa [add_comm] using h
  refine isHomogeneousOfShift_zero_iff.2 ?_
  rintro ⟨p, w⟩ x hx
  obtain hp | hp := lt_or_ge p 0
  · rw [bigrading_eq_bot_of_fst_neg 𝒜 ℬ hp, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _
  · lift p to ℕ using hp
    rw [bigrading_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb', I, rfl, rfl⟩ := hy
      have h := SetLike.GradedMul.mul_mem (hb hb') (hw I)
      rw [map_smul, Algebra.smul_def]
      simpa using h
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
    | smul r x _ hx =>
      rw [← algebraMap_smul B r x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ r hx

end Homogeneous

end OSAlgebra

/-! ### Coordinate changes of the presentation -/

section CoordinateChange

variable {k : Type u} [Field k] {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- A relabeling along an affine equivalence preserves the guarded dependence of a list. -/
theorem Arrangement.isDependent_map_of_forall_coe_eq_comap {𝒜 : Arrangement k V}
    {𝒟 : Arrangement k W} (e : W ≃ᵃ[k] V) {σ : 𝒜 → 𝒟}
    (hσ : ∀ K, (σ K : AffineSubspace k W) = (K : AffineSubspace k V).comap (e : W →ᵃ[k] V))
    (I : List 𝒜) : IsDependent (I.map σ) ↔ IsDependent I := by
  simp only [IsDependent, inter_map_of_forall_coe_eq_comap hσ, List.length_map, Ne,
    comap_affineEquiv_eq_bot_iff, codim_comap_affineEquiv]

namespace OSAlgebra

variable (B : Type v) [CommRing B] {𝒜 : Arrangement k V} {𝒟 : Arrangement k W}

/-- The generators of the preimages of the hyperplanes of `𝒜` under an affine equivalence satisfy
the relations of `𝒜`, because the equivalence preserves intersections and codimensions. -/
theorem isFamily_comap (e : W ≃ᵃ[k] V) (h : ∀ K ∈ 𝒜, K.comap (e : W →ᵃ[k] V) ∈ 𝒟) :
    IsFamily 𝒜 fun K ↦ generator B 𝒟 ⟨_, h K K.2⟩ where
  toIsExteriorFamily := (isExteriorFamily_generator B 𝒟).comp _
  word_eq_zero I _ hI := by
    rw [← word_map]
    refine word_eq_zero_of_inter_eq_bot B 𝒟 ?_
    rw [inter_map_of_forall_coe_eq_comap (φ := (e : W →ᵃ[k] V)) (fun _ ↦ rfl), hI,
      AffineSubspace.comap_bot]
  wordBoundary_eq_zero I _ hI := by
    rw [← wordBoundary_map]
    exact wordBoundary_eq_zero_of_isDependent B 𝒟
      ((isDependent_map_of_forall_coe_eq_comap e (fun _ ↦ rfl) I).2 hI)

/-- The algebra map of an affine equivalence `e : W ≃ V` that sends the hyperplanes of `𝒜` into
those of `𝒟`: it sends the generator of `K` to the generator of `K.comap e`.

Blueprint: `lem:realization-basic`. -/
def comapHom (e : W ≃ᵃ[k] V) (h : ∀ K ∈ 𝒜, K.comap (e : W →ᵃ[k] V) ∈ 𝒟) :
    OSAlgebra B 𝒜 →ₐ[B] OSAlgebra B 𝒟 :=
  lift _ (isFamily_comap B e h)

/-- `comapHom` sends the generator of `K` to the generator of `K.comap e`. -/
@[simp]
theorem comapHom_generator (e : W ≃ᵃ[k] V) (h : ∀ K ∈ 𝒜, K.comap (e : W →ᵃ[k] V) ∈ 𝒟) (K : 𝒜) :
    comapHom B e h (generator B 𝒜 K) = generator B 𝒟 ⟨_, h K K.2⟩ :=
  lift_generator _ _ K

/-- The generator formula of `comapHom`, with the label of the target given separately. -/
theorem comapHom_generator_of_comap_eq (e : W ≃ᵃ[k] V)
    (h : ∀ K ∈ 𝒜, K.comap (e : W →ᵃ[k] V) ∈ 𝒟) (K : 𝒜) (L : 𝒟)
    (hKL : (K : AffineSubspace k V).comap (e : W →ᵃ[k] V) = L) :
    comapHom B e h (generator B 𝒜 K) = generator B 𝒟 L := by
  rw [comapHom_generator]
  exact congrArg (generator B 𝒟) (Subtype.ext hKL)

/-- `comapHom` preserves the weighted bigrading. -/
theorem isHomogeneousOfShift_comapHom {R : Type*} [CommRing R] [Algebra R B]
    (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] (e : W ≃ᵃ[k] V)
    (h : ∀ K ∈ 𝒜, K.comap (e : W →ᵃ[k] V) ∈ 𝒟) :
    IsHomogeneousOfShift (bigrading 𝒜 ℬ) (bigrading 𝒟 ℬ) 0 (comapHom B e h) :=
  isHomogeneousOfShift_of_generator_mem _ (fun _ _ hb ↦ algebraMap_mem_bigrading 𝒟 ℬ hb)
    fun K ↦ by simpa using generator_mem_bigrading 𝒟 ℬ _

/-- The algebra equivalence of a relabeling along an affine equivalence `e : W ≃ V`, for which `K`
is a hyperplane of `𝒜` exactly when `K.comap e` is a hyperplane of `𝒟`. It sends the generator of
`K` to the generator of `K.comap e`.

This covers an affine coordinate change, with `𝒟 = 𝒜.comap e`, by `comap_mem_comap_affineEquiv`, and
an equality `𝒜 = 𝒟`, with `e = AffineEquiv.refl k V`.

Blueprint: `lem:realization-basic`. -/
def comapEquiv (e : W ≃ᵃ[k] V) (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ 𝒟) :
    OSAlgebra B 𝒜 ≃ₐ[B] OSAlgebra B 𝒟 :=
  AlgEquiv.ofAlgHom (comapHom B e fun K ↦ (h K).1)
    (comapHom B e.symm fun L hL ↦ (h _).2 (by rwa [comap_symm_comap]))
    (algHom_ext fun L ↦ by
      simp only [AlgHom.comp_apply, comapHom_generator, AlgHom.id_apply]
      exact congrArg (generator B 𝒟) (Subtype.ext (comap_symm_comap e _)))
    (algHom_ext fun K ↦ by
      simp only [AlgHom.comp_apply, comapHom_generator, AlgHom.id_apply]
      exact congrArg (generator B 𝒜) (Subtype.ext (comap_comap_symm e _)))

/-- `comapEquiv` sends the generator of `K` to the generator of `K.comap e`. -/
@[simp]
theorem comapEquiv_generator (e : W ≃ᵃ[k] V) (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ 𝒟)
    (K : 𝒜) : comapEquiv B e h (generator B 𝒜 K) = generator B 𝒟 ⟨_, (h K).1 K.2⟩ :=
  comapHom_generator B e (fun K ↦ (h K).1) K

/-- `comapEquiv` is `comapHom`, as a function. -/
theorem coe_comapEquiv (e : W ≃ᵃ[k] V) (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ 𝒟) :
    ⇑(comapEquiv B e h) = comapHom B e fun K ↦ (h K).1 :=
  rfl

end OSAlgebra

end CoordinateChange

namespace OrdinaryTheory

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {𝒜 : Arrangement k V} {f g : V →ᵃ[k] k}

/-! ### The relations -/

section Relations

/-- The word of logarithmic classes of a list of units with a `RelationTarget` vanishes: it is
pulled back from a product of more classes than the dimension of the target, which vanishes by the
dimension bound of `thm:generation`. This is the common proof of both relations.

Blueprint: `lem:empty-relation`, `lem:dependent-relation`. -/
theorem word_logClass_eq_zero {us : List (complement 𝒜)ˣ} (t : RelationTarget 𝒜 us) :
    word T.logClass us = 0 := by
  have h : word T.logClass t.units = 0 :=
    T.eq_zero_of_mem_grading_of_finrank_lt t.arrangement
      (by exact_mod_cast t.finrank_lt_length_units) (T.word_logClass_mem_grading id t.units)
  rw [← t.map_units, word_map]
  simpa [map_word] using congr(T.C.map t.map $h)

/-- If the hyperplanes of a list have empty intersection, the product of the logarithms of their
chosen equations vanishes. `log_emptyRelation_of_isEquation` is the same for any equations.

Blueprint: `lem:empty-relation`. -/
theorem log_emptyRelation (I : List 𝒜) (h : inter I = ⊥) : T.logMonomial 𝒜 I = 0 := by
  rw [logMonomial, ← word_map (T.logClass) (equationUnit 𝒜) I]
  exact T.word_logClass_eq_zero (.ofInterEqBot I h)

/-- If a list of hyperplanes is dependent, that is, has nonempty intersection of codimension less
than its length, then the boundary of the logarithms of their chosen equations vanishes.
`log_dependentRelation_of_isEquation` is the same for any equations.

Blueprint: `lem:dependent-relation`. -/
theorem log_dependentRelation {I : List 𝒜} (h : IsDependent I) :
    wordBoundary (fun H ↦ T.logClass (equationUnit 𝒜 H)) I = 0 := by
  obtain _ | ⟨H₀, J⟩ := I
  · exact absurd h (isDependent_nil 𝒜)
  rw [← (T.isExteriorFamily_logClass _).word_sub_eq_wordBoundary_cons]
  simpa [word_map] using T.word_logClass_eq_zero (.ofDependent H₀ J h.1 h.2)

/-- The logarithm of an equation of a hyperplane does not depend on the equation, as a family: any
choice of one equation for each hyperplane of `𝒜` has the logarithms of the chosen equations.

Blueprint: `lem:realization-basic`. -/
theorem logClass_complementUnit_family (F : 𝒜 → V →ᵃ[k] k)
    (hF : ∀ H : 𝒜, IsEquation (F H) H) :
    (fun H : 𝒜 ↦ T.logClass (complementUnit 𝒜 (F H) ((hF H).covers H.2))) =
      fun H ↦ T.logClass (equationUnit 𝒜 H) :=
  funext fun H ↦ T.logClass_complementUnit_eq_logClass_equationUnit H.2 (hF H)

/-- `lem:empty-relation`, for any choice of equations.

Blueprint: `lem:empty-relation`. -/
theorem log_emptyRelation_of_isEquation (F : 𝒜 → V →ᵃ[k] k) (hF : ∀ H : 𝒜, IsEquation (F H) H)
    (I : List 𝒜) (h : inter I = ⊥) :
    word (fun H : 𝒜 ↦ T.logClass (complementUnit 𝒜 (F H) ((hF H).covers H.2))) I = 0 := by
  rw [T.logClass_complementUnit_family F hF]
  exact T.log_emptyRelation I h

/-- `lem:dependent-relation`, for any choice of equations.

Blueprint: `lem:dependent-relation`. -/
theorem log_dependentRelation_of_isEquation (F : 𝒜 → V →ᵃ[k] k)
    (hF : ∀ H : 𝒜, IsEquation (F H) H) {I : List 𝒜} (h : IsDependent I) :
    wordBoundary (fun H : 𝒜 ↦ T.logClass (complementUnit 𝒜 (F H) ((hF H).covers H.2))) I = 0 := by
  rw [T.logClass_complementUnit_family F hF]
  exact T.log_dependentRelation h

variable (𝒜) in
/-- The logarithms of the chosen equations satisfy the relations of the presentation. -/
theorem isFamily_logClass_equationUnit :
    OSAlgebra.IsFamily 𝒜 fun H ↦ T.logClass (equationUnit 𝒜 H) where
  toIsExteriorFamily := T.isExteriorFamily_logClass _
  word_eq_zero I _ h := T.log_emptyRelation I h
  wordBoundary_eq_zero _ _ h := T.log_dependentRelation h

/-- The logarithms of any choice of equations satisfy the relations of the presentation. -/
theorem isFamily_logClass_complementUnit (F : 𝒜 → V →ᵃ[k] k)
    (hF : ∀ H : 𝒜, IsEquation (F H) H) :
    OSAlgebra.IsFamily 𝒜 fun H ↦ T.logClass (complementUnit 𝒜 (F H) ((hF H).covers H.2)) := by
  rw [T.logClass_complementUnit_family F hF]
  exact T.isFamily_logClass_equationUnit 𝒜

end Relations

/-! ### The realization map -/

section Realization

variable (𝒜) in
/-- The canonical realization map `Φ_𝒜 : OS_B(𝒜) → C(U_𝒜)`, the algebra map sending the generator
`e_H` to the logarithm `[f_H]` of an equation of `H`. It exists by the universal property of the
presentation and the two relation lemmas.

It does not depend on the equations: see `realization_generator_of_isEquation` and
`realization_eq_lift`. It preserves the bigrading, by `isHomogeneousOfShift_realization`.

Blueprint: `def:realization`. -/
@[no_expose]
def realization : OSAlgebra B 𝒜 →ₐ[B] T.C.obj (complement 𝒜) :=
  OSAlgebra.lift _ (T.isFamily_logClass_equationUnit 𝒜)

/-- The realization map sends a generator to the logarithm of the chosen equation of its hyperplane.
`realization_generator_of_isEquation` is the same formula for any equation.

Blueprint: `def:realization`. -/
@[simp]
theorem realization_generator (H : 𝒜) :
    T.realization 𝒜 (OSAlgebra.generator B 𝒜 H) = T.logClass (equationUnit 𝒜 H) :=
  OSAlgebra.lift_generator _ _ H

/-- The realization map sends a generator to the logarithm of **any** equation of its hyperplane.
Since `f` is not on the left, `simp` needs the equation to be given, as in
`simp [T.realization_generator_of_isEquation H hf]`.

Blueprint: `def:realization`, `lem:realization-basic`. -/
theorem realization_generator_of_isEquation (H : 𝒜) (hf : IsEquation f H) :
    T.realization 𝒜 (OSAlgebra.generator B 𝒜 H) =
      T.logClass (complementUnit 𝒜 f (hf.covers H.2)) :=
  (T.realization_generator H).trans (T.logClass_complementUnit_eq_logClass_equationUnit H.2 hf).symm

/-- The generator formula for a label presented by an equation: if the zero locus of `f` is a
hyperplane of `𝒜`, then the generator of that hyperplane goes to `[f]`. Here `f` is on the left, so
`simp` uses this with no further input, for any equation. It takes priority over
`realization_generator`, which would replace `f` by the chosen equation.

Blueprint: `def:realization`, `lem:realization-basic`. -/
@[simp high]
theorem realization_generator_zeroLocus (hf : zeroLocus f ∈ 𝒜) :
    T.realization 𝒜 (OSAlgebra.generator B 𝒜 ⟨zeroLocus f, hf⟩) =
      T.logClass (complementUnit 𝒜 f (.of_mem hf)) :=
  T.realization_generator_of_isEquation _ (isEquation_of_zeroLocus_mem hf)

/-- The realization map sends a word in the generators to the logarithmic monomial of the word. It
takes priority over `map_word`, which would leave a word in logarithms. -/
@[simp high]
theorem realization_word (I : List 𝒜) :
    T.realization 𝒜 (word (OSAlgebra.generator B 𝒜) I) = T.logMonomial 𝒜 I := by
  simp [logMonomial]

/-- The realization map sends a boundary of generators to the boundary of the logarithms. -/
theorem realization_wordBoundary (I : List 𝒜) :
    T.realization 𝒜 (wordBoundary (OSAlgebra.generator B 𝒜) I) =
      wordBoundary (fun H ↦ T.logClass (equationUnit 𝒜 H)) I := by
  simp

/-- The difference of two generators goes to the logarithm of the quotient of any of their
equations, as in `thm:projective`. -/
theorem realization_generator_sub_generator (H K : 𝒜) (hf : IsEquation f H) (hg : IsEquation g K) :
    T.realization 𝒜 (OSAlgebra.generator B 𝒜 H - OSAlgebra.generator B 𝒜 K) =
      T.logClass (complementUnit 𝒜 f (hf.covers H.2) / complementUnit 𝒜 g (hg.covers K.2)) := by
  rw [map_sub, T.realization_generator_of_isEquation H hf,
    T.realization_generator_of_isEquation K hg, logClass_div]

/-- The realization map is the lift of the logarithms of **any** choice of equations, so it does not
depend on the equations.

Blueprint: `lem:realization-basic`. -/
theorem realization_eq_lift (F : 𝒜 → V →ᵃ[k] k) (hF : ∀ H : 𝒜, IsEquation (F H) H) :
    T.realization 𝒜 = OSAlgebra.lift _ (T.isFamily_logClass_complementUnit F hF) :=
  OSAlgebra.algHom_ext fun H ↦ by
    rw [OSAlgebra.lift_generator, T.realization_generator_of_isEquation H (hF H)]

/-- The realization map preserves the bigrading of the presentation, with `e_H` in bidegree `(1, 1)`
and `B_w` in bidegree `(0, w)`.

Blueprint: `def:realization`. -/
theorem isHomogeneousOfShift_realization :
    IsHomogeneousOfShift (OSAlgebra.bigrading 𝒜 ℬ) (T.grading (complement 𝒜)) 0
      (T.realization 𝒜) :=
  OSAlgebra.isHomogeneousOfShift_of_generator_mem _ (fun _ _ hb ↦ T.algebraMap_mem_grading _ hb)
    fun H ↦ by simpa using T.logClass_mem_grading (equationUnit 𝒜 H)

/-- The realization map preserves the bigrading, for one element.

Blueprint: `def:realization`. -/
theorem realization_mem_grading {i : ℤ × ℤ} {x : OSAlgebra B 𝒜}
    (hx : x ∈ OSAlgebra.bigrading 𝒜 ℬ i) : T.realization 𝒜 x ∈ T.grading (complement 𝒜) i :=
  isHomogeneousOfShift_zero_iff.1 T.isHomogeneousOfShift_realization hx

variable (𝒜) in
/-- The realization map is surjective, because logarithmic monomials span by `thm:generation`.

Blueprint: `lem:realization-basic`. -/
theorem surjective_realization : Function.Surjective (T.realization 𝒜) := by
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, eq_top_iff, ← T.generated 𝒜,
    Submodule.span_le]
  rintro _ ⟨I, rfl⟩
  exact ⟨_, T.realization_word I⟩

variable (V) in
/-- The realization map of the empty arrangement is bijective, since both sides are the coefficient
ring. This is the base case of `thm:affine`. -/
theorem bijective_realization_empty :
    Function.Bijective (T.realization (∅ : Arrangement k V)) := by
  have h : ⇑(T.realization (∅ : Arrangement k V)) =
      algebraMap B _ ∘ OSAlgebra.emptyEquiv B (k := k) (V := V) := by
    funext x
    obtain ⟨b, rfl⟩ := (OSAlgebra.emptyEquiv B (k := k) (V := V)).symm.surjective x
    have hb : (OSAlgebra.emptyEquiv B (k := k) (V := V)).symm b =
        algebraMap B (OSAlgebra B (∅ : Arrangement k V)) b := rfl
    simp [hb]
  rw [h]
  exact (T.bijective_algebraMap_complement_empty V).comp (OSAlgebra.emptyEquiv B).bijective

end Realization

/-! ### Open pullback and deletion -/

section Inclusion

variable {𝒟 : Arrangement k V}

/-- The realization map commutes with an inclusion of arrangements and the open pullback. For a
relabeling that preserves hyperplanes, an equality `𝒜 = 𝒟`, take `h.le`.

Blueprint: `lem:realization-basic`. -/
theorem realization_comp_map (h : 𝒜 ≤ 𝒟) :
    (T.realization 𝒟).comp (OSAlgebra.map B h) =
      (T.C.map (complementInclusion h)).hom.comp (T.realization 𝒜) :=
  OSAlgebra.algHom_ext fun K ↦ by
    simp

/-- The realization map commutes with an inclusion of arrangements and the open pullback. This
pulls a pullback out of the realization map, which is the direction that the residue lemmas use.

Blueprint: `lem:realization-basic`. -/
@[simp]
theorem realization_map (h : 𝒜 ≤ 𝒟) (x : OSAlgebra B 𝒜) :
    T.realization 𝒟 (OSAlgebra.map B h x) =
      T.C.map (complementInclusion h) (T.realization 𝒜 x) :=
  DFunLike.congr_fun (T.realization_comp_map h) x

variable (𝒜) in
/-- The square of the deletion algebra map and the open pullback.

Blueprint: `lem:realization-basic`. -/
theorem realization_comp_deletionMap (H : AffineSubspace k V) :
    (T.realization 𝒜).comp (OSAlgebra.deletionMap B 𝒜 H) =
      (T.C.map (complementInclusion (𝒜.deletion_le H))).hom.comp (T.realization (𝒜.deletion H)) :=
  T.realization_comp_map (𝒜.deletion_le H)

variable (𝒜) in
/-- The square of the deletion algebra map and the open pullback, for one element.

Blueprint: `lem:realization-basic`. -/
@[simp]
theorem realization_deletionMap (H : AffineSubspace k V) (x : OSAlgebra B (𝒜.deletion H)) :
    T.realization 𝒜 (OSAlgebra.deletionMap B 𝒜 H x) =
      T.C.map (complementInclusion (𝒜.deletion_le H)) (T.realization (𝒜.deletion H) x) :=
  T.realization_map (𝒜.deletion_le H) x

variable (𝒜) in
/-- The square of the deletion algebra map and the open pullback, as linear maps, as in the
hypothesis of `lem:comparison`.

Blueprint: `lem:realization-basic`, `thm:affine`. -/
theorem realization_toLinearMap_comp_deletionMap (H : AffineSubspace k V) :
    (T.realization 𝒜).toLinearMap ∘ₗ (OSAlgebra.deletionMap B 𝒜 H).toLinearMap =
      (T.C.map (complementInclusion (𝒜.deletion_le H))).hom.toLinearMap ∘ₗ
        (T.realization (𝒜.deletion H)).toLinearMap :=
  LinearMap.ext fun x ↦ T.realization_deletionMap 𝒜 H x

end Inclusion

/-! ### Affine maps and coordinate changes -/

section AffineMaps

variable {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {𝒟 : Arrangement k W}

/-- The pullback along an affine map `φ` of the logarithm of `K` is the logarithm of its preimage,
when this preimage is a hyperplane `L` of the target. No scalar survives. -/
theorem map_complementMap_realization_generator (φ : W →ᵃ[k] V)
    (h : ∀ K ∈ 𝒜, 𝒟.Covers (K.comap φ)) (K : 𝒜) (L : 𝒟)
    (hKL : (K : AffineSubspace k V).comap φ = L) :
    T.C.map (complementMap φ 𝒜 𝒟 h) (T.realization 𝒜 (OSAlgebra.generator B 𝒜 K)) =
      T.realization 𝒟 (OSAlgebra.generator B 𝒟 L) := by
  have hf := isEquation_equation (𝒜.isHyperplane K.2)
  have hg : IsEquation ((equation (K : AffineSubspace k V)).comp φ) (L : AffineSubspace k W) :=
    hKL ▸ hf.comp φ (hKL ▸ 𝒟.isHyperplane L.2)
  rw [T.realization_generator_of_isEquation K hf, T.map_logClass,
    mapUnits_complementMap_complementUnit, T.realization_generator_of_isEquation L hg]

/-- The pullback along an affine map `φ` of the logarithm of `K` vanishes, when the preimage of `K`
is empty, since an equation of `K` then pulls back to a nonzero constant. -/
theorem map_complementMap_realization_generator_of_comap_eq_bot (φ : W →ᵃ[k] V)
    (h : ∀ K ∈ 𝒜, 𝒟.Covers (K.comap φ)) (K : 𝒜)
    (hK : (K : AffineSubspace k V).comap φ = ⊥) :
    T.C.map (complementMap φ 𝒜 𝒟 h) (T.realization 𝒜 (OSAlgebra.generator B 𝒜 K)) = 0 := by
  have hf := isEquation_equation (𝒜.isHyperplane K.2)
  obtain ⟨c, hc⟩ := zeroLocus_eq_bot_iff.1
    (show zeroLocus ((equation (K : AffineSubspace k V)).comp φ) = ⊥ by
      rw [zeroLocus_comp, hf.zeroLocus_eq, hK])
  rw [T.realization_generator_of_isEquation K hf, T.map_logClass,
    mapUnits_complementMap_complementUnit]
  simp only [hc, complementUnit_const]
  exact T.logClass_units_map_algebraMap c

/-- The realization map commutes with an affine equivalence that sends the hyperplanes of `𝒜` into
those of `𝒟`.

Blueprint: `lem:realization-basic`. -/
@[simp]
theorem realization_comapHom (e : W ≃ᵃ[k] V) (h : ∀ K ∈ 𝒜, K.comap (e : W →ᵃ[k] V) ∈ 𝒟)
    (x : OSAlgebra B 𝒜) :
    T.realization 𝒟 (OSAlgebra.comapHom B e h x) =
      T.C.map (complementMap (e : W →ᵃ[k] V) 𝒜 𝒟 fun K hK ↦ .of_mem (h K hK))
        (T.realization 𝒜 x) := by
  have hext : (T.realization 𝒟).comp (OSAlgebra.comapHom B e h) =
      (T.C.map (complementMap (e : W →ᵃ[k] V) 𝒜 𝒟 fun K hK ↦ .of_mem (h K hK))).hom.comp
        (T.realization 𝒜) :=
    OSAlgebra.algHom_ext fun K ↦
      (congrArg _ (OSAlgebra.comapHom_generator B e h K)).trans
        (T.map_complementMap_realization_generator _ _ K ⟨_, h K K.2⟩ rfl).symm
  exact DFunLike.congr_fun hext x

/-- The square of a relabeling along an affine equivalence, which includes an affine coordinate
change, and the isomorphism of complements.

Blueprint: `lem:realization-basic`. -/
theorem realization_comp_comapEquiv (e : W ≃ᵃ[k] V)
    (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ 𝒟) :
    (T.realization 𝒟).comp (OSAlgebra.comapEquiv B e h).toAlgHom =
      (T.C.map (complementIso 𝒜 𝒟 e h).hom).hom.comp (T.realization 𝒜) :=
  AlgHom.ext fun x ↦ T.realization_comapHom e (fun K ↦ (h K).1) x

/-- The square of a relabeling along an affine equivalence, which includes an affine coordinate
change, and the isomorphism of complements, for one element.

Blueprint: `lem:realization-basic`. -/
@[simp]
theorem realization_comapEquiv (e : W ≃ᵃ[k] V)
    (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ 𝒟) (x : OSAlgebra B 𝒜) :
    T.realization 𝒟 (OSAlgebra.comapEquiv B e h x) =
      T.C.map (complementIso 𝒜 𝒟 e h).hom (T.realization 𝒜 x) :=
  T.realization_comapHom e (fun K ↦ (h K).1) x

end AffineMaps

/-! ### Restriction and residue: the input of the second induction -/

section Restriction

variable {H : AffineSubspace k V}

/-- An old generator restricts to the generator of its retained hyperplane. The equation of the old
hyperplane restricts to a nonzero constant times the equation of the retained one, and this constant
has zero logarithm, so no scalar survives.

Blueprint: `lem:comparison-residue`. -/
theorem map_complementRestriction_realization_generator (hH : IsHyperplane H)
    (K : 𝒜.deletion H) (L : 𝒜.restriction H)
    (hKL : (K : AffineSubspace k V).comap (chart H) = L) :
    T.C.map (complementRestriction 𝒜 hH)
        (T.realization (𝒜.deletion H) (OSAlgebra.generator B _ K)) =
      T.realization (𝒜.restriction H) (OSAlgebra.generator B _ L) :=
  T.map_complementMap_realization_generator (chart H) _ K L hKL

/-- An old generator with empty trace on `H` restricts to zero.

Blueprint: `lem:comparison-residue`. -/
theorem map_complementRestriction_realization_generator_of_inf_eq_bot (hH : IsHyperplane H)
    (K : 𝒜.deletion H) (hK : H ⊓ K = ⊥) :
    T.C.map (complementRestriction 𝒜 hH)
        (T.realization (𝒜.deletion H) (OSAlgebra.generator B _ K)) = 0 :=
  T.map_complementMap_realization_generator_of_comap_eq_bot (chart H) _ K
    ((comap_chart_eq_bot_iff hH.ne_bot).2 hK)

/-- Two old generators with the same trace on `H` have the same restriction. -/
theorem map_complementRestriction_realization_generator_of_inf_eq (hH : IsHyperplane H)
    (K K' : 𝒜.deletion H) (hK : H ⊓ K = H ⊓ K') :
    T.C.map (complementRestriction 𝒜 hH)
        (T.realization (𝒜.deletion H) (OSAlgebra.generator B _ K)) =
      T.C.map (complementRestriction 𝒜 hH)
        (T.realization (𝒜.deletion H) (OSAlgebra.generator B _ K')) := by
  have hf := isEquation_equation ((𝒜.deletion H).isHyperplane K.2)
  have hg := isEquation_equation ((𝒜.deletion H).isHyperplane K'.2)
  rw [T.realization_generator_of_isEquation K hf, T.realization_generator_of_isEquation K' hg]
  exact T.map_complementRestriction_logClass_of_inf_eq hH K.2 K'.2 hf hg hK

/-- A word in old generators representing retained hyperplanes restricts to the word in those
hyperplanes, for any choice `r` of representatives.

Blueprint: `lem:comparison-residue`. -/
theorem map_complementRestriction_realization_word (hH : IsHyperplane H)
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart H) = L) (I : List (𝒜.restriction H)) :
    T.C.map (complementRestriction 𝒜 hH)
        (T.realization (𝒜.deletion H) (word (fun L ↦ OSAlgebra.generator B _ (r L)) I)) =
      T.realization (𝒜.restriction H) (word (OSAlgebra.generator B _) I) := by
  induction I with
  | nil => simp
  | cons L I ih =>
    simp only [word_cons, map_mul, ih,
      T.map_complementRestriction_realization_generator hH (r L) L (hr L)]

/-- The residue of the realization of the generator of `H` is `1`.

Blueprint: `lem:comparison-residue`. -/
theorem deletionResidue_realization_generator (hH : H ∈ 𝒜) :
    T.deletionResidue hH (T.realization 𝒜 (OSAlgebra.generator B 𝒜 ⟨H, hH⟩)) = 1 := by
  simp

/-- `r Φ_𝒜` vanishes on the old image.

Blueprint: `lem:comparison-residue`. -/
theorem deletionResidue_realization_deletionMap (hH : H ∈ 𝒜) (x : OSAlgebra B (𝒜.deletion H)) :
    T.deletionResidue hH (T.realization 𝒜 (OSAlgebra.deletionMap B 𝒜 H x)) = 0 := by
  simp

/-- The residue formula on the realization map: the residue of `e_H a(x)` is the restriction of
`Φ_𝒜' x`. The generator `e_H` must stay on the left.

Blueprint: `lem:comparison-residue`. -/
theorem deletionResidue_realization_generator_mul_deletionMap (hH : H ∈ 𝒜)
    (x : OSAlgebra B (𝒜.deletion H)) :
    T.deletionResidue hH (T.realization 𝒜
        (OSAlgebra.generator B 𝒜 ⟨H, hH⟩ * OSAlgebra.deletionMap B 𝒜 H x)) =
      T.C.map (complementRestriction 𝒜 (𝒜.isHyperplane hH)) (T.realization (𝒜.deletion H) x) := by
  simp

/-- The residue of the realization of a word `e_H e_{K₁} ⋯ e_{Kₜ}` in representatives of retained
hyperplanes `L₁, …, Lₜ` is the realization of `e_{L₁} ⋯ e_{Lₜ}`. This is the computation in
`lem:comparison-residue`, and it holds for any choice `r` of representatives.

Blueprint: `lem:comparison-residue`. -/
theorem deletionResidue_realization_generator_mul_word (hH : H ∈ 𝒜)
    (r : 𝒜.restriction H → 𝒜.deletion H)
    (hr : ∀ L, (r L : AffineSubspace k V).comap (chart H) = L) (I : List (𝒜.restriction H)) :
    T.deletionResidue hH (T.realization 𝒜 (OSAlgebra.generator B 𝒜 ⟨H, hH⟩ *
        OSAlgebra.deletionMap B 𝒜 H (word (fun L ↦ OSAlgebra.generator B _ (r L)) I))) =
      T.realization (𝒜.restriction H) (word (OSAlgebra.generator B _) I) := by
  rw [deletionResidue_realization_generator_mul_deletionMap,
    T.map_complementRestriction_realization_word _ r hr]

end Restriction

end OrdinaryTheory

end OrlikSolomon
