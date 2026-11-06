/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import OrlikSolomon.Algebra.ExteriorBoundary
public import OrlikSolomon.Algebra.RelationQuotient
public import OrlikSolomon.Geometry.Arrangement

/-!
# The affine Orlik–Solomon algebra

`OSAlgebra B 𝒜` is the exterior algebra on the hyperplanes of `𝒜`, modulo the products for
empty intersections and the signed boundaries for nonempty dependent intersections.
`Arrangement.IsDependent` includes the nonempty-intersection guard: the numerical convention
for `codim ⊥` must never create a boundary relation.

The quotient map, generators, word spanning, and the universal property `OSAlgebra.lift`
are the public interface. Inclusions of arrangements induce algebra maps, including the
deletion map. The exterior grading descends to an internal grading by natural numbers.

Blueprint: `def:os`, the deletion map and ordinary grading of `lem:os-basic`.
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

namespace Arrangement

/-- A family of hyperplanes is dependent when its intersection is nonempty and has codimension
less than the number of letters. Repeated letters are allowed in this predicate; the presentation
uses it only on lists without repetitions.

Blueprint: the guarded boundary relation in `def:os`. -/
def IsDependent {𝒜 : Arrangement k V} (I : List 𝒜) : Prop :=
  inter I ≠ ⊥ ∧ codim (inter I) < I.length

@[simp]
theorem isDependent_nil (𝒜 : Arrangement k V) : ¬ IsDependent ([] : List 𝒜) := by
  simp [IsDependent]

/-- A family with empty intersection is never a dependent family in the affine presentation. -/
theorem not_isDependent_of_inter_eq_bot {𝒜 : Arrangement k V} {I : List 𝒜}
    (h : inter I = ⊥) : ¬ IsDependent I :=
  fun hI ↦ hI.1 h

@[simp]
theorem isDependent_map_inclusion {𝒜 ℬ : Arrangement k V} (h : 𝒜 ≤ ℬ) (I : List 𝒜) :
    IsDependent (I.map (inclusion h)) ↔ IsDependent I := by
  simp only [IsDependent, inter_map_inclusion, List.length_map]

end Arrangement

variable (B : Type v) [CommRing B] (𝒜 : Arrangement k V)

/-- The relators in the exterior algebra defining the affine Orlik–Solomon algebra. The first
family consists of products for empty intersections, and the second consists of boundaries for
nonempty dependent intersections. Both families use lists of distinct hyperplanes.

Blueprint: `def:os`. -/
def osRelations : Set (ExteriorAlgebra B (𝒜 →₀ B)) :=
  {r | ∃ I : List 𝒜, I.Nodup ∧
    (Arrangement.inter I = ⊥ ∧ r = word (exteriorGen B) I ∨
      Arrangement.IsDependent I ∧ r = wordBoundary (exteriorGen B) I)}

/-- Membership in the two families of affine Orlik–Solomon relators. -/
@[simp]
theorem mem_osRelations {r : ExteriorAlgebra B (𝒜 →₀ B)} :
    r ∈ osRelations B 𝒜 ↔ ∃ I : List 𝒜, I.Nodup ∧
      (Arrangement.inter I = ⊥ ∧ r = word (exteriorGen B) I ∨
        Arrangement.IsDependent I ∧ r = wordBoundary (exteriorGen B) I) :=
  Iff.rfl

/-- The affine Orlik–Solomon algebra over a commutative coefficient ring. It is a ring rather
than an ordinary commutative ring, and the exterior generators square to zero even in
characteristic two.

Blueprint: `def:os`. -/
def OSAlgebra : Type (max u v) :=
  RelationQuotient (osRelations B 𝒜)

namespace OSAlgebra

-- Keep the transported action visible to instance synthesis, including the canonical
-- natural and integer actions inherited by the ring structure.
instance instSMul {R : Type*} [CommSemiring R] [Algebra R B] : SMul R (OSAlgebra B 𝒜) :=
  inferInstanceAs (SMul R (RelationQuotient (osRelations B 𝒜)))

instance : Ring (OSAlgebra B 𝒜) :=
  inferInstanceAs (Ring (RelationQuotient (osRelations B 𝒜)))

instance instAlgebra {R : Type*} [CommSemiring R] [Algebra R B] : Algebra R (OSAlgebra B 𝒜) :=
  inferInstanceAs (Algebra R (RelationQuotient (osRelations B 𝒜)))

instance [Subsingleton B] : Subsingleton (OSAlgebra B 𝒜) :=
  Module.subsingleton B _

instance {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R B] [Algebra S B]
    [SMul R S] [IsScalarTower R S B] : IsScalarTower R S (OSAlgebra B 𝒜) :=
  inferInstanceAs (IsScalarTower R S (RelationQuotient (osRelations B 𝒜)))

/-- The quotient map from the exterior algebra. -/
def quotient : ExteriorAlgebra B (𝒜 →₀ B) →ₐ[B] OSAlgebra B 𝒜 :=
  RelationQuotient.mkₐ B (osRelations B 𝒜)

/-- The generator indexed by a hyperplane of the arrangement. -/
def generator (H : 𝒜) : OSAlgebra B 𝒜 :=
  quotient B 𝒜 (exteriorGen B H)

@[simp]
theorem quotient_exteriorGen (H : 𝒜) : quotient B 𝒜 (exteriorGen B H) = generator B 𝒜 H :=
  rfl

/-- Every element has an exterior-algebra representative. -/
theorem quotient_surjective : Function.Surjective (quotient B 𝒜) :=
  RelationQuotient.mk_surjective

/-- The kernel of the exterior-algebra quotient map is the two-sided relation submodule. -/
theorem quotient_eq_zero_iff {x : ExteriorAlgebra B (𝒜 →₀ B)} :
    quotient B 𝒜 x = 0 ↔ x ∈ relationSubmodule B (osRelations B 𝒜) :=
  RelationQuotient.mk_eq_zero_iff B

/-- Two exterior-algebra representatives agree exactly when their difference is a relation. -/
theorem quotient_eq_quotient_iff {x y : ExteriorAlgebra B (𝒜 →₀ B)} :
    quotient B 𝒜 x = quotient B 𝒜 y ↔ x - y ∈ relationSubmodule B (osRelations B 𝒜) :=
  RelationQuotient.mk_eq_mk_iff B

/-- Induction on representatives in the exterior algebra. -/
@[elab_as_elim, induction_eliminator]
protected theorem induction {motive : OSAlgebra B 𝒜 → Prop}
    (quotient : ∀ x, motive (quotient B 𝒜 x)) (x : OSAlgebra B 𝒜) : motive x := by
  obtain ⟨x, rfl⟩ := quotient_surjective B 𝒜 x
  exact quotient x

theorem quotient_word (I : List 𝒜) :
    quotient B 𝒜 (word (exteriorGen B) I) = word (generator B 𝒜) I := by
  simp

theorem quotient_wordBoundary (I : List 𝒜) :
    quotient B 𝒜 (wordBoundary (exteriorGen B) I) = wordBoundary (generator B 𝒜) I := by
  simp

/-- The generators form a square-zero, pairwise anticommuting family. -/
theorem isExteriorFamily_generator : IsExteriorFamily (generator B 𝒜) :=
  (isExteriorFamily_exteriorGen B).map (quotient B 𝒜)

/-- Each generator squares to zero, without assuming that two is invertible. -/
@[simp]
theorem generator_mul_self (H : 𝒜) : generator B 𝒜 H * generator B 𝒜 H = 0 :=
  (isExteriorFamily_generator B 𝒜).mul_self H

@[simp]
theorem generator_sq (H : 𝒜) : generator B 𝒜 H ^ 2 = 0 := by
  rw [pow_two, generator_mul_self]

/-- Empty-intersection products vanish in the presentation. -/
theorem word_eq_zero_of_inter_eq_bot {I : List 𝒜}
    (h : Arrangement.inter I = ⊥) : word (generator B 𝒜) I = 0 := by
  classical
  by_cases hI : I.Nodup
  · rw [← quotient_word]
    exact RelationQuotient.mk_eq_zero_of_mem ⟨I, hI, Or.inl ⟨h, rfl⟩⟩
  · exact (isExteriorFamily_generator B 𝒜).word_eq_zero_of_not_nodup hI

/-- The product of generators of disjoint hyperplanes vanishes in the presentation. -/
theorem generator_mul_eq_zero_of_disjoint (H K : 𝒜)
    (hHK : (H : AffineSubspace k V) ⊓ K = ⊥) :
    generator B 𝒜 H * generator B 𝒜 K = 0 := by
  simpa using word_eq_zero_of_inter_eq_bot B 𝒜 (I := [H, K]) (by simpa using hHK)

/-- The boundary of a nonempty dependent family vanishes in the presentation. -/
theorem wordBoundary_eq_zero_of_isDependent {I : List 𝒜}
    (h : Arrangement.IsDependent I) : wordBoundary (generator B 𝒜) I = 0 := by
  classical
  by_cases hI : I.Nodup
  · rw [← quotient_wordBoundary]
    exact RelationQuotient.mk_eq_zero_of_mem ⟨I, hI, Or.inr ⟨h, rfl⟩⟩
  · exact (isExteriorFamily_generator B 𝒜).wordBoundary_eq_zero_of_not_nodup hI

/-- Words in the generators span the Orlik–Solomon algebra as a module. -/
theorem span_range_word :
    Submodule.span B (Set.range (word (generator B 𝒜) : List 𝒜 → _)) = ⊤ := by
  have h := RelationQuotient.span_image_mk_eq_top
    (ℛ := osRelations B 𝒜) (OrlikSolomon.span_range_word B (I := 𝒜))
  change Submodule.span B ((quotient B 𝒜) '' Set.range (word (exteriorGen B))) = ⊤ at h
  simpa only [← Set.range_comp, Function.comp_def, quotient_word] using h

section Universal

variable {T : Type*} [Ring T]

/-- A family satisfying the affine Orlik–Solomon relations. This is the input of the universal
property, for example for logarithmic classes or for an inclusion of arrangements. -/
structure IsFamily (x : 𝒜 → T) : Prop extends IsExteriorFamily x where
  /-- Products for empty intersections vanish. -/
  word_eq_zero : ∀ I : List 𝒜, I.Nodup → Arrangement.inter I = ⊥ → word x I = 0
  /-- Boundaries for nonempty dependent intersections vanish. -/
  wordBoundary_eq_zero : ∀ I : List 𝒜, I.Nodup → Arrangement.IsDependent I →
    wordBoundary x I = 0

variable {B 𝒜}

/-- The canonical generators satisfy precisely the relations defining the presentation. -/
theorem isFamily_generator : IsFamily 𝒜 (generator B 𝒜) where
  toIsExteriorFamily := isExteriorFamily_generator B 𝒜
  word_eq_zero _ _ := word_eq_zero_of_inter_eq_bot B 𝒜
  wordBoundary_eq_zero _ _ := wordBoundary_eq_zero_of_isDependent B 𝒜

/-- A ring homomorphism carries a family satisfying the presentation to another such family. -/
theorem IsFamily.map {T' : Type*} [Ring T'] {x : 𝒜 → T} (hx : IsFamily 𝒜 x)
    (f : T →+* T') : IsFamily 𝒜 (fun H ↦ f (x H)) where
  toIsExteriorFamily := hx.toIsExteriorFamily.map f
  word_eq_zero I hI h := by simpa using congrArg f (hx.word_eq_zero I hI h)
  wordBoundary_eq_zero I hI h := by simpa using congrArg f (hx.wordBoundary_eq_zero I hI h)

variable [Algebra B T]

/-- The universal algebra map sending each generator to a family satisfying the two types of
affine Orlik–Solomon relations.

Blueprint: the presentation universal property of `def:os`. -/
noncomputable def lift (x : 𝒜 → T) (hx : IsFamily 𝒜 x) : OSAlgebra B 𝒜 →ₐ[B] T :=
  RelationQuotient.liftAlgHom (exteriorLift B ⟨x, hx.toIsExteriorFamily⟩) <| by
    rintro r ⟨I, hI, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩
    · simpa using hx.word_eq_zero I hI h
    · simpa using hx.wordBoundary_eq_zero I hI h

@[simp]
theorem lift_quotient (x : 𝒜 → T) (hx : IsFamily 𝒜 x) (a : ExteriorAlgebra B (𝒜 →₀ B)) :
    lift x hx (quotient B 𝒜 a) = exteriorLift B ⟨x, hx.toIsExteriorFamily⟩ a :=
  rfl

@[simp]
theorem lift_generator (x : 𝒜 → T) (hx : IsFamily 𝒜 x) (H : 𝒜) :
    lift x hx (generator B 𝒜 H) = x H := by
  change lift x hx (quotient B 𝒜 (exteriorGen B H)) = x H
  rw [lift_quotient, exteriorLift_exteriorGen]

/-- Algebra homomorphisms out of the presentation agree when they agree on generators. -/
@[ext]
theorem algHom_ext {f g : OSAlgebra B 𝒜 →ₐ[B] T}
    (h : ∀ H, f (generator B 𝒜 H) = g (generator B 𝒜 H)) : f = g := by
  apply RelationQuotient.algHom_ext
  exact exteriorAlgHom_ext h

/-- The universal property also gives uniqueness of the lifted algebra map. -/
theorem lift_unique (x : 𝒜 → T) (hx : IsFamily 𝒜 x) (f : OSAlgebra B 𝒜 →ₐ[B] T) :
    (∀ H, f (generator B 𝒜 H) = x H) ↔ f = lift x hx :=
  ⟨fun h ↦ algHom_ext fun H ↦ (h H).trans (lift_generator x hx H).symm,
    fun h H ↦ h ▸ lift_generator x hx H⟩

end Universal

/-! ### The empty arrangement -/

/-- The unique family on the empty arrangement satisfies its presentation. -/
theorem isFamily_empty : IsFamily (∅ : Arrangement k V)
    (fun H ↦ (isEmptyElim H : B)) where
  toIsExteriorFamily := ⟨fun H ↦ isEmptyElim H, fun H ↦ isEmptyElim H⟩
  word_eq_zero I _ h := by
    cases I with
    | nil => simp at h
    | cons H _ => exact isEmptyElim H
  wordBoundary_eq_zero I _ h := by
    cases I with
    | nil => exact False.elim (Arrangement.isDependent_nil _ h)
    | cons H _ => exact isEmptyElim H

/-- The affine presentation of the empty arrangement is the coefficient ring. In particular,
this calculation applies in dimension zero and with the zero coefficient ring.

Blueprint: the empty-arrangement case of `lem:os-basic`. -/
def emptyEquiv : OSAlgebra B (∅ : Arrangement k V) ≃ₐ[B] B :=
  AlgEquiv.ofAlgHom (lift _ (isFamily_empty B)) (Algebra.ofId B _)
    (Subsingleton.elim _ _)
    (algHom_ext fun H ↦ isEmptyElim H)

theorem emptyEquiv_algebraMap (b : B) :
    emptyEquiv B (k := k) (V := V) (algebraMap B (OSAlgebra B ∅) b) = b :=
  (emptyEquiv B).commutes b

/-- In dimension zero every arrangement is empty, so its presentation is the coefficient ring. -/
def equivOfSubsingleton [Subsingleton V] : OSAlgebra B 𝒜 ≃ₐ[B] B := by
  have h := Arrangement.eq_empty_of_subsingleton 𝒜
  subst 𝒜
  exact emptyEquiv B

/-! ### Linear descent and spanning -/

section Linear

variable {N : Type*} [AddCommGroup N] [Module B N]

/-- Linear maps out of the presentation agree if they agree on generator words. -/
theorem linearMap_ext {f g : OSAlgebra B 𝒜 →ₗ[B] N}
    (h : ∀ I : List 𝒜, f (word (generator B 𝒜) I) = g (word (generator B 𝒜) I)) : f = g :=
  LinearMap.ext_on_range (span_range_word B 𝒜) h

/-- A linear map on the exterior algebra descends when it kills every context of a relator.
This version of descent, unlike algebra descent, can target a deletion cokernel.

Blueprint: the linear descent used in `def:lift-map`. -/
def liftLinear (f : ExteriorAlgebra B (𝒜 →₀ B) →ₗ[B] N)
    (hf : ∀ u, ∀ r ∈ osRelations B 𝒜, ∀ v, f (u * r * v) = 0) :
    OSAlgebra B 𝒜 →ₗ[B] N :=
  RelationQuotient.liftLinear f (relationSubmodule_le_ker_iff.2 hf)

@[simp]
theorem liftLinear_quotient (f : ExteriorAlgebra B (𝒜 →₀ B) →ₗ[B] N)
    (hf : ∀ u, ∀ r ∈ osRelations B 𝒜, ∀ v, f (u * r * v) = 0)
    (a : ExteriorAlgebra B (𝒜 →₀ B)) :
    liftLinear B 𝒜 f hf (quotient B 𝒜 a) = f a :=
  rfl

end Linear

/-! ### Inclusions and deletion -/

section Map

variable {𝒜 ℬ 𝒞 : Arrangement k V}

/-- An inclusion of arrangements carries the presentation generators to a family satisfying
the old relations. -/
theorem isFamily_inclusion (h : 𝒜 ≤ ℬ) :
    IsFamily 𝒜 (fun H ↦ generator B ℬ (Arrangement.inclusion h H)) where
  toIsExteriorFamily := (isExteriorFamily_generator B ℬ).comp _
  word_eq_zero I _ he := by
    rw [← word_map]
    exact word_eq_zero_of_inter_eq_bot B ℬ (by simpa using he)
  wordBoundary_eq_zero I _ hd := by
    rw [← wordBoundary_map]
    exact wordBoundary_eq_zero_of_isDependent B ℬ
      ((Arrangement.isDependent_map_inclusion h I).2 hd)

/-- An inclusion of arrangements induces an algebra map of their affine presentations.
Injectivity is a conclusion of the later structure theorem, not part of this construction. -/
def map (h : 𝒜 ≤ ℬ) : OSAlgebra B 𝒜 →ₐ[B] OSAlgebra B ℬ :=
  lift _ (isFamily_inclusion B h)

@[simp]
theorem map_generator (h : 𝒜 ≤ ℬ) (H : 𝒜) :
    map B h (generator B 𝒜 H) = generator B ℬ (Arrangement.inclusion h H) :=
  lift_generator _ _ H

/-- Inclusions carry words to the same words with the letters included. -/
theorem map_word (h : 𝒜 ≤ ℬ) (I : List 𝒜) :
    map B h (word (generator B 𝒜) I) =
      word (generator B ℬ) (I.map (Arrangement.inclusion h)) := by
  simp [word_map]

@[simp]
theorem map_refl : map B (le_refl 𝒜) = AlgHom.id B (OSAlgebra B 𝒜) := by
  ext H
  rw [map_generator]
  rfl

@[simp]
theorem map_comp (h : 𝒜 ≤ ℬ) (h' : ℬ ≤ 𝒞) :
    (map B h').comp (map B h) = map B (h.trans h') := by
  ext H
  simp only [AlgHom.comp_apply, map_generator]
  rfl

variable (𝒜)

/-- The deletion algebra map, preserving the generators of the deletion.

Blueprint: the map `a` in `lem:os-basic`. -/
def deletionMap (H : AffineSubspace k V) : OSAlgebra B (𝒜.deletion H) →ₐ[B] OSAlgebra B 𝒜 :=
  map B (Arrangement.deletion_le 𝒜 H)

@[simp]
theorem deletionMap_generator (H : AffineSubspace k V) (K : 𝒜.deletion H) :
    deletionMap B 𝒜 H (generator B (𝒜.deletion H) K) =
      generator B 𝒜 (Arrangement.inclusion (Arrangement.deletion_le 𝒜 H) K) :=
  map_generator B _ K

end Map

/-! ### The ordinary exterior degree -/

/-- The internal grading by exterior degree. Coefficients have degree zero; the weight-graded
coefficient refinement is constructed separately over the smaller coefficient ring.

Blueprint: the exterior-degree part of `lem:os-basic`. -/
def degree (n : ℕ) : Submodule B (OSAlgebra B 𝒜) :=
  RelationQuotient.grading (osRelations B 𝒜)
    (fun n : ℕ ↦ ⋀[B]^n (𝒜 →₀ B)) n

/-- Each defining relator is homogeneous in exterior degree. -/
theorem osRelations_homogeneous :
    ∀ r ∈ osRelations B 𝒜,
      SetLike.IsHomogeneousElem (fun n : ℕ ↦ ⋀[B]^n (𝒜 →₀ B)) r := by
  rintro r ⟨I, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩
  · exact ⟨I.length, word_mem_exteriorPower B I⟩
  · exact ⟨I.length - 1, wordBoundary_mem_exteriorPower B I⟩

instance : GradedAlgebra (degree B 𝒜) :=
  RelationQuotient.gradedAlgebra (fun n : ℕ ↦ ⋀[B]^n (𝒜 →₀ B))
    (osRelations_homogeneous B 𝒜)

/-- A word has degree equal to its length. -/
theorem word_mem_degree (I : List 𝒜) :
    word (generator B 𝒜) I ∈ degree B 𝒜 I.length := by
  rw [← quotient_word]
  exact RelationQuotient.mk_mem_grading (word_mem_exteriorPower B I)

/-- Each generator has exterior degree one. -/
theorem generator_mem_degree (H : 𝒜) : generator B 𝒜 H ∈ degree B 𝒜 1 := by
  simpa only [word_singleton, List.length_singleton] using word_mem_degree B 𝒜 [H]

/-- A signed boundary has degree one less than its word. -/
theorem wordBoundary_mem_degree (I : List 𝒜) :
    wordBoundary (generator B 𝒜) I ∈ degree B 𝒜 (I.length - 1) := by
  rw [← quotient_wordBoundary]
  exact RelationQuotient.mk_mem_grading (wordBoundary_mem_exteriorPower B I)

/-- Words of length `n` span the degree `n` piece. -/
theorem span_word_length (n : ℕ) :
    Submodule.span B {y | ∃ I : List 𝒜, I.length = n ∧ word (generator B 𝒜) I = y} =
      degree B 𝒜 n := by
  change _ = (⋀[B]^n (𝒜 →₀ B)).map (quotient B 𝒜).toLinearMap
  rw [← OrlikSolomon.span_word_length B n, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨I, hI, rfl⟩
    exact ⟨word (exteriorGen B) I, ⟨I, hI, rfl⟩, quotient_word B 𝒜 I⟩
  · rintro ⟨_, ⟨I, hI, rfl⟩, rfl⟩
    exact ⟨I, hI, (quotient_word B 𝒜 I).symm⟩

/-- Homogeneous elements supercommute according to their exterior degrees. The proof uses
square-zero exterior generators, so it also applies with two-torsion coefficients. -/
theorem mul_comm_of_mem_degree {n m : ℕ} {x y : OSAlgebra B 𝒜}
    (hx : x ∈ degree B 𝒜 n) (hy : y ∈ degree B 𝒜 m) :
    x * y = ((n : ℤ) * m).negOnePow • (y * x) := by
  rw [← span_word_length] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, hI, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨J, hJ, rfl⟩ := hy
      simpa only [hI, hJ] using (isExteriorFamily_generator B 𝒜).word_mul_word_comm I J
    | zero => simp
    | add x y _ _ hx hy => simp only [mul_add, add_mul, hx, hy, smul_add]
    | smul b y _ hy =>
      simp only [mul_smul_comm, smul_mul_assoc, smul_comm b, hy]
  | zero => simp
  | add x y _ _ hx hy => simp only [add_mul, mul_add, hx, hy, smul_add]
  | smul b x _ hx =>
    simp only [smul_mul_assoc, mul_smul_comm, smul_comm b, hx]

/-- Inclusion maps preserve exterior degree. -/
theorem map_mem_degree {ℬ : Arrangement k V} (h : 𝒜 ≤ ℬ) {n : ℕ} {x : OSAlgebra B 𝒜}
    (hx : x ∈ degree B 𝒜 n) : map B h x ∈ degree B ℬ n := by
  rw [← span_word_length] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, rfl, rfl⟩ := hx
    rw [map_word]
    simpa only [List.length_map] using word_mem_degree B ℬ (I.map (Arrangement.inclusion h))
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx

/-- The deletion map preserves exterior degree. -/
theorem deletionMap_mem_degree (H : AffineSubspace k V) {n : ℕ}
    {x : OSAlgebra B (𝒜.deletion H)} (hx : x ∈ degree B (𝒜.deletion H) n) :
    deletionMap B 𝒜 H x ∈ degree B 𝒜 n :=
  map_mem_degree B _ _ hx

end OSAlgebra

end OrlikSolomon
