/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Algebra.ExteriorWords
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

/-- The affine Orlik–Solomon algebra over a commutative coefficient ring. It is a ring rather
than an ordinary commutative ring, and the exterior generators square to zero even in
characteristic two.

Blueprint: `def:os`. -/
def OSAlgebra : Type (max u v) :=
  RelationQuotient (osRelations B 𝒜)

namespace OSAlgebra

instance : Ring (OSAlgebra B 𝒜) :=
  inferInstanceAs (Ring (RelationQuotient (osRelations B 𝒜)))

instance instAlgebra {R : Type*} [CommSemiring R] [Algebra R B] : Algebra R (OSAlgebra B 𝒜) :=
  inferInstanceAs (Algebra R (RelationQuotient (osRelations B 𝒜)))

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

/-- Induction on representatives in the exterior algebra. -/
@[elab_as_elim, induction_eliminator]
protected theorem induction {motive : OSAlgebra B 𝒜 → Prop}
    (quotient : ∀ x, motive (quotient B 𝒜 x)) (x : OSAlgebra B 𝒜) : motive x := by
  obtain ⟨x, rfl⟩ := quotient_surjective B 𝒜 x
  exact quotient x

@[simp]
theorem quotient_word (I : List 𝒜) :
    quotient B 𝒜 (word (exteriorGen B) I) = word (generator B 𝒜) I := by
  simp

@[simp]
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

/-- Empty-intersection products vanish in the presentation. -/
theorem word_eq_zero_of_inter_eq_bot {I : List 𝒜} (hI : I.Nodup)
    (h : Arrangement.inter I = ⊥) : word (generator B 𝒜) I = 0 := by
  rw [← quotient_word]
  exact RelationQuotient.mk_eq_zero_of_mem ⟨I, hI, Or.inl ⟨h, rfl⟩⟩

/-- The boundary of a nonempty dependent family vanishes in the presentation. -/
theorem wordBoundary_eq_zero_of_isDependent {I : List 𝒜} (hI : I.Nodup)
    (h : Arrangement.IsDependent I) : wordBoundary (generator B 𝒜) I = 0 := by
  rw [← quotient_wordBoundary]
  exact RelationQuotient.mk_eq_zero_of_mem ⟨I, hI, Or.inr ⟨h, rfl⟩⟩

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
  word_eq_zero _ := word_eq_zero_of_inter_eq_bot B 𝒜
  wordBoundary_eq_zero _ := wordBoundary_eq_zero_of_isDependent B 𝒜

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

end OSAlgebra

end OrlikSolomon
