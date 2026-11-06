/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Examples.CoordinatePolynomials
public import OrlikSolomon.Examples.Cokernel
public import OrlikSolomon.Presentation.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Exterior algebras in the regression examples

`coordinateExteriorEquiv` identifies the algebra of the coordinate hyperplanes with the full
exterior algebra on their labels. `singletonExteriorEquiv` gives the one-hyperplane case, and
`singlePointExteriorEquiv` instantiates it on the existing one-point fixture.
These equivalences send each generator to the corresponding exterior generator, over arbitrary
commutative coefficient rings. In particular, the singleton generator squares to zero over
`ZMod 2` and `ZMod 4`.

Blueprint: items 2 and 3 of "Required mathematical regression examples".
-/

@[expose] public section

noncomputable section

universe u v

namespace OrlikSolomon.ExteriorExamples

open OrlikSolomon.OSAlgebra OrlikSolomon.Arrangement

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
  (B : Type v) [CommRing B] {𝒜 : Arrangement k V}

private theorem exteriorFamilyOfIndependent
    (h : ∀ I : List 𝒜, I.Nodup → inter I ≠ ⊥ ∧ codim (inter I) = I.length) :
    IsFamily 𝒜 (exteriorGen B : 𝒜 → ExteriorAlgebra B (𝒜 →₀ B)) where
  toIsExteriorFamily := isExteriorFamily_exteriorGen B
  word_eq_zero I hI hbot := ((h I hI).1 hbot).elim
  wordBoundary_eq_zero I hI hdep := by
    have hlt : I.length < I.length := by simpa [(h I hI).2] using hdep.2
    exact (Nat.lt_irrefl _ hlt).elim

private def exteriorEquivOfIndependent
    (h : ∀ I : List 𝒜, I.Nodup → inter I ≠ ⊥ ∧ codim (inter I) = I.length) :
    OSAlgebra B 𝒜 ≃ₐ[B] ExteriorAlgebra B (𝒜 →₀ B) :=
  AlgEquiv.ofAlgHom (lift _ (exteriorFamilyOfIndependent B h)) (quotient B 𝒜)
    (exteriorAlgHom_ext fun H ↦ by simp)
    (OSAlgebra.algHom_ext fun H ↦ by simp)

private theorem exteriorEquivOfIndependent_generator
    (h : ∀ I : List 𝒜, I.Nodup → inter I ≠ ⊥ ∧ codim (inter I) = I.length) (H : 𝒜) :
    exteriorEquivOfIndependent B h (generator B 𝒜 H) = exteriorGen B H :=
  lift_generator _ (exteriorFamilyOfIndependent B h) H

section Coordinate

variable (k) (ι : Type u) [Fintype ι]

open scoped Classical in
private theorem coordinate_inter (I : List (Examples.coordinateArrangement k ι)) :
    inter I = sInf (↑(I.toFinset.image Subtype.val) : Set (AffineSubspace k (ι → k))) := by
  classical
  ext x
  rw [mem_inter, AffineSubspace.mem_sInf_iff]
  constructor
  · intro h H hH
    obtain ⟨K, hK, rfl⟩ := Finset.mem_image.1 hH
    exact h K (List.mem_toFinset.1 hK)
  · intro h K hK
    exact h _ (Finset.mem_image.2 ⟨K, List.mem_toFinset.2 hK, rfl⟩)

private theorem coordinate_independent (I : List (Examples.coordinateArrangement k ι))
    (hI : I.Nodup) : inter I ≠ ⊥ ∧ codim (inter I) = I.length := by
  classical
  have hsub : I.toFinset.image Subtype.val ⊆
      (Examples.coordinateArrangement k ι).hyperplanes := by
    intro H hH
    obtain ⟨K, -, rfl⟩ := Finset.mem_image.1 hH
    exact K.2
  rw [Examples.hyperplanes_coordinateArrangement] at hsub
  obtain ⟨S, hS⟩ := Finset.subset_univ_image_iff.1 hsub
  have hcard : S.card = I.length := by
    have hc : (I.toFinset.image Subtype.val).card = I.length := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, List.toFinset_card_of_nodup hI]
    rw [← hS, Finset.card_image_of_injective _ (Examples.coordinateHyperplane_injective k)] at hc
    exact hc
  rw [coordinate_inter k ι I, ← hS]
  exact ⟨Examples.coordinateHyperplane_sInf_ne_bot k S,
    (Examples.codim_sInf_coordinateHyperplane k S).trans hcard⟩

/-- The coordinate arrangement has the full exterior algebra on its coordinate labels, with no
additional relations. This holds over every coefficient ring, including the zero ring.

Blueprint: regression item 3. -/
@[no_expose]
def coordinateExteriorEquiv :
    OSAlgebra B (Examples.coordinateArrangement k ι) ≃ₐ[B]
      ExteriorAlgebra B ((Examples.coordinateArrangement k ι) →₀ B) :=
  exteriorEquivOfIndependent B (coordinate_independent k ι)

/-- The coordinate-algebra equivalence preserves the specified generators. -/
@[simp]
theorem coordinateExteriorEquiv_generator (H : Examples.coordinateArrangement k ι) :
    coordinateExteriorEquiv (B := B) (k := k) ι (generator B _ H) = exteriorGen B H :=
  exteriorEquivOfIndependent_generator B _ H

end Coordinate

section Singleton

variable (H₀ : 𝒜) (h𝒜 : ∀ H : 𝒜, H = H₀)

include h𝒜 in
private theorem singleton_independent (I : List 𝒜) (hI : I.Nodup) :
    inter I ≠ ⊥ ∧ codim (inter I) = I.length := by
  cases I with
  | nil => simp
  | cons H I =>
    cases I with
    | nil => simpa using ⟨(𝒜.isHyperplane H.2).ne_bot, (𝒜.isHyperplane H.2).codim_eq_one⟩
    | cons K I =>
      have hne : H ≠ K := by
        intro h
        apply (List.nodup_cons.1 hI).1
        simp [h]
      exact (hne ((h𝒜 H).trans (h𝒜 K).symm)).elim

/-- A one-hyperplane arrangement has the exterior algebra on its unique label.

Blueprint: regression item 2. -/
@[no_expose]
def singletonExteriorEquiv : OSAlgebra B 𝒜 ≃ₐ[B] ExteriorAlgebra B (𝒜 →₀ B) :=
  exteriorEquivOfIndependent B (singleton_independent (H₀ := H₀) h𝒜)

/-- The singleton-algebra equivalence preserves the unique generator. -/
@[simp]
theorem singletonExteriorEquiv_generator :
    singletonExteriorEquiv B H₀ h𝒜 (generator B 𝒜 H₀) = exteriorGen B H₀ :=
  exteriorEquivOfIndependent_generator B _ H₀

end Singleton

/-- The existing singleton fixture has the full exterior algebra on its one actual label. -/
def singlePointExteriorEquiv (k : Type u) [Field k] :
    OSAlgebra B (PresentationExamples.singlePoint k) ≃ₐ[B]
      ExteriorAlgebra B ((PresentationExamples.singlePoint k) →₀ B) :=
  singletonExteriorEquiv B (PresentationExamples.singlePointLabel k)
    (fun _ ↦ Subsingleton.elim _ _)

/-- The concrete singleton equivalence sends its generator to the exterior generator. -/
@[simp]
theorem singlePointExteriorEquiv_generator :
    singlePointExteriorEquiv B k
        (generator B (PresentationExamples.singlePoint k)
          (PresentationExamples.singlePointLabel k)) =
      exteriorGen B (PresentationExamples.singlePointLabel k) :=
  singletonExteriorEquiv_generator B _ _

/-- The actual singleton generator has square zero over `ℤ/4`, where signed commutativity alone
would only force twice its square to vanish. -/
theorem singlePoint_generator_sq_zmod_four :
    generator (ZMod 4) (PresentationExamples.singlePoint k)
      (PresentationExamples.singlePointLabel k) ^ 2 = 0 := generator_sq _ _ _

example : generator (ZMod 2) (PresentationExamples.singlePoint k)
    (PresentationExamples.singlePointLabel k) ^ 2 = 0 := generator_sq _ _ _

-- These coefficients detect the distinction between square-zero and merely signed commutativity.
example (H : 𝒜) : generator (ZMod 2) 𝒜 H ^ 2 = 0 := generator_sq _ _ _

example (H : 𝒜) : generator (ZMod 4) 𝒜 H ^ 2 = 0 := generator_sq _ _ _

end OrlikSolomon.ExteriorExamples
