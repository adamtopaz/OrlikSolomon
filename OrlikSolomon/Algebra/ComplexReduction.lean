/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Reduction through a contractible quotient of complexes

For a short exact sequence `0 → F → G → Q → 0` of complexes of modules with a contracting
homotopy on `Q`, a cocycle in `G` is cohomologous to a cocycle in `F`, and a primitive in `G` of a
class from `F` can be replaced by one in `F`. The conclusions specify representatives and
primitives, rather than just an isomorphism on homology, so they can be applied successively in a
finite filtration.

Everything holds for any complex shape and over any ring. There is no boundedness, nontriviality,
commutativity or coefficient-characteristic assumption. For connective cochain complexes, the
vanishing differentials dictated by the shape handle degree zero.

## Main results

* `OrlikSolomon.exists_cocycle_reduction_of_contractible_quotient` and
  `OrlikSolomon.exists_primitive_reduction_of_contractible_quotient`: reduction for a square-zero
  linear map and a submodule described as the kernel of a quotient map.
* `OrlikSolomon.exists_cocycle_reduction`: lower a cocycle by an explicit boundary.
* `OrlikSolomon.exists_primitive_reduction`: lower a primitive without changing its differential.

Blueprint: `lem:dr-filtration-reduction`. These are pure homological algebra and do not depend on
forms, arrangements or a cohomology theory.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

namespace OrlikSolomon

universe u v w

private theorem exists_sub_differential_mem_ker {R : Type u} [Ring R]
    {M₀ M₁ Q₀ Q₁ Q₂ : Type*}
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup Q₀] [AddCommGroup Q₁] [AddCommGroup Q₂]
    [Module R M₀] [Module R M₁] [Module R Q₀] [Module R Q₁] [Module R Q₂]
    (d : M₀ →ₗ[R] M₁) (δ₀ : Q₀ →ₗ[R] Q₁) (δ₁ : Q₁ →ₗ[R] Q₂)
    (q₀ : M₀ →ₗ[R] Q₀) (q₁ : M₁ →ₗ[R] Q₁)
    (H₀ : Q₁ →ₗ[R] Q₀) (H₁ : Q₂ →ₗ[R] Q₁) (hq₀ : Function.Surjective q₀)
    (hcomm : q₁.comp d = δ₀.comp q₀)
    (hcontract : δ₀.comp H₀ + H₁.comp δ₁ = LinearMap.id)
    (y : M₁) (hy : δ₁ (q₁ y) = 0) : ∃ b : M₀, q₁ (y - d b) = 0 := by
  obtain ⟨b, hb⟩ := hq₀ (H₀ (q₁ y))
  have hcontract_apply := congrArg (fun t : Q₁ →ₗ[R] Q₁ => t (q₁ y)) hcontract
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hy, map_zero,
    add_zero] at hcontract_apply
  have hcomm_apply := congrArg (fun t : M₀ →ₗ[R] Q₁ => t b) hcomm
  simp only [LinearMap.comp_apply] at hcomm_apply
  exact ⟨b, by rw [map_sub, hcomm_apply, hb, hcontract_apply, sub_self]⟩

section LinearMap

variable {R : Type u} [Ring R] {M Q : Type*} [AddCommGroup M] [AddCommGroup Q]
  [Module R M] [Module R Q]
  (d : M →ₗ[R] M) (hd : d.comp d = 0) (F : Submodule R M)
  (q : M →ₗ[R] Q) (hq : Function.Surjective q) (hker : LinearMap.ker q = F)
  (dQ H : Q →ₗ[R] Q) (hcomm : q.comp d = dQ.comp q)
  (hcontract : dQ.comp H + H.comp dQ = LinearMap.id)

include hd hq hker hcomm hcontract

/-- A closed element can be lowered, by subtracting an actual boundary, into the kernel of a
quotient map whose differential admits a contracting homotopy. The submodule `F` is specified by
`ker q = F`; its stability under the differential follows from this equation and `hcomm`.

This total-module version does not require a grading or a complex structure. It applies, for
example, to successive stages of a differential-stable filtration of a total algebra.

Blueprint: the cocycle assertion of `lem:dr-filtration-reduction`. -/
theorem exists_cocycle_reduction_of_contractible_quotient (z : M) (hz : d z = 0) :
    ∃ b : M, z - d b ∈ F ∧ d (z - d b) = 0 := by
  have hzero : dQ (q z) = 0 := by
    have hc := congrArg (fun t : M →ₗ[R] Q => t z) hcomm
    simp only [LinearMap.comp_apply, hz, map_zero] at hc
    exact hc.symm
  obtain ⟨b, hb⟩ := exists_sub_differential_mem_ker d dQ dQ q q H H hq hcomm hcontract z hzero
  refine ⟨b, ?_, ?_⟩
  · rw [← hker]
    exact hb
  · have hd2 := congrArg (fun t : M →ₗ[R] M => t b) hd
    change d (d b) = 0 at hd2
    rw [map_sub, hz, hd2, sub_self]

/-- If a differential belongs to the kernel of a quotient map with a contracting homotopy, its
primitive can be replaced by one in that kernel. The resulting primitive has exactly the same
differential. No grading or boundedness assumption is needed.

Blueprint: the primitive assertion of `lem:dr-filtration-reduction`. -/
theorem exists_primitive_reduction_of_contractible_quotient (y : M) (hy : d y ∈ F) :
    ∃ x : M, x ∈ F ∧ d x = d y := by
  have hzero : dQ (q y) = 0 := by
    have hc := congrArg (fun t : M →ₗ[R] Q => t y) hcomm
    simp only [LinearMap.comp_apply] at hc
    rw [← hc]
    exact (show d y ∈ LinearMap.ker q by rw [hker]; exact hy)
  obtain ⟨b, hb⟩ := exists_sub_differential_mem_ker d dQ dQ q q H H hq hcomm hcontract y hzero
  refine ⟨y - d b, ?_, ?_⟩
  · rw [← hker]
    exact hb
  · have hd2 := congrArg (fun t : M →ₗ[R] M => t b) hd
    change d (d b) = 0 at hd2
    rw [map_sub, hd2, sub_zero]

end LinearMap

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)}
  (hS : S.ShortExact) (hQ : Homotopy (𝟙 S.X₃) 0)

include hS hQ

private theorem exists_sub_boundary_eq_image (i : ι) (y : S.X₂.X i)
    (hy : S.X₃.d i (c.next i) (S.g.f i y) = 0) :
    ∃ (b : S.X₂.X (c.prev i)) (a : S.X₁.X i),
      S.f.f i a = y - S.X₂.d (c.prev i) i b := by
  have hp := hS.map_of_exact (eval (ModuleCat R) c (c.prev i))
  have hcomm : (S.g.f i).hom.comp (S.X₂.d (c.prev i) i).hom =
      (S.X₃.d (c.prev i) i).hom.comp (S.g.f (c.prev i)).hom := by
    exact congrArg ModuleCat.Hom.hom (S.g.comm (c.prev i) i).symm
  have hcontract : (S.X₃.d (c.prev i) i).hom.comp (hQ.hom i (c.prev i)).hom +
      (hQ.hom (c.next i) i).hom.comp (S.X₃.d i (c.next i)).hom = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom (hQ.comm i)
    change LinearMap.id =
      (hQ.hom (c.next i) i).hom.comp (S.X₃.d i (c.next i)).hom +
        (S.X₃.d (c.prev i) i).hom.comp (hQ.hom i (c.prev i)).hom + 0 at h
    rw [add_zero, add_comm] at h
    exact h.symm
  obtain ⟨b, hzero⟩ := exists_sub_differential_mem_ker
    (S.X₂.d (c.prev i) i).hom (S.X₃.d (c.prev i) i).hom
    (S.X₃.d i (c.next i)).hom (S.g.f (c.prev i)).hom (S.g.f i).hom
    (hQ.hom i (c.prev i)).hom (hQ.hom (c.next i) i).hom
    hp.moduleCat_surjective_g hcomm hcontract y hy
  have hi := hS.map_of_exact (eval (ModuleCat R) c i)
  obtain ⟨a, ha⟩ := (S.map (eval (ModuleCat R) c i)).moduleCat_exact_iff.1 hi.exact _ hzero
  exact ⟨b, a, ha⟩

/-- A cocycle in the middle complex of a short exact sequence with contractible quotient is
cohomologous to the image of a cocycle in the first complex. The primitive `b` lies in the preceding
degree, and the displayed equation specifies the actual correction.

The complex shape is arbitrary. In particular, for a cochain complex indexed by `ℕ` and `i = 0`,
the preceding differential is zero, so the cocycle itself comes from the first complex.

Blueprint: the cocycle assertion of `lem:dr-filtration-reduction`. -/
theorem exists_cocycle_reduction (i : ι) (z : S.X₂.X i) (hz : S.X₂.d i (c.next i) z = 0) :
    ∃ (a : S.X₁.X i) (b : S.X₂.X (c.prev i)),
      S.X₁.d i (c.next i) a = 0 ∧ S.f.f i a = z - S.X₂.d (c.prev i) i b := by
  have hzero : S.X₃.d i (c.next i) (S.g.f i z) = 0 := by
    have hc := congrArg (fun t : S.X₂.X i ⟶ S.X₃.X (c.next i) => t z)
      (S.g.comm i (c.next i))
    change S.X₃.d i (c.next i) (S.g.f i z) = S.g.f (c.next i) (S.X₂.d i (c.next i) z) at hc
    rw [hc, hz, map_zero]
  obtain ⟨b, a, ha⟩ := exists_sub_boundary_eq_image hS hQ i z hzero
  refine ⟨a, b, ?_, ha⟩
  have hi := (hS.map_of_exact (eval (ModuleCat R) c (c.next i))).moduleCat_injective_f
  apply hi
  change S.f.f (c.next i) (S.X₁.d i (c.next i) a) = S.f.f (c.next i) 0
  have hc := congrArg (fun t : S.X₁.X i ⟶ S.X₂.X (c.next i) => t a)
    (S.f.comm i (c.next i))
  change S.X₂.d i (c.next i) (S.f.f i a) = S.f.f (c.next i) (S.X₁.d i (c.next i) a) at hc
  have hd2 := congrArg (fun t : S.X₂.X (c.prev i) ⟶ S.X₂.X (c.next i) => t b)
    (S.X₂.d_comp_d (c.prev i) i (c.next i))
  change S.X₂.d i (c.next i) (S.X₂.d (c.prev i) i b) = 0 at hd2
  rw [← hc, ha, map_sub, hz, hd2, sub_self, map_zero]

private theorem exists_primitive_reduction_next (i : ι) (z : S.X₁.X (c.next i)) (y : S.X₂.X i)
    (hy : S.f.f (c.next i) z = S.X₂.d i (c.next i) y) :
    ∃ x : S.X₁.X i, S.X₁.d i (c.next i) x = z := by
  have hzero : S.X₃.d i (c.next i) (S.g.f i y) = 0 := by
    have hc := congrArg (fun t : S.X₂.X i ⟶ S.X₃.X (c.next i) => t y)
      (S.g.comm i (c.next i))
    change S.X₃.d i (c.next i) (S.g.f i y) = S.g.f (c.next i) (S.X₂.d i (c.next i) y) at hc
    rw [hc, ← hy]
    exact (S.map (eval (ModuleCat R) c (c.next i))).moduleCat_zero_apply z
  obtain ⟨b, x, hx⟩ := exists_sub_boundary_eq_image hS hQ i y hzero
  refine ⟨x, ?_⟩
  have hi := (hS.map_of_exact (eval (ModuleCat R) c (c.next i))).moduleCat_injective_f
  apply hi
  change S.f.f (c.next i) (S.X₁.d i (c.next i) x) = S.f.f (c.next i) z
  have hc := congrArg (fun t : S.X₁.X i ⟶ S.X₂.X (c.next i) => t x)
    (S.f.comm i (c.next i))
  change S.X₂.d i (c.next i) (S.f.f i x) = S.f.f (c.next i) (S.X₁.d i (c.next i) x) at hc
  have hd2 := congrArg (fun t : S.X₂.X (c.prev i) ⟶ S.X₂.X (c.next i) => t b)
    (S.X₂.d_comp_d (c.prev i) i (c.next i))
  change S.X₂.d i (c.next i) (S.X₂.d (c.prev i) i b) = 0 at hd2
  rw [← hc, hx, map_sub, hd2, sub_zero, hy]

/-- A primitive in the middle complex of a short exact sequence with contractible quotient
can be replaced by a primitive in the first complex whenever its differential comes from that
complex. No closedness hypothesis on `z` is needed: it follows from the given equation and
injectivity of the inclusion.

The two indices need not be related by the complex shape. When there is no arrow, both
differentials vanish, and injectivity forces `z = 0`. This includes degree-zero boundaries in a
cochain complex indexed by `ℕ`.

Blueprint: the primitive assertion of `lem:dr-filtration-reduction`. -/
theorem exists_primitive_reduction (i j : ι) (z : S.X₁.X j) (y : S.X₂.X i)
    (hy : S.f.f j z = S.X₂.d i j y) :
    ∃ x : S.X₁.X i, S.X₁.d i j x = z := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact exists_primitive_reduction_next hS hQ i z y hy
  · have hi : Function.Injective (S.f.f j) :=
      (hS.map_of_exact (eval (ModuleCat R) c j)).moduleCat_injective_f
    have hz : z = 0 := hi (by rw [hy, S.X₂.shape i j hij, map_zero]; rfl)
    exact ⟨0, by rw [map_zero, hz]⟩

end OrlikSolomon
