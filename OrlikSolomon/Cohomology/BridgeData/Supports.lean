/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.BridgeData.Basic

/-!
# Localization with supports and oriented divisor purity

`SupportsAndPurity` is the standard degreewise input for the localization part of
`lem:standard-bridge`. It includes groups with supports, support-forgetting maps, the connecting
maps of localization, and oriented purity equivalences. Its exactness fields concern the
degreewise sequence with supports; neither total exactness nor Gysin or residue maps are input.

Mixed products of a supported class and an ambient class encode the usual boundary projection
formula and the compatibility of oriented purity with products. These give coefficient linearity
of the Gysin and residue maps constructed from the data.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum
open OrlikSolomon.SmoothAlg

universe u v w z t

namespace OrlikSolomon

/-- Degreewise localization with supports and oriented purity for all the certified divisor pairs.
The supported group is `H_D^{p,w}(X)`, the connecting map raises `p` by one, and purity raises the
bidegree by `(2,1)`. Products and their compatibilities use sigma equalities whenever the written
degrees differ by associativity or commutativity. Blueprint: `lem:standard-bridge`.

The projection identities are supplied for arbitrary homogeneous factors. This is the standard
full homogeneous projection formula allowed by the blueprint. Only the specialization with the
first factor in degree `(1,1)` is retained in `OrdinaryTheory`. -/
structure SupportsAndPurity {k : Type u} [CommRing k] {R : Type v} [CommRing R]
    {B : Type w} [CommRing B] [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
    (D : DegreewiseTheory.{u, v, w, z} k ℬ) where
  /-- Cohomology of the ambient object with supports in its divisor. -/
  support (P : DivisorPair k) : ℤ × ℤ → Type t
  /-- Supported cohomology groups are additive abelian groups. -/
  [addCommGroup : ∀ P i, AddCommGroup (support P i)]
  /-- Supported cohomology groups are `R`-modules. -/
  [module : ∀ P i, Module R (support P i)]
  /-- The support-forgetting map `H_D^{p,w}(X) → H^{p,w}(X)`. -/
  forget (P : DivisorPair k) (i : ℤ × ℤ) : support P i →ₗ[R] D.H P.ambient i
  /-- The connecting homomorphism `H^{p,w}(U) → H_D^{p+1,w}(X)`. -/
  boundary (P : DivisorPair k) (i : ℤ × ℤ) :
    D.H P.compl i →ₗ[R] support P (i + (1, 0))
  /-- Oriented divisor purity `H^{p,w}(D) ≃ H_D^{p+2,w+1}(X)`. -/
  purity (P : DivisorPair k) (i : ℤ × ℤ) :
    D.H P.closed i ≃ₗ[R] support P (i + (2, 1))
  /-- Exactness at ambient cohomology in the localization sequence with supports. -/
  exact_forget_map (P : DivisorPair k) (i : ℤ × ℤ) :
    Function.Exact (forget P i) (D.map P.j i)
  /-- Exactness at open cohomology in the localization sequence with supports. -/
  exact_map_boundary (P : DivisorPair k) (i : ℤ × ℤ) :
    Function.Exact (D.map P.j i) (boundary P i)
  /-- Exactness at supported cohomology in the localization sequence. -/
  exact_boundary_forget (P : DivisorPair k) (i : ℤ × ℤ) :
    Function.Exact (boundary P i) (forget P (i + (1, 0)))
  /-- Transverse pullback in supported cohomology. -/
  supportMap {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ) :
    support P i →ₗ[R] support Q i
  /-- Support-forgetting commutes with transverse pullback. -/
  forget_natural {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ) (x : support P i) :
    forget Q i (supportMap f i x) = D.map f.ambient i (forget P i x)
  /-- The localization connecting homomorphism commutes with transverse pullback. -/
  boundary_natural {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ) (x : D.H P.compl i) :
    boundary Q i (D.map f.compl i x) = supportMap f (i + (1, 0)) (boundary P i x)
  /-- Oriented purity commutes with transverse pullback. -/
  purity_natural {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ) (x : D.H P.closed i) :
    purity Q i (D.map f.closed i x) = supportMap f (i + (2, 1)) (purity P i x)
  /-- The mixed cup product of a supported class with an ambient class. -/
  supportMul (P : DivisorPair k) (i j : ℤ × ℤ) :
    support P i →ₗ[R] D.H P.ambient j →ₗ[R] support P (i + j)
  /-- Forgetting supports preserves mixed products. -/
  forget_mul (P : DivisorPair k) {i j : ℤ × ℤ}
      (x : support P i) (y : D.H P.ambient j) :
    forget P (i + j) (supportMul P i j x y) = GradedMonoid.GMul.mul (forget P i x) y
  /-- Oriented purity respects products with classes from the ambient object. -/
  purity_mul (P : DivisorPair k) {i j : ℤ × ℤ}
      (x : D.H P.closed i) (y : D.H P.ambient j) :
    GradedMonoid.mk ((i + j) + (2, 1))
        (purity P (i + j) (GradedMonoid.GMul.mul x (D.map P.i j y))) =
      GradedMonoid.mk ((i + (2, 1)) + j) (supportMul P (i + (2, 1)) j (purity P i x) y)
  /-- The boundary projection formula, with the open class first and no sign. -/
  boundary_mul (P : DivisorPair k) {i j : ℤ × ℤ}
      (x : D.H P.compl i) (y : D.H P.ambient j) :
    GradedMonoid.mk ((i + j) + (1, 0))
        (boundary P (i + j) (GradedMonoid.GMul.mul x (D.map P.j j y))) =
      GradedMonoid.mk ((i + (1, 0)) + j)
        (supportMul P (i + (1, 0)) j (boundary P i x) y)

namespace SupportsAndPurity

attribute [instance] addCommGroup module

variable {k : Type u} [CommRing k] {R : Type v} [CommRing R]
  {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ]
  {D : DegreewiseTheory.{u, v, w, z} k ℬ} (S : SupportsAndPurity.{u, v, w, z, t} D)

/-- Total cohomology with supports, summed over cohomological degree and twist. -/
abbrev Total (P : DivisorPair k) := ⨁ i, S.support P i

/-- The inclusion of one supported cohomology group in its total direct sum. -/
abbrev incl (P : DivisorPair k) (i : ℤ × ℤ) : S.support P i →ₗ[R] S.Total P :=
  DirectSum.lof R _ (S.support P) i

/-- Support-forgetting on the external direct sums. -/
def forgetTotal (P : DivisorPair k) : S.Total P →ₗ[R] D.Total P.ambient :=
  DirectSum.lmap (S.forget P)

@[simp]
lemma forgetTotal_incl (P : DivisorPair k) (i : ℤ × ℤ) (x : S.support P i) :
    S.forgetTotal P (S.incl P i x) = D.incl P.ambient i (S.forget P i x) :=
  DirectSum.lmap_lof _ _ _

/-- Transverse pullback on total cohomology with supports. -/
def supportMapTotal {P Q : DivisorPair k} (f : P ⟶ Q) : S.Total P →ₗ[R] S.Total Q :=
  DirectSum.lmap (S.supportMap f)

@[simp]
lemma supportMapTotal_incl {P Q : DivisorPair k} (f : P ⟶ Q) (i : ℤ × ℤ)
    (x : S.support P i) :
    S.supportMapTotal f (S.incl P i x) = S.incl Q i (S.supportMap f i x) :=
  DirectSum.lmap_lof _ _ _

/-- Mixed cup product on total supported and ambient cohomology. -/
def supportMulTotal (P : DivisorPair k) :
    S.Total P →ₗ[R] D.Total P.ambient →ₗ[R] S.Total P :=
  DirectSum.toModule R _ _ fun i ↦
    (DirectSum.toModule R _ _ fun j ↦
      ((S.supportMul P i j).compr₂ (S.incl P (i + j))).flip).flip

@[simp]
lemma supportMulTotal_incl (P : DivisorPair k) {i j : ℤ × ℤ}
    (x : S.support P i) (y : D.H P.ambient j) :
    S.supportMulTotal P (S.incl P i x) (D.incl P.ambient j y) =
      S.incl P (i + j) (S.supportMul P i j x y) := by
  simp only [supportMulTotal, incl, DegreewiseTheory.incl, DirectSum.toModule_lof,
    LinearMap.flip_apply, LinearMap.compr₂_apply]

/-- The support-forgetting projection formula holds on total cohomology by bilinearity. -/
lemma forgetTotal_mul (P : DivisorPair k) (x : S.Total P) (y : D.Total P.ambient) :
    S.forgetTotal P (S.supportMulTotal P x y) = S.forgetTotal P x * y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      change S.forgetTotal P (S.supportMulTotal P (S.incl P i x) (D.incl P.ambient j y)) =
        S.forgetTotal P (S.incl P i x) * D.incl P.ambient j y
      rw [S.supportMulTotal_incl, S.forgetTotal_incl, S.forgetTotal_incl, S.forget_mul]
      exact (DirectSum.of_mul_of _ _).symm
    | add y z hy hz => simp [hy, hz, mul_add]
  | add x y hx hy => simp [hx, hy, add_mul]

/-- Support-forgetting commutes with total transverse pullback. -/
lemma forgetTotal_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : S.Total P) :
    S.forgetTotal Q (S.supportMapTotal f x) = D.mapTotal f.ambient (S.forgetTotal P x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    change S.forgetTotal Q (S.supportMapTotal f (S.incl P i x)) =
      D.mapTotal f.ambient (S.forgetTotal P (S.incl P i x))
    rw [S.supportMapTotal_incl, S.forgetTotal_incl, S.forgetTotal_incl,
      D.mapTotal_incl, S.forget_natural]
  | add x y hx hy => simp [hx, hy]

/-- The localization connecting homomorphism on total cohomology, of shift `(1,0)`. -/
def boundaryTotal (P : DivisorPair k) : D.Total P.compl →ₗ[R] S.Total P :=
  shiftedDirectSumMap (D.H P.compl) (S.support P) (1, 0) (S.boundary P)

@[simp]
lemma boundaryTotal_incl (P : DivisorPair k) (i : ℤ × ℤ) (x : D.H P.compl i) :
    S.boundaryTotal P (D.incl P.compl i x) =
      S.incl P (i + (1, 0)) (S.boundary P i x) :=
  shiftedDirectSumMap_lof _ _ _ _ _ _

/-- The boundary map commutes with transverse pullback on total cohomology. -/
lemma boundaryTotal_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : D.Total P.compl) :
    S.boundaryTotal Q (D.mapTotal f.compl x) =
      S.supportMapTotal f (S.boundaryTotal P x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    change S.boundaryTotal Q (D.mapTotal f.compl (D.incl P.compl i x)) =
      S.supportMapTotal f (S.boundaryTotal P (D.incl P.compl i x))
    rw [D.mapTotal_incl, S.boundaryTotal_incl, S.boundaryTotal_incl,
      S.supportMapTotal_incl, S.boundary_natural]
  | add x y hx hy => simp [hx, hy]

/-- The boundary projection formula on the direct sums, obtained by summing homogeneous formulas. -/
lemma boundaryTotal_mul (P : DivisorPair k) (x : D.Total P.compl) (y : D.Total P.ambient) :
    S.boundaryTotal P (x * D.mapTotal P.j y) =
      S.supportMulTotal P (S.boundaryTotal P x) y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      change S.boundaryTotal P (D.incl P.compl i x * D.mapTotal P.j (D.incl P.ambient j y)) =
        S.supportMulTotal P (S.boundaryTotal P (D.incl P.compl i x)) (D.incl P.ambient j y)
      rw [D.mapTotal_incl, D.incl_mul_incl, S.boundaryTotal_incl,
        S.boundaryTotal_incl, S.supportMulTotal_incl]
      exact DirectSum.of_eq_of_gradedMonoid_eq (S.boundary_mul P x y)
    | add y z hy hz => simp [hy, hz, mul_add]
  | add x y hx hy => simp [hx, hy, add_mul]

/-- Support-forgetting preserves bidegrees. -/
lemma isHomogeneousOfShift_forgetTotal (P : DivisorPair k) :
    IsHomogeneousOfShift (directSumGrading (R := R) (S.support P)) (D.grading P.ambient) 0
      (S.forgetTotal P) := by
  rintro i _ ⟨x, rfl⟩
  rw [S.forgetTotal_incl, add_zero]
  exact lof_mem_directSumGrading _ _ _

/-- The connecting homomorphism raises cohomological degree by one and preserves the twist. -/
lemma isHomogeneousOfShift_boundaryTotal (P : DivisorPair k) :
    IsHomogeneousOfShift (D.grading P.compl) (directSumGrading (R := R) (S.support P)) (1, 0)
      (S.boundaryTotal P) :=
  isHomogeneousOfShift_shiftedDirectSumMap _ _ _ _

/-- Exactness at total ambient cohomology, derived from degreewise localization with supports. -/
lemma exact_forgetTotal_map (P : DivisorPair k) :
    Function.Exact (S.forgetTotal P) (D.mapTotal P.j) := by
  apply ((S.isHomogeneousOfShift_forgetTotal P).exact_iff_forall_mem
    (D.isHomogeneousOfShift_mapTotal P.j)).2
  intro i j hij y hy
  have hij' : i = j := by simpa using hij
  clear hij
  subst j
  obtain ⟨y, rfl⟩ := hy
  constructor
  · intro h
    have h' : D.map P.j i y = 0 := DirectSum.of_injective (β := D.H P.compl) _ (by
      rw [D.mapTotal_incl] at h
      simpa only [DirectSum.lof_eq_of, map_zero] using h)
    obtain ⟨x, hx⟩ := (S.exact_forget_map P i y).1 h'
    exact ⟨S.incl P i x, lof_mem_directSumGrading _ _ _, by
      rw [S.forgetTotal_incl, hx]⟩
  · rintro ⟨z, ⟨x, rfl⟩, hx⟩
    have hxy : S.forget P i x = y := DirectSum.of_injective (β := D.H P.ambient) _ (by
      rw [S.forgetTotal_incl] at hx
      exact hx)
    rw [D.mapTotal_incl, ← hxy, (S.exact_forget_map P i _).2 ⟨x, rfl⟩, map_zero]

/-- Exactness at total open cohomology, derived from localization in each degree. -/
lemma exact_map_boundaryTotal (P : DivisorPair k) :
    Function.Exact (D.mapTotal P.j) (S.boundaryTotal P) := by
  apply ((D.isHomogeneousOfShift_mapTotal P.j).exact_iff_forall_mem
    (S.isHomogeneousOfShift_boundaryTotal P)).2
  intro i j hij y hy
  have hij' : i = j := by simpa using hij
  clear hij
  subst j
  obtain ⟨y, rfl⟩ := hy
  constructor
  · intro h
    have h' : S.boundary P i y = 0 := DirectSum.of_injective (β := S.support P) _ (by
      rw [S.boundaryTotal_incl] at h
      simpa only [DirectSum.lof_eq_of, map_zero] using h)
    obtain ⟨x, hx⟩ := (S.exact_map_boundary P i y).1 h'
    exact ⟨D.incl P.ambient i x, lof_mem_directSumGrading _ _ _, by
      rw [D.mapTotal_incl, hx]⟩
  · rintro ⟨z, ⟨x, rfl⟩, hx⟩
    have hxy : D.map P.j i x = y := DirectSum.of_injective (β := D.H P.compl) _ (by
      rw [D.mapTotal_incl] at hx
      exact hx)
    rw [S.boundaryTotal_incl, ← hxy, (S.exact_map_boundary P i _).2 ⟨x, rfl⟩, map_zero]

/-- Exactness at total supported cohomology, derived from the degreewise localization sequence. -/
lemma exact_boundaryTotal_forgetTotal (P : DivisorPair k) :
    Function.Exact (S.boundaryTotal P) (S.forgetTotal P) := by
  apply ((S.isHomogeneousOfShift_boundaryTotal P).exact_iff_forall_mem
    (S.isHomogeneousOfShift_forgetTotal P)).2
  intro i j hij y hy
  subst j
  obtain ⟨y, rfl⟩ := hy
  constructor
  · intro h
    have h' : S.forget P (i + (1, 0)) y = 0 :=
      DirectSum.of_injective (β := D.H P.ambient) _ (by
        rw [S.forgetTotal_incl] at h
        simpa only [DirectSum.lof_eq_of, map_zero] using h)
    obtain ⟨x, hx⟩ := (S.exact_boundary_forget P i y).1 h'
    exact ⟨D.incl P.compl i x, lof_mem_directSumGrading _ _ _, by
      rw [S.boundaryTotal_incl, hx]⟩
  · rintro ⟨z, ⟨x, rfl⟩, hx⟩
    have hxy : S.boundary P i x = y := DirectSum.of_injective (β := S.support P) _ (by
      rw [S.boundaryTotal_incl] at hx
      exact hx)
    rw [S.forgetTotal_incl, ← hxy, (S.exact_boundary_forget P i _).2 ⟨x, rfl⟩, map_zero]

/-- Oriented purity on the total direct sums. It is a reindexed sum of the degreewise purity
equivalences, rather than an additional assumption. -/
def purityTotal (P : DivisorPair k) : D.Total P.closed ≃ₗ[R] S.Total P :=
  shiftedDirectSumEquiv (D.H P.closed) (S.support P) (2, 1) (S.purity P)

@[simp]
lemma purityTotal_incl (P : DivisorPair k) (i : ℤ × ℤ) (x : D.H P.closed i) :
    S.purityTotal P (D.incl P.closed i x) =
      S.incl P (i + (2, 1)) (S.purity P i x) :=
  shiftedDirectSumEquiv_lof _ _ _ _ _ _

/-- Oriented purity on total cohomology has bidegree `(2,1)`. -/
lemma isHomogeneousOfShift_purityTotal (P : DivisorPair k) :
    IsHomogeneousOfShift (D.grading P.closed) (directSumGrading (R := R) (S.support P)) (2, 1)
      (S.purityTotal P) := by
  rintro i _ ⟨x, rfl⟩
  rw [S.purityTotal_incl]
  exact lof_mem_directSumGrading _ _ _

/-- Oriented purity commutes with transverse pullback on total cohomology. -/
lemma purityTotal_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : D.Total P.closed) :
    S.purityTotal Q (D.mapTotal f.closed x) = S.supportMapTotal f (S.purityTotal P x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    change S.purityTotal Q (D.mapTotal f.closed (D.incl P.closed i x)) =
      S.supportMapTotal f (S.purityTotal P (D.incl P.closed i x))
    rw [D.mapTotal_incl, S.purityTotal_incl, S.purityTotal_incl,
      S.supportMapTotal_incl, S.purity_natural]
  | add x y hx hy => simp [hx, hy]

/-- Purity respects the product with an ambient class, on total cohomology. -/
lemma purityTotal_mul (P : DivisorPair k) (x : D.Total P.closed) (y : D.Total P.ambient) :
    S.purityTotal P (x * D.mapTotal P.i y) =
      S.supportMulTotal P (S.purityTotal P x) y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of j y =>
      change S.purityTotal P (D.incl P.closed i x * D.mapTotal P.i (D.incl P.ambient j y)) =
        S.supportMulTotal P (S.purityTotal P (D.incl P.closed i x)) (D.incl P.ambient j y)
      rw [D.mapTotal_incl, D.incl_mul_incl, S.purityTotal_incl,
        S.purityTotal_incl, S.supportMulTotal_incl]
      exact DirectSum.of_eq_of_gradedMonoid_eq (S.purity_mul P x y)
    | add y z hy hz => simp [hy, hz, mul_add]
  | add x y hx hy => simp [hx, hy, add_mul]

/-- The Gysin map, constructed as oriented purity followed by forgetting supports. -/
def gysinR (P : DivisorPair k) : D.Total P.closed →ₗ[R] D.Total P.ambient :=
  (S.forgetTotal P).comp (S.purityTotal P).toLinearMap

/-- The residue map, constructed as the localization boundary followed by inverse purity. -/
def residueR (P : DivisorPair k) : D.Total P.compl →ₗ[R] D.Total P.closed :=
  (S.purityTotal P).symm.toLinearMap.comp (S.boundaryTotal P)

/-- The Gysin map has bidegree `(2,1)`. -/
lemma isHomogeneousOfShift_gysinR (P : DivisorPair k) :
    IsHomogeneousOfShift (D.grading P.closed) (D.grading P.ambient) (2, 1) (S.gysinR P) := by
  intro i x hx
  change S.forgetTotal P (S.purityTotal P x) ∈ D.grading P.ambient (i + (2, 1))
  simpa only [add_zero] using
    S.isHomogeneousOfShift_forgetTotal P (S.isHomogeneousOfShift_purityTotal P hx)

/-- The residue map has bidegree `(-1,-1)`. -/
lemma isHomogeneousOfShift_residueR (P : DivisorPair k) :
    IsHomogeneousOfShift (D.grading P.compl) (D.grading P.closed) (-1, -1) (S.residueR P) := by
  intro i x hx
  change (S.purityTotal P).symm (S.boundaryTotal P x) ∈ D.grading P.closed (i + (-1, -1))
  have h := (S.isHomogeneousOfShift_purityTotal P).linearEquiv_symm
    (S.isHomogeneousOfShift_boundaryTotal P hx)
  simpa only [add_assoc, show (1, 0) + -(2, 1) = ((-1, -1) : ℤ × ℤ) from rfl] using h

/-- The Gysin projection formula follows from the product identities for purity and supports. -/
lemma gysinR_mul_map (P : DivisorPair k) (x : D.Total P.closed) (y : D.Total P.ambient) :
    S.gysinR P (x * D.mapTotal P.i y) = S.gysinR P x * y := by
  change S.forgetTotal P (S.purityTotal P (x * D.mapTotal P.i y)) = _
  rw [S.purityTotal_mul, S.forgetTotal_mul]
  rfl

/-- The residue projection formula follows from the boundary formula and oriented purity. -/
lemma residueR_mul_map (P : DivisorPair k) (x : D.Total P.compl) (y : D.Total P.ambient) :
    S.residueR P (x * D.mapTotal P.j y) = S.residueR P x * D.mapTotal P.i y := by
  apply (S.purityTotal P).injective
  change S.purityTotal P ((S.purityTotal P).symm
      (S.boundaryTotal P (x * D.mapTotal P.j y))) =
    S.purityTotal P ((S.purityTotal P).symm (S.boundaryTotal P x) * D.mapTotal P.i y)
  rw [LinearEquiv.apply_symm_apply, S.purityTotal_mul, LinearEquiv.apply_symm_apply,
    S.boundaryTotal_mul]

/-- Gysin naturality follows from the support-forgetting and purity squares. -/
lemma gysinR_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : D.Total P.closed) :
    S.gysinR Q (D.mapTotal f.closed x) = D.mapTotal f.ambient (S.gysinR P x) := by
  change S.forgetTotal Q (S.purityTotal Q (D.mapTotal f.closed x)) = _
  rw [S.purityTotal_natural, S.forgetTotal_natural]
  rfl

/-- Residue naturality follows from the localization boundary and purity squares. -/
lemma residueR_natural {P Q : DivisorPair k} (f : P ⟶ Q) (x : D.Total P.compl) :
    S.residueR Q (D.mapTotal f.compl x) = D.mapTotal f.closed (S.residueR P x) := by
  apply (S.purityTotal Q).injective
  change S.purityTotal Q ((S.purityTotal Q).symm
      (S.boundaryTotal Q (D.mapTotal f.compl x))) =
    S.purityTotal Q (D.mapTotal f.closed ((S.purityTotal P).symm (S.boundaryTotal P x)))
  rw [LinearEquiv.apply_symm_apply, S.purityTotal_natural, LinearEquiv.apply_symm_apply,
    S.boundaryTotal_natural]

/-- Exactness at ambient cohomology after using purity to replace support groups. -/
lemma exact_gysinR_map (P : DivisorPair k) :
    Function.Exact (S.gysinR P) (D.mapTotal P.j) := by
  intro x
  rw [S.exact_forgetTotal_map P x]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(S.purityTotal P).symm y, by simp [gysinR]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨S.purityTotal P y, rfl⟩

/-- Exactness at open cohomology after using inverse purity in the residue map. -/
lemma exact_map_residueR (P : DivisorPair k) :
    Function.Exact (D.mapTotal P.j) (S.residueR P) := by
  intro x
  change (S.purityTotal P).symm (S.boundaryTotal P x) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, S.exact_map_boundaryTotal P x]

/-- Exactness at divisor cohomology after identifying it with shifted supported cohomology. -/
lemma exact_residueR_gysinR (P : DivisorPair k) :
    Function.Exact (S.residueR P) (S.gysinR P) := by
  intro x
  change S.forgetTotal P (S.purityTotal P x) = 0 ↔ _
  rw [S.exact_boundaryTotal_forgetTotal P (S.purityTotal P x)]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simp only [residueR, LinearMap.comp_apply,
      LinearEquiv.coe_coe, hy, LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp [residueR]⟩

/-- The Gysin map is linear over the whole coefficient ring, including nonzero weights. This
follows from the homogeneous mixed-product identities, not from an extra linearity assumption. -/
lemma gysinR_smul (P : DivisorPair k) (b : B) (x : D.Total P.closed) :
    S.gysinR P (b • x) = b • S.gysinR P x := by
  calc
    S.gysinR P (b • x) =
        S.gysinR P (x * D.mapTotal P.i (algebraMap B (D.Total P.ambient) b)) := by
      rw [AlgHom.commutes, Algebra.smul_def, Algebra.commutes]
    _ = S.gysinR P x * algebraMap B (D.Total P.ambient) b := S.gysinR_mul_map P x _
    _ = b • S.gysinR P x := by rw [Algebra.smul_def, Algebra.commutes]

/-- The residue map is linear over the whole coefficient ring, by the boundary and purity
projection formulas. -/
lemma residueR_smul (P : DivisorPair k) (b : B) (x : D.Total P.compl) :
    S.residueR P (b • x) = b • S.residueR P x := by
  calc
    S.residueR P (b • x) =
        S.residueR P (x * D.mapTotal P.j (algebraMap B (D.Total P.ambient) b)) := by
      rw [AlgHom.commutes, Algebra.smul_def, Algebra.commutes]
    _ = S.residueR P x * D.mapTotal P.i (algebraMap B (D.Total P.ambient) b) :=
      S.residueR_mul_map P x _
    _ = b • S.residueR P x := by rw [AlgHom.commutes, Algebra.smul_def, Algebra.commutes]

/-- The Gysin map, bundled as a `B`-linear map. -/
def gysin (P : DivisorPair k) : D.Total P.closed →ₗ[B] D.Total P.ambient where
  toFun := S.gysinR P
  map_add' := map_add _
  map_smul' := S.gysinR_smul P

/-- The residue map, bundled as a `B`-linear map. -/
def residue (P : DivisorPair k) : D.Total P.compl →ₗ[B] D.Total P.closed where
  toFun := S.residueR P
  map_add' := map_add _
  map_smul' := S.residueR_smul P

end SupportsAndPurity

end OrlikSolomon
