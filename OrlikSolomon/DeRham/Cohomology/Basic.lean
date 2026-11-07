/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import OrlikSolomon.Algebra.RelationQuotient
public import OrlikSolomon.DeRham.Complex

/-!
# The de Rham cohomology algebra

For a commutative algebra `A` over a commutative ring `k`, with no smoothness hypothesis, this file
defines the total de Rham cohomology `H^•_dR(A/k)` as a `k`-algebra, covariantly functorial in `A`.
The closed forms are a `k`-subalgebra of all forms, and the exact forms are a two-sided ideal **in
that subalgebra**. They are not an ideal of the algebra of all forms: a function times an exact form
need not even be closed.

The degree pieces, the identification of a piece with `ker d / im d`, and graded commutativity are
in `DeRham/Cohomology/Degree`.

## Main definitions

* `OrlikSolomon.DeRham.cycles k A`: the closed forms, as a `k`-subalgebra of forms.
* `OrlikSolomon.DeRham.boundaries k A`: the exact forms, as a two-sided ideal of the closed forms.
* `OrlikSolomon.DeRham.Cohomology k A`: the total cohomology, which is a `k`-algebra.
* `OrlikSolomon.DeRham.Cohomology.mk x hx`: the class of a closed form `x`.
* `OrlikSolomon.DeRham.Cohomology.lift` and `OrlikSolomon.DeRham.Cohomology.liftLinear`: algebra and
  linear maps out of cohomology, from maps on closed forms killing exact forms.
* `OrlikSolomon.DeRham.Cohomology.map φ`: the algebra map induced by `φ : A →ₐ[k] A'`.
* `OrlikSolomon.DeRham.cohomologyFunctor k`: cohomology as a functor to `k`-algebras.

## Main results

* `OrlikSolomon.DeRham.Cohomology.mk_eq_mk_iff`, `OrlikSolomon.DeRham.Cohomology.mk_eq_zero_iff`:
  when two closed forms are cohomologous. Hide the quotient behind these.
* `OrlikSolomon.DeRham.Cohomology.induction`: every class is the class of a closed form.
* `OrlikSolomon.DeRham.Cohomology.map_id`, `OrlikSolomon.DeRham.Cohomology.map_comp`,
  `OrlikSolomon.DeRham.Cohomology.map_map`: functoriality.
* `OrlikSolomon.DeRham.Cohomology.map_eq_map_of_homotopy`: chain homotopic maps agree on cohomology.

## Normal form

Sums, products, scalar multiples and negatives of classes of closed forms are combined by `simp`
into one class, as in `mk_mul : mk x hx * mk y hy = mk (x * y) _`. The opposite direction cannot be
a rewrite rule, since `x * y` can be closed when `x` and `y` are not.

## Blueprint

`def:dr-cohomology`. See `OrlikSolomon/DeRham/Cohomology.lean` for the summary.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CliffordAlgebra (involute)

namespace OrlikSolomon.DeRham

universe u v v' v''

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  {A' : Type v'} [CommRing A'] [Algebra k A'] {A'' : Type v''} [CommRing A''] [Algebra k A'']

/-! ### Cycles and boundaries -/

/-- The closed forms, as a `k`-subalgebra of all forms. They are not an `A`-submodule, since `d` is
not `A`-linear. They contain every degree of a closed form, by `decompose_mem_cycles`.

Blueprint: `def:dr-cohomology`. -/
def cycles : Subalgebra k (Forms k A) where
  carrier := {x | d k x = 0}
  mul_mem' {x y} (hx : d k x = 0) (hy : d k y = 0) := by
    change d k (x * y) = 0
    rw [d_mul, hx, hy, zero_mul, mul_zero, add_zero]
  add_mem' {x y} (hx : d k x = 0) (hy : d k y = 0) := by
    change d k (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  algebraMap_mem' c := by
    change d k (algebraMap k (Forms k A) c) = 0
    rw [IsScalarTower.algebraMap_apply k A (Forms k A), d_algebraMap, Derivation.map_algebraMap]

variable {k A} in
@[simp]
theorem mem_cycles {x : Forms k A} : x ∈ cycles k A ↔ d k x = 0 :=
  Iff.rfl

/-- The exact forms, as a two-sided ideal of the closed forms.

They are an ideal here and not in all forms. The left multiple `x ∧ dy` of a boundary by a closed
form is `d (σ x ∧ y)`, by `mul_d_of_d_eq_zero`, with `σ` the grade involution, so no degree of `x`
is involved. The right multiple `dy ∧ x` is `d (y ∧ x)`, by `d_mul`.

Blueprint: `def:dr-cohomology`. -/
def boundaries : TwoSidedIdeal (cycles k A) :=
  .mk' {z | ∃ y, d k y = (z : Forms k A)}
    ⟨0, by simp⟩
    (by rintro _ _ ⟨x, hx⟩ ⟨y, hy⟩; exact ⟨x + y, by simp [hx, hy]⟩)
    (by rintro _ ⟨x, hx⟩; exact ⟨-x, by simp [hx]⟩)
    (by
      rintro x _ ⟨y, hy⟩
      exact ⟨involute (x : Forms k A) * y, by
        rw [Subalgebra.coe_mul, ← hy, mul_d_of_d_eq_zero k x.2]⟩)
    (by
      rintro _ x ⟨y, hy⟩
      exact ⟨y * x, by rw [d_mul, mem_cycles.1 x.2, mul_zero, add_zero, hy, Subalgebra.coe_mul]⟩)

variable {k A} in
@[simp]
theorem mem_boundaries {z : cycles k A} : z ∈ boundaries k A ↔ ∃ y, d k y = (z : Forms k A) :=
  TwoSidedIdeal.mem_mk' ..

/-! ### The cohomology algebra -/

/-- The total de Rham cohomology `H^•_dR(A/k)`, which is the quotient of the closed forms by the
exact forms. It is a `k`-algebra with the product induced by the wedge product, and the unit is the
class of `1`. It is the direct sum of its degree pieces, `Cohomology.degree k A`, and it is graded
commutative. It is not an `A`-module: multiplication by a function does not preserve closed forms.

The total algebra comes first because forms and `d` do: see `docs/ARCHITECTURE.md`.

Blueprint: `def:dr-cohomology`. -/
def Cohomology : Type v :=
  RelationQuotient (boundaries k A : Set (cycles k A))

namespace Cohomology

-- Keep the transported action visible to instance synthesis, including the canonical
-- natural and integer actions inherited by the ring structure. See `RelationQuotient`.
instance instSMul {S : Type*} [CommSemiring S] [Algebra S (cycles k A)] : SMul S (Cohomology k A) :=
  inferInstanceAs (SMul S (RelationQuotient (boundaries k A : Set (cycles k A))))

instance : Ring (Cohomology k A) :=
  inferInstanceAs (Ring (RelationQuotient (boundaries k A : Set (cycles k A))))

instance instAlgebra {S : Type*} [CommSemiring S] [Algebra S (cycles k A)] :
    Algebra S (Cohomology k A) :=
  inferInstanceAs (Algebra S (RelationQuotient (boundaries k A : Set (cycles k A))))

instance {S S' : Type*} [CommSemiring S] [CommSemiring S'] [Algebra S (cycles k A)]
    [Algebra S' (cycles k A)] [SMul S S'] [IsScalarTower S S' (cycles k A)] :
    IsScalarTower S S' (Cohomology k A) :=
  inferInstanceAs (IsScalarTower S S' (RelationQuotient (boundaries k A : Set (cycles k A))))

instance {S S' : Type*} [CommSemiring S] [CommSemiring S'] [Algebra S (cycles k A)]
    [Algebra S' (cycles k A)] [SMulCommClass S S' (cycles k A)] :
    SMulCommClass S S' (Cohomology k A) :=
  inferInstanceAs (SMulCommClass S S' (RelationQuotient (boundaries k A : Set (cycles k A))))

-- Verify that there is no diamond, as for `RelationQuotient`.
example : (Semiring.toNatAlgebra : Algebra ℕ (Cohomology k A)) = instAlgebra k A := rfl
example : (Ring.toIntAlgebra _ : Algebra ℤ (Cohomology k A)) = instAlgebra k A := rfl

/-- The quotient map from the closed forms, as an algebra map. `simp` rewrites `mkₐ k A z` to
`mk z z.2`. -/
def mkₐ : cycles k A →ₐ[k] Cohomology k A :=
  RelationQuotient.mkₐ k _

variable {k A}

/-- The class of a closed form.

Blueprint: `def:dr-cohomology`. -/
def mk (x : Forms k A) (hx : d k x = 0) : Cohomology k A :=
  mkₐ k A ⟨x, hx⟩

@[simp]
theorem mkₐ_apply (z : cycles k A) : mkₐ k A z = mk (z : Forms k A) z.2 :=
  rfl

/-- The class depends on the form and on nothing else. This is for changing a form to an equal one
inside a class. -/
theorem mk_congr {x y : Forms k A} (h : x = y) (hx : d k x = 0) : mk x hx = mk y (h ▸ hx) := by
  subst h
  rfl

theorem mkₐ_surjective : Function.Surjective (mkₐ k A) :=
  RelationQuotient.mkₐ_surjective

/-- Every class is the class of a closed form. -/
theorem exists_mk_eq (c : Cohomology k A) : ∃ (x : Forms k A) (hx : d k x = 0), mk x hx = c := by
  obtain ⟨z, rfl⟩ := mkₐ_surjective c
  exact ⟨z, z.2, rfl⟩

/-- Induction over classes: every class is the class of a closed form. See
`Cohomology.induction_degree` for homogeneous forms.

Blueprint: `def:dr-cohomology`. -/
@[elab_as_elim, induction_eliminator]
protected theorem induction {motive : Cohomology k A → Prop}
    (mk : ∀ (x : Forms k A) (hx : d k x = 0), motive (mk x hx)) (c : Cohomology k A) :
    motive c := by
  obtain ⟨x, hx, rfl⟩ := exists_mk_eq c
  exact mk x hx

/-! ### When classes agree -/

/-- A closed form has zero class exactly when it is exact.

Blueprint: `def:dr-cohomology`. -/
theorem mk_eq_zero_iff {x : Forms k A} {hx : d k x = 0} : mk x hx = 0 ↔ ∃ y, d k y = x := by
  have h : mk x hx = 0 ↔ (⟨x, hx⟩ : cycles k A) ∈
      relationSubmodule k (boundaries k A : Set (cycles k A)) :=
    RelationQuotient.mk_eq_zero_iff k
  rw [h, mem_relationSubmodule_coe_twoSidedIdeal, mem_boundaries]

/-- Two closed forms have the same class exactly when they differ by an exact form.

Blueprint: `def:dr-cohomology`. -/
theorem mk_eq_mk_iff {x x' : Forms k A} {hx : d k x = 0} {hx' : d k x' = 0} :
    mk x hx = mk x' hx' ↔ ∃ y, d k y = x - x' := by
  have h : mk x hx = mk x' hx' ↔ (⟨x, hx⟩ - ⟨x', hx'⟩ : cycles k A) ∈
      relationSubmodule k (boundaries k A : Set (cycles k A)) :=
    RelationQuotient.mk_eq_mk_iff k
  rw [h, mem_relationSubmodule_coe_twoSidedIdeal, mem_boundaries]
  rfl

/-- An exact form has zero class. -/
@[simp]
theorem mk_d (y : Forms k A) (h : d k (d k y) = 0) : mk (d k y) h = 0 :=
  mk_eq_zero_iff.2 ⟨y, rfl⟩

/-- Adding an exact form does not change the class. -/
@[simp]
theorem mk_add_d (x y : Forms k A) (h : d k (x + d k y) = 0) :
    mk (x + d k y) h = mk x (by simpa using h) :=
  mk_eq_mk_iff.2 ⟨y, by simp⟩

/-- A differential has zero class. -/
@[simp]
theorem mk_diff (a : A) (h : d k (diff k a) = 0) : mk (diff k a) h = 0 :=
  mk_eq_zero_iff.2 ⟨algebraMap A (Forms k A) a, d_algebraMap k a⟩

/-! ### The operations on classes -/

@[simp]
theorem mk_zero (h : d k (0 : Forms k A) = 0) : mk (0 : Forms k A) h = 0 :=
  map_zero (mkₐ k A)

@[simp]
theorem mk_one (h : d k (1 : Forms k A) = 0) : mk (1 : Forms k A) h = 1 :=
  map_one (mkₐ k A)

/-- The class of a scalar is the scalar. -/
@[simp]
theorem mk_algebraMap (c : k) (h : d k (algebraMap k (Forms k A) c) = 0) :
    mk (algebraMap k (Forms k A) c) h = algebraMap k (Cohomology k A) c :=
  (mkₐ k A).commutes c

@[simp]
theorem mk_add (x x' : Forms k A) (hx : d k x = 0) (hx' : d k x' = 0) :
    mk x hx + mk x' hx' =
      mk (x + x') (mem_cycles.1 (add_mem (mem_cycles.2 hx) (mem_cycles.2 hx'))) :=
  (map_add (mkₐ k A) ⟨x, hx⟩ ⟨x', hx'⟩).symm

@[simp]
theorem mk_neg (x : Forms k A) (hx : d k x = 0) :
    -mk x hx = mk (-x) (mem_cycles.1 (neg_mem (mem_cycles.2 hx))) :=
  (map_neg (mkₐ k A) ⟨x, hx⟩).symm

@[simp]
theorem mk_sub (x x' : Forms k A) (hx : d k x = 0) (hx' : d k x' = 0) :
    mk x hx - mk x' hx' =
      mk (x - x') (mem_cycles.1 (sub_mem (mem_cycles.2 hx) (mem_cycles.2 hx'))) :=
  (map_sub (mkₐ k A) ⟨x, hx⟩ ⟨x', hx'⟩).symm

/-- The product of classes is the class of the wedge product.

Blueprint: `def:dr-cohomology`. -/
@[simp]
theorem mk_mul (x x' : Forms k A) (hx : d k x = 0) (hx' : d k x' = 0) :
    mk x hx * mk x' hx' =
      mk (x * x') (mem_cycles.1 (mul_mem (mem_cycles.2 hx) (mem_cycles.2 hx'))) :=
  (map_mul (mkₐ k A) ⟨x, hx⟩ ⟨x', hx'⟩).symm

@[simp]
theorem mk_pow (x : Forms k A) (hx : d k x = 0) (n : ℕ) :
    mk x hx ^ n = mk (x ^ n) (mem_cycles.1 (pow_mem (mem_cycles.2 hx) n)) :=
  (map_pow (mkₐ k A) ⟨x, hx⟩ n).symm

@[simp]
theorem mk_smul (c : k) (x : Forms k A) (hx : d k x = 0) :
    c • mk x hx = mk (c • x) (mem_cycles.1 ((cycles k A).smul_mem (mem_cycles.2 hx) c)) :=
  (map_smul (mkₐ k A) c (⟨x, hx⟩ : cycles k A)).symm

@[simp]
theorem mk_sum {ι : Type*} (s : Finset ι) (x : ι → Forms k A) (hx : ∀ i, d k (x i) = 0) :
    ∑ i ∈ s, mk (x i) (hx i) =
      mk (∑ i ∈ s, x i) (mem_cycles.1 (sum_mem fun i _ => mem_cycles.2 (hx i))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/-- Cohomology of the zero ring is zero. -/
instance [Subsingleton A] : Subsingleton (Cohomology k A) :=
  ⟨fun c c' => by
    induction c with
    | mk x hx =>
      induction c' with
      | mk y hy => exact mk_congr (Subsingleton.elim x y) hx⟩

/-! ### Maps out of cohomology -/

section Lift

variable {T : Type*} [Semiring T] [Algebra k T] {M : Type*} [AddCommMonoid M] [Module k M]

/-- An algebra map on closed forms that kills exact forms descends to cohomology. -/
def lift (f : cycles k A →ₐ[k] T) (hf : ∀ y, f ⟨d k y, d_d k y⟩ = 0) : Cohomology k A →ₐ[k] T :=
  RelationQuotient.liftAlgHom f fun z hz => by
    obtain ⟨y, hy⟩ := mem_boundaries.1 hz
    rw [show z = ⟨d k y, d_d k y⟩ from Subtype.ext hy.symm, hf]

@[simp]
theorem lift_mk (f : cycles k A →ₐ[k] T) (hf : ∀ y, f ⟨d k y, d_d k y⟩ = 0) (x : Forms k A)
    (hx : d k x = 0) : lift f hf (mk x hx) = f ⟨x, hx⟩ :=
  rfl

/-- A `k`-linear map on closed forms that kills exact forms descends to cohomology. It need not be
multiplicative, and there is no degree in the statement. This is the form to use for a map with a
sign or a shift, such as a residue. -/
def liftLinear (f : cycles k A →ₗ[k] M) (hf : ∀ y, f ⟨d k y, d_d k y⟩ = 0) :
    Cohomology k A →ₗ[k] M :=
  RelationQuotient.liftLinear f fun z hz => by
    obtain ⟨y, hy⟩ := mem_boundaries.1 ((mem_relationSubmodule_coe_twoSidedIdeal _).1 hz)
    rw [LinearMap.mem_ker, show z = ⟨d k y, d_d k y⟩ from Subtype.ext hy.symm, hf]

@[simp]
theorem liftLinear_mk (f : cycles k A →ₗ[k] M) (hf : ∀ y, f ⟨d k y, d_d k y⟩ = 0) (x : Forms k A)
    (hx : d k x = 0) : liftLinear f hf (mk x hx) = f ⟨x, hx⟩ :=
  RelationQuotient.liftLinear_mk f _ _

/-- Algebra maps out of cohomology agree if they agree on the classes of closed forms. -/
@[ext]
theorem algHom_ext {f g : Cohomology k A →ₐ[k] T}
    (h : ∀ (x : Forms k A) (hx : d k x = 0), f (mk x hx) = g (mk x hx)) : f = g :=
  AlgHom.ext fun c => by
    induction c with
    | mk x hx => exact h x hx

/-- Linear maps out of cohomology agree if they agree on the classes of closed forms. -/
@[ext]
theorem linearMap_ext {f g : Cohomology k A →ₗ[k] M}
    (h : ∀ (x : Forms k A) (hx : d k x = 0), f (mk x hx) = g (mk x hx)) : f = g :=
  LinearMap.ext fun c => by
    induction c with
    | mk x hx => exact h x hx

end Lift

/-! ### Functoriality -/

/-- The map on forms of an algebra map, restricted to closed forms. -/
def cyclesMap (φ : A →ₐ[k] A') : cycles k A →ₐ[k] cycles k A' :=
  ((Forms.map φ).comp (cycles k A).val).codRestrict (cycles k A') fun z => by
    simp only [AlgHom.comp_apply, Subalgebra.coe_val, mem_cycles]
    rw [← Forms.map_d, mem_cycles.1 z.2, map_zero]

@[simp]
theorem coe_cyclesMap (φ : A →ₐ[k] A') (z : cycles k A) :
    (cyclesMap φ z : Forms k A') = Forms.map φ z :=
  rfl

/-- An algebra map preserves closed forms. -/
theorem d_map_eq_zero (φ : A →ₐ[k] A') {x : Forms k A} (hx : d k x = 0) : d k (Forms.map φ x) = 0 :=
  (cyclesMap φ ⟨x, hx⟩).2

/-- The `k`-algebra map on cohomology induced by a `k`-algebra map, covariantly. It sends the class
of `x` to the class of `Forms.map φ x`.

Blueprint: `def:dr-cohomology`. -/
def map (φ : A →ₐ[k] A') : Cohomology k A →ₐ[k] Cohomology k A' :=
  lift ((mkₐ k A').comp (cyclesMap φ)) fun y =>
    mk_eq_zero_iff.2 ⟨Forms.map φ y, (Forms.map_d φ y).symm⟩

/-- The induced map on a class.

Blueprint: `def:dr-cohomology`. -/
@[simp]
theorem map_mk (φ : A →ₐ[k] A') (x : Forms k A) (hx : d k x = 0) :
    map φ (mk x hx) = mk (Forms.map φ x) (d_map_eq_zero φ hx) :=
  rfl

/-- The identity induces the identity.

Blueprint: `def:dr-cohomology`. -/
@[simp]
theorem map_id : map (AlgHom.id k A) = AlgHom.id k (Cohomology k A) := by
  ext x hx
  simp only [map_mk, AlgHom.id_apply]
  exact mk_congr (by simp) _

/-- `map` respects composition, as an equation of algebra maps.

Blueprint: `def:dr-cohomology`. -/
theorem map_comp (ψ : A' →ₐ[k] A'') (φ : A →ₐ[k] A') :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  ext x hx
  simp only [map_mk, AlgHom.comp_apply]
  exact mk_congr (by simp) _

/-- `map` respects composition.

Blueprint: `def:dr-cohomology`. -/
@[simp]
theorem map_map (ψ : A' →ₐ[k] A'') (φ : A →ₐ[k] A') (c : Cohomology k A) :
    map ψ (map φ c) = map (ψ.comp φ) c := by
  rw [map_comp, AlgHom.comp_apply]

/-- The equivalence on cohomology of an equivalence of algebras. -/
def mapEquiv (e : A ≃ₐ[k] A') : Cohomology k A ≃ₐ[k] Cohomology k A' :=
  AlgEquiv.ofAlgHom (map e.toAlgHom) (map e.symm.toAlgHom)
    (by rw [← map_comp]; simp) (by rw [← map_comp]; simp)

@[simp]
theorem mapEquiv_apply (e : A ≃ₐ[k] A') (c : Cohomology k A) : mapEquiv e c = map e.toAlgHom c :=
  rfl

@[simp]
theorem mapEquiv_symm_apply (e : A ≃ₐ[k] A') (c : Cohomology k A') :
    (mapEquiv e).symm c = map e.symm.toAlgHom c :=
  rfl

/-! ### Chain homotopies -/

/-- Two algebra maps agree on cohomology as soon as their maps on forms differ by an exact form on
each closed form. The operator of a chain homotopy is the usual witness: see
`map_eq_map_of_homotopy`. -/
theorem map_eq_map_of_exists {φ ψ : A →ₐ[k] A'}
    (h : ∀ x : Forms k A, d k x = 0 → ∃ y, d k y = Forms.map φ x - Forms.map ψ x) :
    map φ = map ψ := by
  ext x hx
  exact mk_eq_mk_iff.2 (h x hx)

/-- Chain homotopic algebra maps agree on cohomology. The homotopy `K` is an operator on total
forms, as `d` is, and its degree is not used. It need only be additive: it can be `k`-linear, as an
integration operator is, and it is not expected to be multiplicative or linear over `A`.

Blueprint: used by `thm:dr-homotopy`, with `K` the integration homotopy. -/
theorem map_eq_map_of_homotopy {φ ψ : A →ₐ[k] A'} {F : Type*} [FunLike F (Forms k A) (Forms k A')]
    [AddMonoidHomClass F (Forms k A) (Forms k A')] (K : F)
    (hK : ∀ x, Forms.map φ x - Forms.map ψ x = d k (K x) + K (d k x)) : map φ = map ψ :=
  map_eq_map_of_exists fun x hx => ⟨K x, by rw [hK, hx, map_zero, add_zero]⟩

end Cohomology

/-! ### The functor -/

/-- De Rham cohomology, as a functor from commutative `k`-algebras to `k`-algebras. Mathlib's
`CommAlgCat` is the covariant convention, so that a map `A → A'` of algebras goes to a map in the
same direction. The target is `AlgCat`, since cohomology is only graded commutative.

Blueprint: `def:dr-cohomology`. -/
def cohomologyFunctor : CommAlgCat.{v} k ⥤ AlgCat.{v} k where
  obj B := AlgCat.of k (Cohomology k B)
  map f := AlgCat.ofHom (Cohomology.map f.hom)
  map_id B := by
    ext : 1
    exact Cohomology.map_id
  map_comp f g := by
    ext : 1
    exact Cohomology.map_comp g.hom f.hom

variable {k}

@[simp]
theorem cohomologyFunctor_obj (B : CommAlgCat.{v} k) :
    (cohomologyFunctor k).obj B = AlgCat.of k (Cohomology k B) :=
  rfl

@[simp]
theorem cohomologyFunctor_map_hom {B C : CommAlgCat.{v} k} (f : B ⟶ C) :
    ((cohomologyFunctor k).map f).hom = Cohomology.map f.hom :=
  rfl

end OrlikSolomon.DeRham
