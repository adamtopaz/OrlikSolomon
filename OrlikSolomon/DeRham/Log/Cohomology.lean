/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Cohomology
public import OrlikSolomon.DeRham.Log.Basic

/-!
# The cohomology of the logarithmic complex

For a localization `T` of a commutative `k`-algebra `A` away from `f`, this file defines the
cohomology `H^•(L)` of the logarithmic forms as a `k`-algebra, with its maps
`H^•(A) → H^•(L) → H^•(T)` of algebras. These are the maps of `thm:dr-comparison` and
`lem:dr-exactness`. Nothing here needs smoothness, or that `f` is a non-zero-divisor.

The construction is that of `Cohomology k T`, with logarithmic forms for all forms. The closed
logarithmic forms are a `k`-subalgebra of forms, and the differentials of logarithmic forms are a
two-sided ideal of it, because the grade involution preserves logarithmic forms.

## Main definitions

* `OrlikSolomon.DeRham.logCycles k f T`: the closed logarithmic forms, as a `k`-subalgebra of forms.
* `OrlikSolomon.DeRham.logBoundaries k f T`: the differentials of logarithmic forms, as a two-sided
  ideal of the closed logarithmic forms.
* `OrlikSolomon.DeRham.LogCohomology k f T`: the total cohomology of the logarithmic forms.
* `OrlikSolomon.DeRham.LogCohomology.mk x hx`: the class of `x : logForms k f T`, for
  `hx : logD k f T x = 0`.
* `OrlikSolomon.DeRham.LogCohomology.degree k f T n`: the piece `H^n(L)`, for `n : ℕ`.
* `OrlikSolomon.DeRham.LogCohomology.grading k f T p`: the same grading, indexed by `p : ℤ`, zero in
  negative degrees.
* `OrlikSolomon.DeRham.LogCohomology.toCohomology k f T`: the map `H^•(L) → H^•(T)` of algebras, the
  map of `thm:dr-comparison`.
* `OrlikSolomon.DeRham.LogCohomology.ofCohomology k f T`: the map `H^•(A) → H^•(L)` of algebras.

## Main results

* `OrlikSolomon.DeRham.LogCohomology.mk_eq_zero_iff`,
  `OrlikSolomon.DeRham.LogCohomology.mk_eq_mk_iff`: when two closed logarithmic forms are
  cohomologous **in `L`**. Hide the quotient behind these.
* `OrlikSolomon.DeRham.LogCohomology.mem_degree_iff`: `H^n(L)` consists of the classes of the closed
  logarithmic forms of degree `n`, and
  `OrlikSolomon.DeRham.LogCohomology.mk_eq_zero_iff_of_mem_logPower_succ` says that a primitive of
  such a form can be taken logarithmic of degree `n - 1`, with
  `OrlikSolomon.DeRham.LogCohomology.mk_eq_zero_iff_of_mem_logPower_zero` for `n = 0`.
* `OrlikSolomon.DeRham.LogCohomology.toCohomology_mk`,
  `OrlikSolomon.DeRham.LogCohomology.ofCohomology_mk`: the maps on representatives.
* `OrlikSolomon.DeRham.LogCohomology.toCohomology_ofCohomology`: the composite `H^•(A) → H^•(T)` is
  the functoriality of cohomology along `A → T`.
* `OrlikSolomon.DeRham.LogCohomology.isHomogeneousOfShift_toCohomology`,
  `OrlikSolomon.DeRham.LogCohomology.isHomogeneousOfShift_ofCohomology`: the maps preserve degree.
* `OrlikSolomon.DeRham.LogCohomology.bijective_toCohomology_of_forall`: the bijectivity of
  `toCohomology`, in terms of forms. This is what `thm:dr-comparison` proves.

## Blueprint

`thm:dr-comparison` and `def:dr-gysin` use the cohomology of `L`, and the blueprint does not name it
separately. This file supplies it, as "Cohomology" in `docs/ARCHITECTURE.md` describes.
-/

@[expose] public section

noncomputable section

open CliffordAlgebra (involute)
open DirectSum

namespace OrlikSolomon.DeRham

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

local notation "reg" => Forms.map (IsScalarTower.toAlgHom k A T)
local notation "θ" => theta k f T

omit [Algebra k A] [IsScalarTower k A T] in
/-- `θ` has degree one, so the grade involution negates it. -/
@[simp]
theorem involute_theta : involute θ = -θ := by
  rw [involute_of_mem_exteriorPower (theta_mem_exteriorPower_one k f T)]
  simp

variable {k f T} in
/-- The grade involution preserves logarithmic forms. This is why the differentials of logarithmic
forms are an ideal of the closed logarithmic forms: `x ∧ dy = d (σ x ∧ y)` for closed `x`. -/
theorem involute_mem_logForms {x : Forms k T} (hx : x ∈ logForms k f T) :
    involute x ∈ logForms k f T := by
  obtain ⟨ω, η, rfl⟩ := hx
  refine ⟨involute ω, -involute η, ?_⟩
  rw [map_add, map_mul, involute_theta, Forms.map_involute, map_neg, Forms.map_involute, mul_neg,
    neg_mul]

/-! ### Cycles and boundaries -/

/-- The closed logarithmic forms, as a `k`-subalgebra of forms.

Blueprint: the cohomology of `L` in `thm:dr-comparison`. -/
def logCycles : Subalgebra k (Forms k T) :=
  (logForms k f T).restrictScalars k ⊓ cycles k T

variable {k f T} in
theorem mem_logCycles {x : Forms k T} :
    x ∈ logCycles k f T ↔ x ∈ logForms k f T ∧ d k x = 0 :=
  Iff.rfl

/-- The differentials of logarithmic forms, as a two-sided ideal of the closed logarithmic forms.
Note that the primitive is required to be logarithmic: this is what makes
`LogCohomology.toCohomology` a statement, and not a tautology.

Blueprint: the cohomology of `L` in `thm:dr-comparison`. -/
def logBoundaries : TwoSidedIdeal (logCycles k f T) :=
  .mk' {z | ∃ y ∈ logForms k f T, d k y = (z : Forms k T)}
    ⟨0, zero_mem _, by simp⟩
    (by
      rintro _ _ ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
      exact ⟨x + y, add_mem hx hy, by simp [hx', hy']⟩)
    (by
      rintro _ ⟨x, hx, hx'⟩
      exact ⟨-x, neg_mem hx, by simp [hx']⟩)
    (by
      rintro x _ ⟨y, hy, hy'⟩
      refine ⟨involute (x : Forms k T) * y, mul_mem (involute_mem_logForms x.2.1) hy, ?_⟩
      rw [Subalgebra.coe_mul, ← hy', mul_d_of_d_eq_zero k x.2.2])
    (by
      rintro _ x ⟨y, hy, hy'⟩
      refine ⟨y * x, mul_mem hy x.2.1, ?_⟩
      rw [d_mul, x.2.2, mul_zero, add_zero, hy', Subalgebra.coe_mul])

variable {k f T} in
@[simp]
theorem mem_logBoundaries {z : logCycles k f T} :
    z ∈ logBoundaries k f T ↔ ∃ y ∈ logForms k f T, d k y = (z : Forms k T) :=
  TwoSidedIdeal.mem_mk' ..

/-! ### The logarithmic differential -/

variable {k f T} in
/-- A logarithmic form is closed exactly when it is closed as a form. -/
theorem logD_eq_zero_iff {x : logForms k f T} : logD k f T x = 0 ↔ d k (x : Forms k T) = 0 :=
  Subtype.ext_iff

variable {k f T} in
/-- A product of closed logarithmic forms is closed. -/
theorem logD_mul_eq_zero {x y : logForms k f T} (hx : logD k f T x = 0) (hy : logD k f T y = 0) :
    logD k f T (x * y) = 0 := by
  rw [logD_eq_zero_iff] at *
  rw [Subalgebra.coe_mul, d_mul, hx, hy, zero_mul, mul_zero, add_zero]

/-! ### The cohomology algebra -/

/-- The total cohomology `H^•(L)` of the logarithmic forms: closed logarithmic forms, modulo the
differentials of logarithmic forms. It is a `k`-algebra with the product induced by the wedge
product, and the unit is the class of `1`. It is the direct sum of its degree pieces,
`LogCohomology.degree k f T`.

Blueprint: the cohomology of `L` in `thm:dr-comparison`. -/
def LogCohomology : Type _ :=
  RelationQuotient (logBoundaries k f T : Set (logCycles k f T))

namespace LogCohomology

-- Keep the transported action visible to instance synthesis, including the canonical
-- natural and integer actions inherited by the ring structure. See `RelationQuotient`.
instance instSMul {R : Type*} [CommSemiring R] [Algebra R (logCycles k f T)] :
    SMul R (LogCohomology k f T) :=
  inferInstanceAs (SMul R (RelationQuotient (logBoundaries k f T : Set (logCycles k f T))))

instance : Ring (LogCohomology k f T) :=
  inferInstanceAs (Ring (RelationQuotient (logBoundaries k f T : Set (logCycles k f T))))

instance instAlgebra {R : Type*} [CommSemiring R] [Algebra R (logCycles k f T)] :
    Algebra R (LogCohomology k f T) :=
  inferInstanceAs (Algebra R (RelationQuotient (logBoundaries k f T : Set (logCycles k f T))))

instance {R R' : Type*} [CommSemiring R] [CommSemiring R'] [Algebra R (logCycles k f T)]
    [Algebra R' (logCycles k f T)] [SMul R R'] [IsScalarTower R R' (logCycles k f T)] :
    IsScalarTower R R' (LogCohomology k f T) :=
  inferInstanceAs
    (IsScalarTower R R' (RelationQuotient (logBoundaries k f T : Set (logCycles k f T))))

instance {R R' : Type*} [CommSemiring R] [CommSemiring R'] [Algebra R (logCycles k f T)]
    [Algebra R' (logCycles k f T)] [SMulCommClass R R' (logCycles k f T)] :
    SMulCommClass R R' (LogCohomology k f T) :=
  inferInstanceAs
    (SMulCommClass R R' (RelationQuotient (logBoundaries k f T : Set (logCycles k f T))))

-- Verify that there is no diamond, as for `RelationQuotient`.
example : (Semiring.toNatAlgebra : Algebra ℕ (LogCohomology k f T)) = instAlgebra k f T := rfl
example : (Ring.toIntAlgebra _ : Algebra ℤ (LogCohomology k f T)) = instAlgebra k f T := rfl

/-- The quotient map from the closed logarithmic forms, as an algebra map. `simp` rewrites
`mkₐ k f T z` to `mk`. -/
def mkₐ : logCycles k f T →ₐ[k] LogCohomology k f T :=
  RelationQuotient.mkₐ k _

variable {k f T}

/-- The class of a closed logarithmic form.

Blueprint: the cohomology of `L` in `thm:dr-comparison`. -/
def mk (x : logForms k f T) (hx : logD k f T x = 0) : LogCohomology k f T :=
  mkₐ k f T ⟨x, x.2, logD_eq_zero_iff.1 hx⟩

@[simp]
theorem mkₐ_apply (z : logCycles k f T) :
    mkₐ k f T z = mk ⟨z, z.2.1⟩ (logD_eq_zero_iff.2 (mem_logCycles.1 z.2).2) :=
  rfl

/-- The class depends on the form and on nothing else. This is for changing a form to an equal one
inside a class. -/
theorem mk_congr {x y : logForms k f T} (h : x = y) (hx : logD k f T x = 0) :
    mk x hx = mk y (h ▸ hx) := by
  subst h
  rfl

theorem mkₐ_surjective : Function.Surjective (mkₐ k f T) :=
  RelationQuotient.mkₐ_surjective

/-- Every class is the class of a closed logarithmic form. -/
theorem exists_mk_eq (c : LogCohomology k f T) :
    ∃ (x : logForms k f T) (hx : logD k f T x = 0), mk x hx = c := by
  obtain ⟨z, rfl⟩ := mkₐ_surjective c
  exact ⟨⟨z, z.2.1⟩, logD_eq_zero_iff.2 (mem_logCycles.1 z.2).2, rfl⟩

/-- Induction over classes: every class is the class of a closed logarithmic form. See
`LogCohomology.induction_degree` for homogeneous forms. -/
@[elab_as_elim, induction_eliminator]
protected theorem induction {motive : LogCohomology k f T → Prop}
    (mk : ∀ (x : logForms k f T) (hx : logD k f T x = 0), motive (mk x hx))
    (c : LogCohomology k f T) : motive c := by
  obtain ⟨x, hx, rfl⟩ := exists_mk_eq c
  exact mk x hx

/-! ### When classes agree -/

/-- A closed logarithmic form has zero class exactly when it is the differential of a logarithmic
form. -/
theorem mk_eq_zero_iff {x : logForms k f T} {hx : logD k f T x = 0} :
    mk x hx = 0 ↔ ∃ y, logD k f T y = x := by
  have h : mk x hx = 0 ↔ (⟨x, x.2, logD_eq_zero_iff.1 hx⟩ : logCycles k f T) ∈
      relationSubmodule k (logBoundaries k f T : Set (logCycles k f T)) :=
    RelationQuotient.mk_eq_zero_iff k
  rw [h, mem_relationSubmodule_coe_twoSidedIdeal, mem_logBoundaries]
  constructor
  · rintro ⟨y, hy, hy'⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hy'⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩

/-- Two closed logarithmic forms have the same class exactly when they differ by the differential of
a logarithmic form. -/
theorem mk_eq_mk_iff {x x' : logForms k f T} {hx : logD k f T x = 0} {hx' : logD k f T x' = 0} :
    mk x hx = mk x' hx' ↔ ∃ y, logD k f T y = x - x' := by
  have h : mk x hx = mk x' hx' ↔
      ((⟨x, x.2, logD_eq_zero_iff.1 hx⟩ : logCycles k f T) - ⟨x', x'.2, logD_eq_zero_iff.1 hx'⟩) ∈
        relationSubmodule k (logBoundaries k f T : Set (logCycles k f T)) :=
    RelationQuotient.mk_eq_mk_iff k
  rw [h, mem_relationSubmodule_coe_twoSidedIdeal, mem_logBoundaries]
  constructor
  · rintro ⟨y, hy, hy'⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hy'⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, y.2, congrArg Subtype.val hy⟩

/-- The differential of a logarithmic form has zero class. -/
@[simp]
theorem mk_logD (y : logForms k f T) (h : logD k f T (logD k f T y) = 0) :
    mk (logD k f T y) h = 0 :=
  mk_eq_zero_iff.2 ⟨y, rfl⟩

/-- Adding the differential of a logarithmic form does not change the class. -/
@[simp]
theorem mk_add_logD (x y : logForms k f T) (h : logD k f T (x + logD k f T y) = 0) :
    mk (x + logD k f T y) h = mk x (by simpa using h) :=
  mk_eq_mk_iff.2 ⟨y, by simp⟩

/-! ### The operations on classes -/

@[simp]
theorem mk_zero (h : logD k f T 0 = 0) : mk 0 h = 0 :=
  map_zero (mkₐ k f T)

@[simp]
theorem mk_one (h : logD k f T 1 = 0) : mk 1 h = 1 :=
  map_one (mkₐ k f T)

@[simp]
theorem mk_add (x x' : logForms k f T) (hx : logD k f T x = 0) (hx' : logD k f T x' = 0) :
    mk x hx + mk x' hx' = mk (x + x') (by simp [hx, hx']) :=
  (map_add (mkₐ k f T) ⟨x, x.2, logD_eq_zero_iff.1 hx⟩ ⟨x', x'.2, logD_eq_zero_iff.1 hx'⟩).symm

@[simp]
theorem mk_neg (x : logForms k f T) (hx : logD k f T x = 0) :
    -mk x hx = mk (-x) (by simp [hx]) :=
  (map_neg (mkₐ k f T) ⟨x, x.2, logD_eq_zero_iff.1 hx⟩).symm

@[simp]
theorem mk_sub (x x' : logForms k f T) (hx : logD k f T x = 0) (hx' : logD k f T x' = 0) :
    mk x hx - mk x' hx' = mk (x - x') (by simp [hx, hx']) :=
  (map_sub (mkₐ k f T) ⟨x, x.2, logD_eq_zero_iff.1 hx⟩ ⟨x', x'.2, logD_eq_zero_iff.1 hx'⟩).symm

/-- The product of classes is the class of the wedge product. -/
@[simp]
theorem mk_mul (x x' : logForms k f T) (hx : logD k f T x = 0) (hx' : logD k f T x' = 0) :
    mk x hx * mk x' hx' = mk (x * x') (logD_mul_eq_zero hx hx') :=
  (map_mul (mkₐ k f T) ⟨x, x.2, logD_eq_zero_iff.1 hx⟩ ⟨x', x'.2, logD_eq_zero_iff.1 hx'⟩).symm

@[simp]
theorem mk_smul (c : k) (x : logForms k f T) (hx : logD k f T x = 0) :
    c • mk x hx = mk (c • x) (by simp [hx]) :=
  (map_smul (mkₐ k f T) c (⟨x, x.2, logD_eq_zero_iff.1 hx⟩ : logCycles k f T)).symm

/-- Cohomology of the zero ring is zero. -/
instance [Subsingleton T] : Subsingleton (LogCohomology k f T) :=
  ⟨fun c c' => by
    induction c with
    | mk x hx =>
      induction c' with
      | mk y hy =>
        have : Subsingleton (logForms k f T) := ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩
        exact mk_congr (Subsingleton.elim x y) hx⟩

/-! ### Maps out of cohomology -/

section Lift

variable {R : Type*} [Semiring R] [Algebra k R] {M : Type*} [AddCommMonoid M] [Module k M]

/-- An algebra map on closed logarithmic forms that kills the differentials of logarithmic forms
descends to the cohomology of `L`. -/
def lift (g : logCycles k f T →ₐ[k] R)
    (hg : ∀ y : logForms k f T, g ⟨logD k f T y, d_mem_logForms y.2, d_d k _⟩ = 0) :
    LogCohomology k f T →ₐ[k] R :=
  RelationQuotient.liftAlgHom g fun z hz => by
    obtain ⟨y, hy, hy'⟩ := mem_logBoundaries.1 hz
    rw [show z = ⟨logD k f T ⟨y, hy⟩, d_mem_logForms hy, d_d k _⟩ from Subtype.ext hy'.symm, hg]

@[simp]
theorem lift_mk (g : logCycles k f T →ₐ[k] R)
    (hg : ∀ y : logForms k f T, g ⟨logD k f T y, d_mem_logForms y.2, d_d k _⟩ = 0)
    (x : logForms k f T) (hx : logD k f T x = 0) :
    lift g hg (mk x hx) = g ⟨x, x.2, logD_eq_zero_iff.1 hx⟩ :=
  rfl

/-- A `k`-linear map on closed logarithmic forms that kills the differentials of logarithmic forms
descends to the cohomology of `L`. It need not be multiplicative, and there is no degree in the
statement. This is the form to use for a map with a sign or a shift, such as a residue. -/
def liftLinear (g : logCycles k f T →ₗ[k] M)
    (hg : ∀ y : logForms k f T, g ⟨logD k f T y, d_mem_logForms y.2, d_d k _⟩ = 0) :
    LogCohomology k f T →ₗ[k] M :=
  RelationQuotient.liftLinear g fun z hz => by
    obtain ⟨y, hy, hy'⟩ := mem_logBoundaries.1 ((mem_relationSubmodule_coe_twoSidedIdeal _).1 hz)
    rw [LinearMap.mem_ker,
      show z = ⟨logD k f T ⟨y, hy⟩, d_mem_logForms hy, d_d k _⟩ from Subtype.ext hy'.symm, hg]

@[simp]
theorem liftLinear_mk (g : logCycles k f T →ₗ[k] M)
    (hg : ∀ y : logForms k f T, g ⟨logD k f T y, d_mem_logForms y.2, d_d k _⟩ = 0)
    (x : logForms k f T) (hx : logD k f T x = 0) :
    liftLinear g hg (mk x hx) = g ⟨x, x.2, logD_eq_zero_iff.1 hx⟩ :=
  RelationQuotient.liftLinear_mk g _ _

/-- Algebra maps out of cohomology agree if they agree on the classes of closed logarithmic
forms. -/
@[ext]
theorem algHom_ext {g g' : LogCohomology k f T →ₐ[k] R}
    (h : ∀ (x : logForms k f T) (hx : logD k f T x = 0), g (mk x hx) = g' (mk x hx)) : g = g' :=
  AlgHom.ext fun c => by
    induction c with
    | mk x hx => exact h x hx

/-- Linear maps out of cohomology agree if they agree on the classes of closed logarithmic forms. -/
@[ext]
theorem linearMap_ext {g g' : LogCohomology k f T →ₗ[k] M}
    (h : ∀ (x : logForms k f T) (hx : logD k f T x = 0), g (mk x hx) = g' (mk x hx)) : g = g' :=
  LinearMap.ext fun c => by
    induction c with
    | mk x hx => exact h x hx

end Lift

/-! ### The maps `H^•(A) → H^•(L) → H^•(T)` -/

variable (k f T) in
/-- The map `H^•(L) → H^•(T)` of algebras, induced by the inclusion of logarithmic forms in forms on
`T`. For a smooth pair over a ring in which positive integers are units it is bijective, and that is
`thm:dr-comparison`.

Blueprint: `thm:dr-comparison`. -/
def toCohomology : LogCohomology k f T →ₐ[k] Cohomology k T :=
  lift ((Cohomology.mkₐ k T).comp (Subalgebra.inclusion inf_le_right)) fun _ =>
    Cohomology.mk_d _ _

/-- The map `H^•(L) → H^•(T)` on a class.

Blueprint: `thm:dr-comparison`. -/
@[simp]
theorem toCohomology_mk (x : logForms k f T) (hx : logD k f T x = 0) :
    toCohomology k f T (mk x hx) = Cohomology.mk (x : Forms k T) (logD_eq_zero_iff.1 hx) :=
  rfl

variable (k f T) in
/-- The inclusion of closed regular forms in closed logarithmic forms. -/
def cyclesToLogCycles : cycles k A →ₐ[k] logCycles k f T :=
  (((logForms k f T).val.restrictScalars k).comp
      (((ofRegular k f T).restrictScalars k).comp (cycles k A).val)).codRestrict (logCycles k f T)
    fun z => ⟨(ofRegular k f T z).2, by
      change d k (ofRegular k f T z : Forms k T) = 0
      rw [coe_ofRegular]
      exact Cohomology.d_map_eq_zero _ z.2⟩

/-- `ofRegular` preserves closed forms. -/
theorem logD_ofRegular_eq_zero {ω : Forms k A} (hω : d k ω = 0) :
    logD k f T (ofRegular k f T ω) = 0 := by
  rw [logD_ofRegular, hω, map_zero]

/-- The class of a closed regular form, viewed as a closed logarithmic form. -/
theorem mkₐ_cyclesToLogCycles (z : cycles k A) :
    mkₐ k f T (cyclesToLogCycles k f T z) = mk (ofRegular k f T z) (logD_ofRegular_eq_zero z.2) :=
  rfl

variable (k f T) in
/-- The map `H^•(A) → H^•(L)` of algebras, induced by the map from regular forms to logarithmic
forms. Its composite with `toCohomology` is the functoriality of cohomology along `A → T`, by
`toCohomology_ofCohomology`.

Blueprint: the map `j_*` of `lem:dr-exactness`, before `thm:dr-comparison`. -/
def ofCohomology : Cohomology k A →ₐ[k] LogCohomology k f T :=
  Cohomology.lift ((mkₐ k f T).comp (cyclesToLogCycles k f T)) fun y => by
    rw [AlgHom.comp_apply, mkₐ_cyclesToLogCycles]
    exact mk_eq_zero_iff.2 ⟨ofRegular k f T y, logD_ofRegular k f T y⟩

/-- The map `H^•(A) → H^•(L)` on a class.

Blueprint: the map `j_*` of `lem:dr-exactness`, before `thm:dr-comparison`. -/
@[simp]
theorem ofCohomology_mk (ω : Forms k A) (hω : d k ω = 0) :
    ofCohomology k f T (Cohomology.mk ω hω) =
      mk (ofRegular k f T ω) (logD_ofRegular_eq_zero hω) :=
  rfl

/-- The composite `H^•(A) → H^•(L) → H^•(T)` is the functoriality of cohomology along `A → T`.

Blueprint: the map `j_*` of `lem:dr-exactness`. -/
@[simp]
theorem toCohomology_ofCohomology (c : Cohomology k A) :
    toCohomology k f T (ofCohomology k f T c) =
      Cohomology.map (IsScalarTower.toAlgHom k A T) c := by
  induction c with
  | mk ω hω =>
    rw [ofCohomology_mk, toCohomology_mk, Cohomology.map_mk]
    exact Cohomology.mk_eq_mk_iff.2 ⟨0, by rw [coe_ofRegular, sub_self, map_zero]⟩

variable (k f T) in
/-- The composite `H^•(A) → H^•(L) → H^•(T)` is the functoriality of cohomology along `A → T`, as
an equation of algebra maps. -/
theorem toCohomology_comp_ofCohomology :
    (toCohomology k f T).comp (ofCohomology k f T) =
      Cohomology.map (IsScalarTower.toAlgHom k A T) :=
  AlgHom.ext toCohomology_ofCohomology

/-- The bijectivity of `H^•(L) → H^•(T)`, in terms of forms: every closed form on `T` differs from a
closed logarithmic form by an exact form, and a logarithmic form that is exact on `T` is the
differential of a logarithmic form. These are the two halves of `thm:dr-comparison`. -/
theorem bijective_toCohomology_of_forall
    (hs : ∀ x : Forms k T, d k x = 0 → ∃ y : logForms k f T, logD k f T y = 0 ∧
      ∃ z, d k z = x - (y : Forms k T))
    (hi : ∀ x : logForms k f T, logD k f T x = 0 → (∃ z, d k z = (x : Forms k T)) →
      ∃ y, logD k f T y = x) :
    Function.Bijective (toCohomology k f T) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, fun c => ?_⟩
  · induction c with
    | mk x hx =>
      rw [toCohomology_mk, Cohomology.mk_eq_zero_iff] at hc
      exact mk_eq_zero_iff.2 (hi x hx hc)
  · induction c with
    | mk x hx =>
      obtain ⟨y, hy, z, hz⟩ := hs x hx
      exact ⟨mk y hy, Cohomology.mk_eq_mk_iff.2 ⟨-z, by rw [map_neg, hz, neg_sub]⟩⟩

/-! ### The degrees -/

end LogCohomology

/-- A closed logarithmic form has closed logarithmic components, so the closed logarithmic forms
are a homogeneous subalgebra. -/
theorem logCycles_isHomogeneous : SetLike.IsHomogeneous (formsDegree k T) (logCycles k f T) := by
  intro n x hx
  exact ⟨logPower_le_logForms k f T n (coe_exteriorProj_mem_logPower hx.1 n),
    d_decompose_eq_zero hx.2 n⟩

/-- The closed logarithmic forms of degree `n`, as a `k`-submodule of the closed logarithmic
forms. -/
abbrev logCyclesDegree (n : ℕ) : Submodule k (logCycles k f T) :=
  (formsDegree k T n).comap (logCycles k f T).val.toLinearMap

instance : GradedAlgebra (logCyclesDegree k f T) :=
  homogeneousSubalgebraGradedAlgebra (formsDegree k T) (logCycles k f T)
    (logCycles_isHomogeneous k f T)

variable {k f T} in
/-- The components of a closed logarithmic form, as a closed logarithmic form, are its components as
a form. -/
theorem coe_decompose_logCyclesDegree (z : logCycles k f T) (n : ℕ) :
    ((decompose (logCyclesDegree k f T) z n : logCycles k f T) : Forms k T) =
      decompose (fun n : ℕ => ⋀[T]^n Ω[T⁄k]) (z : Forms k T) n :=
  coe_decompose_homogeneousSubalgebra (formsDegree k T) (logCycles k f T) z n

/-- The boundaries of the logarithmic complex are homogeneous, since `d` is and logarithmic forms
are. -/
theorem relationSubmodule_logBoundaries_isHomogeneous :
    (relationSubmodule k (logBoundaries k f T : Set (logCycles k f T))).IsHomogeneous
      (logCyclesDegree k f T) := by
  rintro n z hz
  rw [mem_relationSubmodule_coe_twoSidedIdeal, mem_logBoundaries] at hz ⊢
  obtain ⟨y, hy, hy'⟩ := hz
  rw [coe_decompose_logCyclesDegree, ← hy']
  cases n with
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | succ n =>
    exact ⟨_, logPower_le_logForms k f T n (coe_exteriorProj_mem_logPower hy n),
      (decompose_d_succ k y n).symm⟩

namespace LogCohomology

/-- The piece `H^n(L)` of the total cohomology, which is the image of the closed logarithmic forms
of degree `n`. The negative degrees are in `LogCohomology.grading`.

Blueprint: the cohomology of `L` in `thm:dr-comparison`, in each degree. -/
def degree (n : ℕ) : Submodule k (LogCohomology k f T) :=
  RelationQuotient.grading (logBoundaries k f T : Set (logCycles k f T)) (logCyclesDegree k f T) n

/-- The total cohomology of `L` is the internal direct sum of its degree pieces, compatibly with
products.

Blueprint: the cohomology of `L` in `thm:dr-comparison`, in each degree. -/
instance gradedAlgebraDegree : GradedAlgebra (degree k f T) :=
  RelationQuotient.gradedAlgebraOfIsHomogeneous (logCyclesDegree k f T)
    (relationSubmodule_logBoundaries_isHomogeneous k f T)

variable {k f T}

/-- The class of a closed logarithmic form of degree `n` has degree `n`. -/
theorem mk_mem_degree {n : ℕ} {x : logForms k f T} (hxn : (x : Forms k T) ∈ logPower k f T n)
    (hx : logD k f T x = 0) : mk x hx ∈ degree k f T n :=
  RelationQuotient.mk_mem_grading (𝒜 := logCyclesDegree k f T)
    (x := ⟨x, x.2, logD_eq_zero_iff.1 hx⟩) (mem_logPower_iff.1 hxn).2

/-- The elements of `H^n(L)` are the classes of the closed logarithmic forms of degree `n`. -/
theorem mem_degree_iff {n : ℕ} {c : LogCohomology k f T} :
    c ∈ degree k f T n ↔
      ∃ (x : logForms k f T) (hx : logD k f T x = 0), (x : Forms k T) ∈ logPower k f T n ∧
        mk x hx = c := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, z.2.1⟩, logD_eq_zero_iff.2 (mem_logCycles.1 z.2).2,
      mem_logPower_iff.2 ⟨z.2.1, hz⟩, rfl⟩
  · rintro ⟨x, hx, hxn, rfl⟩
    exact mk_mem_degree hxn hx

/-- A component of a logarithmic form, as a logarithmic form. -/
theorem decompose_mem_logForms (x : logForms k f T) (n : ℕ) :
    (decompose (fun n : ℕ => ⋀[T]^n Ω[T⁄k]) (x : Forms k T) n : Forms k T) ∈ logForms k f T :=
  logPower_le_logForms k f T n (coe_exteriorProj_mem_logPower x.2 n)

/-- Homogeneous components in the cohomology of `L` are computed on representatives. -/
@[simp]
theorem decompose_mk (x : logForms k f T) (hx : logD k f T x = 0) (n : ℕ) :
    (decompose (degree k f T) (mk x hx) n : LogCohomology k f T) =
      mk ⟨decompose (fun n : ℕ => ⋀[T]^n Ω[T⁄k]) (x : Forms k T) n, decompose_mem_logForms x n⟩
        (logD_eq_zero_iff.2 (d_decompose_eq_zero (logD_eq_zero_iff.1 hx) n)) := by
  let : Decomposition (RelationQuotient.grading (logBoundaries k f T : Set (logCycles k f T))
      (logCyclesDegree k f T)) := inferInstanceAs (Decomposition (degree k f T))
  refine (RelationQuotient.decompose_mk (ℛ := (logBoundaries k f T : Set (logCycles k f T)))
    (𝒜 := logCyclesDegree k f T) (⟨x, x.2, logD_eq_zero_iff.1 hx⟩ : logCycles k f T) n).trans ?_
  exact congrArg (mkₐ k f T) (Subtype.ext (coe_decompose_logCyclesDegree _ n))

/-- Induction over classes of homogeneous closed logarithmic forms. -/
@[elab_as_elim]
theorem induction_degree {motive : LogCohomology k f T → Prop}
    (mk : ∀ (n : ℕ) (x : logForms k f T), (x : Forms k T) ∈ logPower k f T n →
      ∀ hx : logD k f T x = 0, motive (mk x hx))
    (add : ∀ c c', motive c → motive c' → motive (c + c')) (c : LogCohomology k f T) :
    motive c := by
  induction c using Decomposition.inductionOn (degree k f T) with
  | zero =>
    have h := mk 0 0 (zero_mem _) (map_zero _)
    rwa [mk_zero] at h
  | @homogeneous n m =>
    obtain ⟨x, hx, hxn, hm⟩ := mem_degree_iff.1 m.2
    rw [← hm]
    exact mk n x hxn hx
  | add c c' hc hc' => exact add c c' hc hc'

/-- A closed logarithmic form of degree `n + 1` has zero class exactly when it is the differential
of a logarithmic form of degree `n`. -/
theorem mk_eq_zero_iff_of_mem_logPower_succ {n : ℕ} {x : logForms k f T}
    (hxn : (x : Forms k T) ∈ logPower k f T (n + 1)) {hx : logD k f T x = 0} :
    mk x hx = 0 ↔ ∃ y : logForms k f T, (y : Forms k T) ∈ logPower k f T n ∧ logD k f T y = x := by
  rw [mk_eq_zero_iff]
  refine ⟨?_, fun ⟨y, _, hy⟩ => ⟨y, hy⟩⟩
  rintro ⟨y, rfl⟩
  refine ⟨⟨decompose (fun n : ℕ => ⋀[T]^n Ω[T⁄k]) (y : Forms k T) n, decompose_mem_logForms y n⟩,
    coe_exteriorProj_mem_logPower y.2 n, Subtype.ext ?_⟩
  rw [coe_logD, ← decompose_d_succ, ← coe_logD,
    decompose_of_mem_same (fun n : ℕ => ⋀[T]^n Ω[T⁄k]) (mem_logPower_iff.1 hxn).2]

/-- A closed logarithmic form of degree zero has zero class exactly when it is zero: degree `-1` is
zero. -/
theorem mk_eq_zero_iff_of_mem_logPower_zero {x : logForms k f T}
    (hxn : (x : Forms k T) ∈ logPower k f T 0) {hx : logD k f T x = 0} : mk x hx = 0 ↔ x = 0 := by
  rw [mk_eq_zero_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact Subtype.ext
      (eq_zero_of_mem_exteriorPower_zero_of_exists (mem_logPower_iff.1 hxn).2 ⟨y, rfl⟩)
  · rintro rfl
    exact ⟨0, map_zero _⟩

/-! ### The grading by the integers -/

variable (k f T) in
/-- The grading of the total cohomology of `L` by `p : ℤ`. It is `degree k f T n` at `p = n`, by
`grading_natCast`, and zero for `p < 0`, by `grading_of_neg`. -/
def grading (p : ℤ) : Submodule k (LogCohomology k f T) :=
  coarsenGrading (degree k f T) (Nat.castAddMonoidHom ℤ) p

instance gradedAlgebraGrading : GradedAlgebra (grading k f T) :=
  inferInstanceAs (GradedAlgebra (coarsenGrading (degree k f T) (Nat.castAddMonoidHom ℤ)))

/-- In a natural degree, the grading is `degree`. -/
@[simp]
theorem grading_natCast (n : ℕ) : grading k f T (n : ℤ) = degree k f T n :=
  coarsenGrading_apply (degree k f T) (f := Nat.castAddMonoidHom ℤ) Nat.cast_injective n

/-- The grading is zero in negative degrees. -/
theorem grading_of_neg {p : ℤ} (hp : p < 0) : grading k f T p = ⊥ := by
  refine coarsenGrading_eq_bot (degree k f T) (f := Nat.castAddMonoidHom ℤ) ?_
  rintro ⟨n, rfl⟩
  exact absurd hp (by simp)

/-- There is nothing in negative degrees. -/
theorem eq_zero_of_mem_grading_of_neg {p : ℤ} (hp : p < 0) {c : LogCohomology k f T}
    (hc : c ∈ grading k f T p) : c = 0 := by
  rwa [grading_of_neg hp, Submodule.mem_bot] at hc

/-- The class of a closed logarithmic form of degree `n` has degree `n`. -/
theorem mk_mem_grading {n : ℕ} {x : logForms k f T} (hxn : (x : Forms k T) ∈ logPower k f T n)
    (hx : logD k f T x = 0) : mk x hx ∈ grading k f T n := by
  rw [grading_natCast]
  exact mk_mem_degree hxn hx

/-! ### The maps preserve degrees -/

/-- `H^•(L) → H^•(T)` preserves degree. -/
theorem toCohomology_mem_degree {n : ℕ} {c : LogCohomology k f T} (hc : c ∈ degree k f T n) :
    toCohomology k f T c ∈ Cohomology.degree k T n := by
  obtain ⟨x, hx, hxn, rfl⟩ := mem_degree_iff.1 hc
  exact Cohomology.mk_mem_degree (mem_logPower_iff.1 hxn).2 _

/-- `H^•(A) → H^•(L)` preserves degree. -/
theorem ofCohomology_mem_degree {n : ℕ} {c : Cohomology k A} (hc : c ∈ Cohomology.degree k A n) :
    ofCohomology k f T c ∈ degree k f T n := by
  obtain ⟨x, hx, hxn, rfl⟩ := Cohomology.mem_degree_iff.1 hc
  rw [ofCohomology_mk]
  refine mk_mem_degree ?_ _
  rw [coe_ofRegular]
  exact map_mem_logPower k f T hxn

variable (k f T) in
/-- `H^•(L) → H^•(T)` preserves the grading by the integers. -/
theorem isHomogeneousOfShift_toCohomology :
    IsHomogeneousOfShift (grading k f T) (Cohomology.grading k T) 0 (toCohomology k f T) :=
  isHomogeneousOfShift_zero_iff.2 fun _ _ hc =>
    map_mem_coarsenGrading (degree k f T) (Nat.castAddMonoidHom ℤ) (Cohomology.degree k T)
      (toCohomology k f T).toLinearMap (fun _ _ hm => toCohomology_mem_degree hm) hc

variable (k f T) in
/-- `H^•(A) → H^•(L)` preserves the grading by the integers. -/
theorem isHomogeneousOfShift_ofCohomology :
    IsHomogeneousOfShift (Cohomology.grading k A) (grading k f T) 0 (ofCohomology k f T) :=
  isHomogeneousOfShift_zero_iff.2 fun _ _ hc =>
    map_mem_coarsenGrading (Cohomology.degree k A) (Nat.castAddMonoidHom ℤ) (degree k f T)
      (ofCohomology k f T).toLinearMap (fun _ _ hm => ofCohomology_mem_degree hm) hc

end LogCohomology

end OrlikSolomon.DeRham
