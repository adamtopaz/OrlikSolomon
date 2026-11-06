/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Cohomology.Basic
public import OrlikSolomon.Grading.Restriction
public import OrlikSolomon.Grading.TensorProduct

/-!
# The degrees of de Rham cohomology

This file decomposes the total cohomology of `DeRham/Cohomology/Basic` by cohomological degree. The
pieces are the images of the closed forms of each degree. A closed form has closed components, and
an exact form has exact components, so the grading of forms descends.

## Main definitions

* `OrlikSolomon.DeRham.Cohomology.degree k A n`: the piece `H^n`, for `n : ℕ`, a `k`-submodule of
  the total cohomology, with its `GradedAlgebra` instance.
* `OrlikSolomon.DeRham.Cohomology.grading k A p`: the same grading, indexed by `p : ℤ`, zero in
  negative degrees, with its `GradedAlgebra` instance.
* `OrlikSolomon.DeRham.Cohomology.degreeEquiv k A n`: the identification of `H^n` with
  `ker d / im d` in degree `n`.

## Main results

* `OrlikSolomon.DeRham.Cohomology.mem_degree_iff`: `H^n` consists of the classes of the closed forms
  of degree `n`.
* `OrlikSolomon.DeRham.Cohomology.decompose_mk`: homogeneous components are computed on
  representatives.
* `OrlikSolomon.DeRham.Cohomology.mk_eq_zero_iff_of_mem_exteriorPower`: a closed form of degree `n`
  that is exact has a primitive of degree `n - 1`, and it is zero if `n = 0`.
* `OrlikSolomon.DeRham.Cohomology.isGradedCommutative_degree` and
  `OrlikSolomon.DeRham.Cohomology.isGradedCommutative_grading`: graded commutativity with sign
  `(-1)^(pq)`.
* `OrlikSolomon.DeRham.Cohomology.isHomogeneousOfShift_map`: the maps preserve degree.
* `OrlikSolomon.DeRham.Cohomology.induction_degree`: induction over classes of homogeneous forms.

## Blueprint

`def:dr-cohomology`. See `OrlikSolomon/DeRham/Cohomology.lean` for the summary.
-/

@[expose] public section

noncomputable section

open DirectSum

namespace OrlikSolomon.DeRham

universe u v v'

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  {A' : Type v'} [CommRing A'] [Algebra k A']

/-! ### The differential and the components of a form -/

section Forms

variable {A}

/-- `d` is homogeneous of shift one. -/
theorem isHomogeneousOfShift_d :
    IsHomogeneousOfShift (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) 1 (d k) :=
  fun _ _ hx => d_mem_exteriorPower k hx

/-- `d` commutes with taking components: the component of `d x` in degree `n + 1` is `d` of the
component of `x` in degree `n`. -/
theorem decompose_d_succ (x : Forms k A) (n : ℕ) :
    (decompose (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) (d k x) (n + 1) : Forms k A) =
      d k (decompose (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) x n : Forms k A) :=
  (isHomogeneousOfShift_d k).decompose_map rfl x

/-- An exact form has no component in degree zero. -/
@[simp]
theorem decompose_d_zero (x : Forms k A) :
    (decompose (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) (d k x) 0 : Forms k A) = 0 := by
  induction x using Decomposition.inductionOn (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) with
  | zero => simp
  | homogeneous m =>
    exact decompose_of_mem_ne (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) (d_mem_exteriorPower k m.2)
      (Nat.succ_ne_zero _)
  | add x y hx hy => simp [decompose_add, hx, hy]

variable {k}

/-- The components of a closed form are closed. -/
theorem d_decompose_eq_zero {x : Forms k A} (hx : d k x = 0) (n : ℕ) :
    d k (decompose (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) x n : Forms k A) = 0 := by
  rw [← decompose_d_succ, hx]
  simp

/-- A form of degree `n + 1` that is exact has a primitive of degree `n`. -/
theorem exists_mem_exteriorPower_d_eq {n : ℕ} {x : Forms k A} (hx : x ∈ ⋀[A]^(n + 1) Ω[A⁄k])
    (h : ∃ y, d k y = x) : ∃ y ∈ ⋀[A]^n Ω[A⁄k], d k y = x :=
  (isHomogeneousOfShift_d k).exists_mem_preimage rfl hx h

/-- A form of degree zero that is exact is zero. -/
theorem eq_zero_of_mem_exteriorPower_zero_of_exists {x : Forms k A} (hx : x ∈ ⋀[A]^0 Ω[A⁄k])
    (h : ∃ y, d k y = x) : x = 0 := by
  obtain ⟨y, rfl⟩ := h
  rw [← decompose_of_mem_same (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) hx, decompose_d_zero]

end Forms

/-! ### The closed forms of each degree -/

/-- The forms of degree `n`, as a `k`-submodule of all forms. This is `⋀[A]^n Ω[A⁄k]` with its
scalars restricted, which is how a `k`-algebra grading sees it. -/
abbrev formsDegree (n : ℕ) : Submodule k (Forms k A) :=
  (⋀[A]^n Ω[A⁄k]).restrictScalars k

instance : GradedAlgebra (formsDegree k A) :=
  inferInstanceAs (GradedAlgebra ((fun n : ℕ => ⋀[A]^n Ω[A⁄k]) · |>.restrictScalars k))

/-- A closed form has closed components, so the closed forms are a homogeneous subalgebra. -/
theorem cycles_isHomogeneous : SetLike.IsHomogeneous (formsDegree k A) (cycles k A) :=
  fun n _ hx => d_decompose_eq_zero (mem_cycles.1 hx) n

/-- The closed forms of degree `n`. These are the blueprint's `ker (d : Ω^n → Ω^(n+1))`, as a
`k`-submodule of the algebra of closed forms. -/
abbrev cyclesDegree (n : ℕ) : Submodule k (cycles k A) :=
  (formsDegree k A n).comap (cycles k A).val.toLinearMap

instance : GradedAlgebra (cyclesDegree k A) :=
  homogeneousSubalgebraGradedAlgebra (formsDegree k A) (cycles k A) (cycles_isHomogeneous k A)

variable {k A} in
/-- The components of a closed form, as a closed form, are its components as a form. -/
theorem coe_decompose_cyclesDegree (z : cycles k A) (n : ℕ) :
    ((decompose (cyclesDegree k A) z n : cycles k A) : Forms k A) =
      decompose (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) (z : Forms k A) n :=
  coe_decompose_homogeneousSubalgebra (formsDegree k A) (cycles k A) z n

/-- The boundaries are homogeneous, since `d` is. -/
theorem relationSubmodule_boundaries_isHomogeneous :
    (relationSubmodule k (boundaries k A : Set (cycles k A))).IsHomogeneous (cyclesDegree k A) := by
  rintro n z hz
  rw [mem_relationSubmodule_coe_twoSidedIdeal, mem_boundaries] at hz ⊢
  obtain ⟨y, hy⟩ := hz
  rw [coe_decompose_cyclesDegree, ← hy]
  cases n with
  | zero => exact ⟨0, by simp⟩
  | succ n => exact ⟨_, (decompose_d_succ k y n).symm⟩

namespace Cohomology

/-! ### The degree pieces -/

/-- The piece `H^n_dR(A/k)` of the total cohomology, which is the image of the closed forms of
degree `n`. By `degreeEquiv` and `homologyIso`, it is `ker d / im d` in degree `n`. The negative
degrees are in `Cohomology.grading`.

Blueprint: `def:dr-cohomology`. -/
def degree (n : ℕ) : Submodule k (Cohomology k A) :=
  RelationQuotient.grading (boundaries k A : Set (cycles k A)) (cyclesDegree k A) n

/-- The total cohomology is the internal direct sum of its degree pieces, compatibly with products.

Blueprint: `def:dr-cohomology`. -/
instance gradedAlgebraDegree : GradedAlgebra (degree k A) :=
  RelationQuotient.gradedAlgebraOfIsHomogeneous (cyclesDegree k A)
    (relationSubmodule_boundaries_isHomogeneous k A)

variable {k A}

/-- The class of a closed form of degree `n` has degree `n`. -/
theorem mk_mem_degree {n : ℕ} {x : Forms k A} (hxn : x ∈ ⋀[A]^n Ω[A⁄k]) (hx : d k x = 0) :
    mk x hx ∈ degree k A n :=
  RelationQuotient.mk_mem_grading (𝒜 := cyclesDegree k A) (x := ⟨x, hx⟩) hxn

/-- The elements of `H^n` are the classes of the closed forms of degree `n`.

Blueprint: `def:dr-cohomology`. -/
theorem mem_degree_iff {n : ℕ} {c : Cohomology k A} :
    c ∈ degree k A n ↔
      ∃ (x : Forms k A) (hx : d k x = 0), x ∈ ⋀[A]^n Ω[A⁄k] ∧ mk x hx = c := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, z.2, hz, rfl⟩
  · rintro ⟨x, hx, hxn, rfl⟩
    exact mk_mem_degree hxn hx

/-- Homogeneous components in cohomology are computed on representatives. -/
@[simp]
theorem decompose_mk (x : Forms k A) (hx : d k x = 0) (n : ℕ) :
    (decompose (degree k A) (mk x hx) n : Cohomology k A) =
      mk (decompose (fun n : ℕ => ⋀[A]^n Ω[A⁄k]) x n : Forms k A) (d_decompose_eq_zero hx n) := by
  let : Decomposition (RelationQuotient.grading (boundaries k A : Set (cycles k A))
      (cyclesDegree k A)) := inferInstanceAs (Decomposition (degree k A))
  refine (RelationQuotient.decompose_mk (ℛ := (boundaries k A : Set (cycles k A)))
    (𝒜 := cyclesDegree k A) (⟨x, hx⟩ : cycles k A) n).trans ?_
  exact congrArg (mkₐ k A) (Subtype.ext (coe_decompose_cyclesDegree ⟨x, hx⟩ n))

/-- Induction over classes of homogeneous closed forms.

Blueprint: `def:dr-cohomology`. -/
@[elab_as_elim]
theorem induction_degree {motive : Cohomology k A → Prop}
    (mk : ∀ (n : ℕ) (x : Forms k A), x ∈ ⋀[A]^n Ω[A⁄k] → ∀ hx : d k x = 0, motive (mk x hx))
    (add : ∀ c c', motive c → motive c' → motive (c + c')) (c : Cohomology k A) : motive c := by
  induction c using Decomposition.inductionOn (degree k A) with
  | zero =>
    have h := mk 0 0 (zero_mem _) (map_zero _)
    rwa [mk_zero] at h
  | @homogeneous n m =>
    obtain ⟨x, hx, hxn, hm⟩ := mem_degree_iff.1 m.2
    rw [← hm]
    exact mk n x hxn hx
  | add c c' hc hc' => exact add c c' hc hc'

/-! ### Degree and exactness -/

/-- A closed form of degree `n + 1` has zero class exactly when it has a primitive of degree `n`. -/
theorem mk_eq_zero_iff_of_mem_exteriorPower_succ {n : ℕ} {x : Forms k A}
    (hxn : x ∈ ⋀[A]^(n + 1) Ω[A⁄k]) {hx : d k x = 0} :
    mk x hx = 0 ↔ ∃ y ∈ ⋀[A]^n Ω[A⁄k], d k y = x := by
  rw [mk_eq_zero_iff]
  exact ⟨exists_mem_exteriorPower_d_eq hxn, fun ⟨y, _, hy⟩ => ⟨y, hy⟩⟩

/-- A closed form of degree zero has zero class exactly when it is zero: degree `-1` is zero. -/
theorem mk_eq_zero_iff_of_mem_exteriorPower_zero {x : Forms k A}
    (hxn : x ∈ ⋀[A]^0 Ω[A⁄k]) {hx : d k x = 0} : mk x hx = 0 ↔ x = 0 := by
  rw [mk_eq_zero_iff]
  refine ⟨eq_zero_of_mem_exteriorPower_zero_of_exists hxn, ?_⟩
  rintro rfl
  exact ⟨0, map_zero _⟩

/-! ### Graded commutativity -/

/-- A sign can be moved out of a class. -/
theorem mk_units_smul (u : ℤˣ) (x : Forms k A) (hx : d k x = 0) (h : d k (u • x) = 0) :
    mk (u • x) h = u • mk x hx := by
  obtain rfl | rfl := Int.units_eq_one_or u
  · simp
  · simp only [Units.neg_smul, one_smul, mk_neg]

variable (k A) in
/-- Cohomology is graded commutative with the sign `(-1)^(pq)`, by that of forms. This assumes
nothing about `2`.

Blueprint: `def:dr-cohomology`. -/
theorem isGradedCommutative_degree :
    IsGradedCommutative (degree k A) (fun n : ℕ => (n : ℤ)) := by
  intro p q c c' hc hc'
  obtain ⟨x, hx, hxp, rfl⟩ := mem_degree_iff.1 hc
  obtain ⟨y, hy, hyq, rfl⟩ := mem_degree_iff.1 hc'
  have h := mul_comm_of_mem_exteriorPower hxp hyq
  rw [mk_mul, mk_mul, ← mk_units_smul _ _ _ (h ▸ mem_cycles.1 (mul_mem hx hy))]
  exact mk_congr h _

/-! ### Functoriality -/

/-- The induced maps preserve degrees.

Blueprint: `def:dr-cohomology`. -/
theorem map_mem_degree (φ : A →ₐ[k] A') {n : ℕ} {c : Cohomology k A} (hc : c ∈ degree k A n) :
    map φ c ∈ degree k A' n := by
  obtain ⟨x, hx, hxn, rfl⟩ := mem_degree_iff.1 hc
  exact mk_mem_degree (Forms.map_mem_exteriorPower φ hxn) _

/-- The induced maps preserve degrees, as a homogeneous map of shift zero. -/
theorem isHomogeneousOfShift_map_degree (φ : A →ₐ[k] A') :
    IsHomogeneousOfShift (degree k A) (degree k A') 0 (map φ) :=
  isHomogeneousOfShift_zero_iff.2 fun _ _ hc => map_mem_degree φ hc

/-! ### The grading by the integers -/

variable (k A) in
/-- The grading of the total cohomology by `p : ℤ`. It is `degree k A n` at `p = n`, by
`grading_natCast`, and zero for `p < 0`, by `grading_of_neg`. Its pieces are the cohomological
degrees of the bigrading of the de Rham instance.

Blueprint: `def:dr-cohomology`, for `def:dr-twisted-functor`. -/
def grading (p : ℤ) : Submodule k (Cohomology k A) :=
  coarsenGrading (degree k A) (Nat.castAddMonoidHom ℤ) p

instance gradedAlgebraGrading : GradedAlgebra (grading k A) :=
  inferInstanceAs (GradedAlgebra (coarsenGrading (degree k A) (Nat.castAddMonoidHom ℤ)))

/-- In a natural degree, the grading is `degree`. -/
@[simp]
theorem grading_natCast (n : ℕ) : grading k A (n : ℤ) = degree k A n :=
  coarsenGrading_apply (degree k A) (f := Nat.castAddMonoidHom ℤ) Nat.cast_injective n

/-- The grading is zero in negative degrees. -/
theorem grading_of_neg {p : ℤ} (hp : p < 0) : grading k A p = ⊥ := by
  refine coarsenGrading_eq_bot (degree k A) (f := Nat.castAddMonoidHom ℤ) ?_
  rintro ⟨n, rfl⟩
  exact absurd hp (by simp)

/-- There is nothing in negative degrees. -/
theorem eq_zero_of_mem_grading_of_neg {p : ℤ} (hp : p < 0) {c : Cohomology k A}
    (hc : c ∈ grading k A p) : c = 0 := by
  rwa [grading_of_neg hp, Submodule.mem_bot] at hc

/-- The class of a closed form of degree `n` has degree `n`. -/
theorem mk_mem_grading {n : ℕ} {x : Forms k A} (hxn : x ∈ ⋀[A]^n Ω[A⁄k]) (hx : d k x = 0) :
    mk x hx ∈ grading k A n := by
  rw [grading_natCast]
  exact mk_mem_degree hxn hx

variable (k A) in
/-- Cohomology is graded commutative for the grading by the integers. A bigrading whose first index
is this degree has the sign `IsGradedCommutative 𝒜 Prod.fst`.

Blueprint: `def:dr-cohomology`, and the sign in `lem:dr-ordinary-basic`. -/
theorem isGradedCommutative_grading : IsGradedCommutative (grading k A) id := by
  intro p q c c' hc hc'
  obtain hp | hp := lt_or_ge p 0
  · rw [eq_zero_of_mem_grading_of_neg hp hc, zero_mul, mul_zero, smul_zero]
  obtain hq | hq := lt_or_ge q 0
  · rw [eq_zero_of_mem_grading_of_neg hq hc', zero_mul, mul_zero, smul_zero]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  rw [grading_natCast] at hc hc'
  exact isGradedCommutative_degree k A hc hc'

/-- The induced maps preserve the grading by the integers.

Blueprint: `def:dr-cohomology`, and the shift in `lem:dr-ordinary-basic`. -/
theorem isHomogeneousOfShift_map (φ : A →ₐ[k] A') :
    IsHomogeneousOfShift (grading k A) (grading k A') 0 (map φ) :=
  isHomogeneousOfShift_zero_iff.2 fun _ _ hc =>
    map_mem_coarsenGrading (degree k A) (Nat.castAddMonoidHom ℤ) (degree k A')
      (map φ).toLinearMap (fun _ _ hm => map_mem_degree φ hm) hc

/-! ### The kernel and image of `d` in each degree -/

variable (k A) in
/-- The image of `d` in degree `n`, as a `k`-submodule of the forms of degree `n`: the range of
`powerD k A (n - 1)`, and zero for `n = 0`. Degree `-1` is zero, which is what makes `n = 0` no
exception.

Blueprint: `def:dr-cohomology`. -/
def rangeD : (n : ℕ) → Submodule k (⋀[A]^n Ω[A⁄k])
  | 0 => ⊥
  | n + 1 => LinearMap.range (powerD k A n)

@[simp]
theorem rangeD_zero : rangeD k A 0 = ⊥ :=
  rfl

@[simp]
theorem rangeD_succ (n : ℕ) :
    rangeD k A (n + 1) = LinearMap.range (powerD k A n) :=
  rfl

/-- A form of degree `n` is in the image of `d` in degree `n` as soon as it is exact: a primitive
can always be taken of degree `n - 1`. -/
theorem mem_rangeD_iff {n : ℕ} {x : ⋀[A]^n Ω[A⁄k]} :
    x ∈ rangeD k A n ↔ ∃ y, d k y = (x : Forms k A) := by
  cases n with
  | zero =>
    rw [rangeD_zero, Submodule.mem_bot]
    constructor
    · rintro rfl
      exact ⟨0, by simp⟩
    · exact fun h => Subtype.ext (eq_zero_of_mem_exteriorPower_zero_of_exists x.2 h)
  | succ n =>
    rw [rangeD_succ, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · intro h
      obtain ⟨y, hy, hyx⟩ := exists_mem_exteriorPower_d_eq x.2 h
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

/-- An element of the kernel of `powerD` is a closed form. -/
theorem d_eq_zero_of_mem_ker {n : ℕ} (z : LinearMap.ker (powerD k A n)) :
    d k (z.1 : Forms k A) = 0 :=
  congrArg Subtype.val (LinearMap.mem_ker.1 z.2)

variable (k A) in
/-- The class of a closed form of degree `n`, as a surjective `k`-linear map onto `H^n`. -/
def ofKer (n : ℕ) : LinearMap.ker (powerD k A n) →ₗ[k] degree k A n where
  toFun z := ⟨mk z.1 (d_eq_zero_of_mem_ker z), mk_mem_degree z.1.2 _⟩
  map_add' _ _ := Subtype.ext (mk_add _ _ _ _).symm
  map_smul' c _ := Subtype.ext (mk_smul c _ _).symm

@[simp]
theorem coe_ofKer {n : ℕ} (z : LinearMap.ker (powerD k A n)) :
    (ofKer k A n z : Cohomology k A) = mk z.1 (d_eq_zero_of_mem_ker z) :=
  rfl

theorem ofKer_surjective (n : ℕ) : Function.Surjective (ofKer k A n) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, hxn, rfl⟩ := mem_degree_iff.1 hc
  exact ⟨⟨⟨x, hxn⟩, LinearMap.mem_ker.2 (Subtype.ext hx)⟩, rfl⟩

theorem ker_ofKer (n : ℕ) :
    LinearMap.ker (ofKer k A n) =
      (rangeD k A n).comap (LinearMap.ker (powerD k A n)).subtype := by
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_comap, mem_rangeD_iff, ← Subtype.coe_inj]
  exact mk_eq_zero_iff

variable (k A) in
/-- The piece `H^n` of the total cohomology is `ker d / im d` in degree `n`, as the blueprint
defines it. The image of `d` is `rangeD k A n`, which is the range of `powerD k A (n - 1)` and zero
for `n = 0`.

Blueprint: `def:dr-cohomology`. -/
def degreeEquiv (n : ℕ) :
    (LinearMap.ker (powerD k A n) ⧸
      (rangeD k A n).comap (LinearMap.ker (powerD k A n)).subtype) ≃ₗ[k] degree k A n :=
  (Submodule.quotEquivOfEq _ _ (ker_ofKer n).symm).trans
    ((ofKer k A n).quotKerEquivOfSurjective (ofKer_surjective n))

/-- The identification of `H^n` with `ker d / im d` sends the class of `z` to its class. -/
@[simp]
theorem coe_degreeEquiv_mk {n : ℕ} (z : LinearMap.ker (powerD k A n)) :
    (degreeEquiv k A n (Submodule.Quotient.mk z) : Cohomology k A) =
      mk z.1 (d_eq_zero_of_mem_ker z) :=
  rfl

end Cohomology

end OrlikSolomon.DeRham
