/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.RingTheory.Smooth.Basic

/-!
# One-forms for a smooth principal pair

For a regular element `f` of a commutative `k`-algebra `A`, put `S = A/(f)`.
Formal smoothness of `S` splits the conormal sequence of one-forms. Formal smoothness
of `A` then lifts its splitting functional to a global derivation `v` with
`v(f) = 1 + f * h`. These constructions use no coordinates, finite presentation,
connectedness or nonzero-ring hypothesis, and allow `f` to be a unit.

## Main definitions and results

* `principalCotangentEquiv`: the conormal module `(f)/(f²)` is the free `S`-module on `f`.
* `conormalFunctional`: a functional on `S ⊗[A] Ω[A⁄k]` taking `df` to one.
* `splitConormalSequence`: the splitting of one-forms into the conormal line and `Ω[S⁄k]`.
* `existsNormalDerivationModulo`: a global normal derivation modulo the divisor.

Blueprint: `lem:dr-conormal` and the global part of `lem:dr-normal-derivation`.
The higher-form localization and Koszul assertions of `DeRham/SmoothPair` are separate.
-/

@[expose] public section

open scoped TensorProduct
open KaehlerDifferential

namespace OrlikSolomon.DeRham

variable {A : Type*} [CommRing A] (f : A)

private noncomputable def cotangentLine :
    (A ⧸ Ideal.span {f}) →ₗ[A ⧸ Ideal.span {f}] (Ideal.span {f}).Cotangent :=
  LinearMap.toSpanSingleton _ _
    ((Ideal.span {f}).toCotangent ⟨f, Ideal.mem_span_singleton_self f⟩)

private lemma cotangentLine_mk (a : A) :
    cotangentLine f (Ideal.Quotient.mk (Ideal.span {f}) a) =
      (Ideal.span {f}).toCotangent (a • ⟨f, Ideal.mem_span_singleton_self f⟩) := by
  change (Ideal.Quotient.mk (Ideal.span {f}) a) •
    (Ideal.span {f}).toCotangent ⟨f, Ideal.mem_span_singleton_self f⟩ = _
  rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul, map_smul]

private lemma bijective_cotangentLine (hf : f ∈ nonZeroDivisors A) :
    Function.Bijective (cotangentLine f) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro s hs
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
    rw [cotangentLine_mk] at hs
    have haf : a * f ∈ (Ideal.span {f}) ^ 2 := (Ideal.toCotangent_eq_zero _ _).mp hs
    rw [pow_two, Ideal.span_singleton_mul_span_singleton] at haf
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp haf
    have hab : b * f = a := (isRegular_iff_mem_nonZeroDivisors.mpr hf).2
      (by simpa only [mul_assoc] using hb)
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton'.mpr ⟨b, hab⟩)
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ x
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp a.property
    refine ⟨Ideal.Quotient.mk (Ideal.span {f}) b, ?_⟩
    rw [cotangentLine_mk]
    exact congrArg (Ideal.span {f}).toCotangent (Subtype.ext hb)

/-- Multiplication by a regular element identifies `A/(f)` with `(f)/(f²)`.
No nonzero-ring hypothesis is needed. Blueprint: the conormal line in `lem:dr-conormal`. -/
@[no_expose] noncomputable def principalCotangentEquiv (hf : f ∈ nonZeroDivisors A) :
    (A ⧸ Ideal.span {f}) ≃ₗ[A ⧸ Ideal.span {f}] (Ideal.span {f}).Cotangent :=
  LinearEquiv.ofBijective (cotangentLine f) (bijective_cotangentLine f hf)

/-- The conormal-line identification takes the class of `a` to the class of `a*f`. -/
@[simp] lemma principalCotangentEquiv_mk (hf : f ∈ nonZeroDivisors A) (a : A) :
    principalCotangentEquiv f hf (Ideal.Quotient.mk (Ideal.span {f}) a) =
      (Ideal.span {f}).toCotangent (a • ⟨f, Ideal.mem_span_singleton_self f⟩) :=
  cotangentLine_mk f a

/-- The chosen generator of the conormal line is the image of one. -/
@[simp] lemma principalCotangentEquiv_one (hf : f ∈ nonZeroDivisors A) :
    principalCotangentEquiv f hf 1 =
      (Ideal.span {f}).toCotangent ⟨f, Ideal.mem_span_singleton_self f⟩ := by
  change (1 : A ⧸ Ideal.span {f}) •
    (Ideal.span {f}).toCotangent ⟨f, Ideal.mem_span_singleton_self f⟩ = _
  exact one_smul _ _

variable {k : Type*} [CommRing k] [Algebra k A]

private lemma exists_cotangentRetraction {B : Type*} [CommRing B]
    [Algebra k B] [Algebra A B] [IsScalarTower k A B] [Algebra.FormallySmooth k B]
    (h : Function.Surjective (algebraMap A B)) :
    ∃ l, l ∘ₗ kerCotangentToTensor k A B = LinearMap.id := by
  let g := (IsScalarTower.toAlgHom k A B).kerSquareLift
  have hg : Function.Surjective g := by
    intro b
    obtain ⟨a, rfl⟩ := h b
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hgnil : IsNilpotent (RingHom.ker g.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [AlgHom.ker_kerSquareLift]
    exact Ideal.cotangentIdeal_square _
  let σ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k B) g hg hgnil
  have hσ : g.comp σ = AlgHom.id k B :=
    Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  exact ⟨_, ((retractionKerCotangentToTensorEquivSection (R := k) h).symm ⟨σ, hσ⟩).property⟩

private lemma exists_retractionToIdeal {B : Type*} [CommRing B]
    [Algebra k B] [Algebra A B] [IsScalarTower k A B] [Algebra.FormallySmooth k B]
    (h : Function.Surjective (algebraMap A B)) (J : Ideal A)
    (hJ : RingHom.ker (algebraMap A B) = J) :
    ∃ l : (B ⊗[A] Ω[A⁄k]) →ₗ[A] J.Cotangent,
      ∀ x : J, l (1 ⊗ₜ D k A x) = J.toCotangent x := by
  subst J
  obtain ⟨l, hl⟩ := exists_cotangentRetraction (k := k) h
  refine ⟨l, fun x ↦ ?_⟩
  simpa only [LinearMap.comp_apply, kerCotangentToTensor_toCotangent,
    LinearMap.id_apply] using LinearMap.congr_fun hl (Ideal.toCotangent _ x)

/-- The conormal map sends a scalar `s` to `s ⊗ df`. -/
noncomputable def conormalMap :
    (A ⧸ Ideal.span {f}) →ₗ[A ⧸ Ideal.span {f}]
      (A ⧸ Ideal.span {f}) ⊗[A] Ω[A⁄k] :=
  LinearMap.toSpanSingleton _ _ (1 ⊗ₜ[A] D k A f)

/-- Evaluation of the conormal map. -/
@[simp] lemma conormalMap_apply (s : A ⧸ Ideal.span {f}) :
    conormalMap (k := k) f s = s ⊗ₜ[A] D k A f := by
  simp [conormalMap, TensorProduct.smul_tmul']

/-- The principal conormal sequence is right exact, without smoothness or regularity. -/
lemma exact_conormalMap :
    Function.Exact (conormalMap (k := k) f)
      (mapBaseChange k A (A ⧸ Ideal.span {f})) := by
  let I : Ideal A := Ideal.span {f}
  have hi : RingHom.ker (algebraMap A (A ⧸ I)) = I := Ideal.mk_ker
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange k A (A ⧸ I)
      Ideal.Quotient.mk_surjective x).mp hx
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ y
    have hy : y.val ∈ I := by simpa only [hi] using y.property
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
    let yf : RingHom.ker (algebraMap A (A ⧸ I)) := ⟨f, by simp [I]⟩
    have hyf : y = a • yf := Subtype.ext ha.symm
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [hyf, map_smul, map_smul, kerCotangentToTensor_toCotangent]
    change (Ideal.Quotient.mk I a) • ((1 : A ⧸ I) ⊗ₜ[A] D k A f) =
      a • ((1 : A ⧸ I) ⊗ₜ[A] D k A f)
    rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
  · rintro ⟨a, rfl⟩
    simp [mapBaseChange_tmul, map_D]

section QuotientSmooth

variable [Algebra.FormallySmooth k (A ⧸ Ideal.span {f})]

/-- Smoothness of `A/(f)` gives a functional taking `df mod f` to one.
Ambient smoothness is not required. Blueprint: `lem:dr-conormal`. -/
lemma exists_conormalFunctional (hf : f ∈ nonZeroDivisors A) :
    ∃ l : ((A ⧸ Ideal.span {f}) ⊗[A] Ω[A⁄k]) →ₗ[A ⧸ Ideal.span {f}]
        (A ⧸ Ideal.span {f}),
      l (1 ⊗ₜ D k A f) = 1 := by
  have h : Function.Surjective (algebraMap A (A ⧸ Ideal.span {f})) :=
    Ideal.Quotient.mk_surjective
  obtain ⟨l, hl⟩ := exists_retractionToIdeal (k := k) h (Ideal.span {f}) Ideal.mk_ker
  refine ⟨(principalCotangentEquiv f hf).symm.toLinearMap.comp
    (l.extendScalarsOfSurjective h), ?_⟩
  change (principalCotangentEquiv f hf).symm (l (1 ⊗ₜ D k A f)) = 1
  rw [hl ⟨f, Ideal.mem_span_singleton_self f⟩, ← principalCotangentEquiv_one f hf,
    LinearEquiv.symm_apply_apply]

/-- A chosen splitting functional on one-forms along a smooth principal divisor.
It depends on a formal-smoothness lift; no choice of coordinates is involved. -/
@[no_expose] noncomputable def conormalFunctional (hf : f ∈ nonZeroDivisors A) :
    ((A ⧸ Ideal.span {f}) ⊗[A] Ω[A⁄k]) →ₗ[A ⧸ Ideal.span {f}] (A ⧸ Ideal.span {f}) :=
  (exists_conormalFunctional (k := k) f hf).choose

/-- The splitting functional evaluates to one on the conormal generator. -/
lemma conormalFunctional_df (hf : f ∈ nonZeroDivisors A) :
    conormalFunctional (k := k) f hf (1 ⊗ₜ D k A f) = 1 :=
  (exists_conormalFunctional (k := k) f hf).choose_spec

/-- The functional reads the scalar coefficient of the conormal generator. -/
@[simp] lemma conormalFunctional_tmul_df (hf : f ∈ nonZeroDivisors A)
    (s : A ⧸ Ideal.span {f}) :
    conormalFunctional (k := k) f hf (s ⊗ₜ[A] D k A f) = s := by
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, conormalFunctional_df,
    smul_eq_mul, mul_one]

/-- The functional is a retraction of the conormal map. -/
@[simp] lemma conormalFunctional_comp_conormalMap (hf : f ∈ nonZeroDivisors A) :
    (conormalFunctional (k := k) f hf).comp (conormalMap (k := k) f) = LinearMap.id := by
  apply LinearMap.ext
  intro s
  change conormalFunctional (k := k) f hf (s • ((1 : A ⧸ Ideal.span {f}) ⊗ₜ[A] D k A f)) = s
  rw [map_smul, conormalFunctional_df, smul_eq_mul, mul_one]

/-- The conormal line embeds in the restricted module of one-forms. -/
lemma conormalMap_injective (hf : f ∈ nonZeroDivisors A) :
    Function.Injective (conormalMap (k := k) f) := by
  have h : Function.LeftInverse (conormalFunctional (k := k) f hf)
      (conormalMap (k := k) f) :=
    LinearMap.congr_fun (conormalFunctional_comp_conormalMap (k := k) f hf)
  exact h.injective

/-- A chosen splitting of the principal conormal sequence.
The first coordinate is the conormal functional and the second is restriction of forms.
Blueprint: `lem:dr-conormal`. -/
@[no_expose] noncomputable def splitConormalSequence (hf : f ∈ nonZeroDivisors A) :
    ((A ⧸ Ideal.span {f}) ⊗[A] Ω[A⁄k]) ≃ₗ[A ⧸ Ideal.span {f}]
      (A ⧸ Ideal.span {f}) × Ω[(A ⧸ Ideal.span {f})⁄k] :=
  ((exact_conormalMap (k := k) f).splitInjectiveEquiv
    (mapBaseChange_surjective k A _ Ideal.Quotient.mk_surjective)
    ⟨conormalFunctional (k := k) f hf, conormalFunctional_comp_conormalMap (k := k) f hf⟩).val

/-- The coordinates of the conormal splitting are its functional and restriction. -/
@[simp] lemma splitConormalSequence_apply (hf : f ∈ nonZeroDivisors A)
    (x : (A ⧸ Ideal.span {f}) ⊗[A] Ω[A⁄k]) :
    splitConormalSequence (k := k) f hf x =
      (conormalFunctional (k := k) f hf x, mapBaseChange k A (A ⧸ Ideal.span {f}) x) := by
  rfl

/-- The inverse splitting sends the conormal summand to multiples of `df`. -/
@[simp] lemma splitConormalSequence_symm_apply_zero (hf : f ∈ nonZeroDivisors A)
    (s : A ⧸ Ideal.span {f}) :
    (splitConormalSequence (k := k) f hf).symm (s, 0) = s ⊗ₜ[A] D k A f := by
  apply (splitConormalSequence (k := k) f hf).injective
  simp [mapBaseChange_tmul, map_D]

/-- A smooth principal pair has a global normal derivation modulo its divisor.
The value need only be one modulo `f`, including when `A` is disconnected.
Blueprint: the global assertion in `lem:dr-normal-derivation`. -/
lemma existsNormalDerivationModulo [Algebra.FormallySmooth k A]
    (hf : f ∈ nonZeroDivisors A) :
    ∃ (v : Derivation k A A) (h : A), v f = 1 + f * h := by
  let l₀ := (conormalFunctional (k := k) f hf).restrictScalars A |>.comp
    (TensorProduct.mk A (A ⧸ Ideal.span {f}) Ω[A⁄k] 1)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property
    (Ideal.span {f}).mkQ l₀ (Submodule.mkQ_surjective _)
  let v : Derivation k A A := l.compDer (D k A)
  have hv : Ideal.Quotient.mk (Ideal.span {f}) (v f) = 1 := by
    change ((Ideal.span {f}).mkQ.comp l) (D k A f) = 1
    rw [hl]
    exact conormalFunctional_df (k := k) f hf
  have hm : v f - 1 ∈ Ideal.span {f} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hv, map_one, sub_self]
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton.mp hm
  refine ⟨v, h, ?_⟩
  rw [← hh]
  ring

end QuotientSmooth

/-- The equation and the value of a normal derivation generate the unit ideal.
Blueprint: the two-open cover in `lem:dr-normal-derivation`. -/
lemma span_pair_eq_top_of_normalDerivationModulo (v : Derivation k A A) (h : A)
    (hv : v f = 1 + f * h) : Ideal.span {f, v f} = ⊤ := by
  rw [hv, Ideal.span_pair_add_left_mul]
  simp only [Ideal.span_insert, Ideal.span_singleton_one, sup_top_eq]

end OrlikSolomon.DeRham
