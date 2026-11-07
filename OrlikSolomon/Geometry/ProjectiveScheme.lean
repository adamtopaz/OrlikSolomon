/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import OrlikSolomon.Geometry.Projective

/-!
# The projective complement as an open subscheme of `Proj`

This file identifies the ring `O(U_P)` of `OrlikSolomon/Geometry/Projective.lean` with the actual
complement of the hyperplanes of `P` in the projective space `Proj Sym(W*)`, using Mathlib's scheme
`Proj`.

## Main definitions

* `ProjectiveArrangement.complementOpen P`: the open subscheme of `Proj Sym(W*)` of the points on no
  hyperplane of `P`, by `mem_complementOpen_iff`.
* `ProjectiveArrangement.complementOpenIso P`: for nonempty `P`, this open subscheme is the spectrum
  of `O(U_P)`.
* `ProjectiveArrangement.complementι P`: the open immersion `Spec O(U_P) → Proj Sym(W*)`, with image
  `complementOpen P`, by `opensRange_complementι`.
* `ProjectiveArrangement.ComplementRing.awayEquiv`: for any equations `F H` of the hyperplanes of
  `P`, the ring `O(U_P)` is Mathlib's homogeneous localization `Away 𝒜 (∏ H, F H)`, the ring of
  degree-zero fractions with denominators a power of the product.
* `OrlikSolomon.projIsoMvPolynomial`: in a basis of `W*`, the scheme `Proj Sym(W*)` is
  `Proj k[x_i]`.

## Main results

* `OrlikSolomon.mapId_bijective_of_forall_exists_mul_mem`: a homogeneous localization does not
  change when the denominators are enlarged to elements that homogeneously divide the old
  denominators.
* `ProjectiveArrangement.complementOpen_eq_iInf`, `complementOpen_eq_iInf_basicOpen`: the
  complement is the intersection of the charts `D₊(ℓ)` of the equations, which depend only on the
  hyperplanes (`basicOpen_coord_eq_of_ker_eq`). It is `⊤` for empty `P` (`complementOpen_eq_top`).
* `ProjectiveArrangement.complementι_eq_awayι_of_ker_eq`: the open immersion of the complement,
  and so `complementOpenIso`, do not depend on the equations chosen to define them.

## Implementation notes

The proof of the structure theorem does not use schemes, and none of its modules may import this
file. It is what makes the statement of the theorem recognizable. The scheme layer of the geometric
refactor builds on it: `OrlikSolomon/Geometry/Schemes/Projective.lean` makes the complement a scheme
over `Spec k`. Mathlib has no projective
space as a named scheme, so `Proj Sym(W*)` is the definition of the projectivization of `W`, and
`projIsoMvPolynomial` relates it to the polynomial ring in a basis.

## Blueprint

The identification of the object of `def:projective` with the complement in `P^n` that the blueprint
means. The blueprint itself does not spell it out, as it works only with the decone. The first
sentence of the proof of `lem:decone` is `complementOpen_le_basicOpen`. The lemmas on the
intersection of charts and their independence of equations are part of `def:geo-projective` of the
geometric refactor blueprint.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Module HomogeneousLocalization

universe u

namespace OrlikSolomon

open CoordinateRing

section MapId

variable {ι A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] [AddCommMonoid ι]
variable [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜] {S T : Submonoid A}

/-- A homogeneous localization does not change when its denominators `S` are enlarged to a submonoid
`T` of non-zero-divisors, as long as each `t ∈ T` multiplies into `S` by a homogeneous element. -/
theorem mapId_bijective_of_forall_exists_mul_mem (h : S ≤ T) (hT : T ≤ nonZeroDivisors A)
    (hdvd : ∀ t ∈ T, ∃ (i : ι) (c : A), c ∈ 𝒜 i ∧ t * c ∈ S) :
    Function.Bijective (mapId 𝒜 h) := by
  have key (c : NumDenSameDeg 𝒜 S) : (mapId 𝒜 h (HomogeneousLocalization.mk c)).val =
      Localization.mk (c.num : A) ⟨c.den, h c.den_mem⟩ := rfl
  constructor
  · intro x y hxy
    obtain ⟨⟨m, a, b, hb⟩, rfl⟩ := mk_surjective x
    obtain ⟨⟨n, c, d, hd⟩, rfl⟩ := mk_surjective y
    have hval := congrArg val hxy
    rw [key, key, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hval
    obtain ⟨t, ht⟩ := hval
    have ht' := (mul_cancel_left_mem_nonZeroDivisors (hT t.2)).1 ht
    refine val_injective _ ?_
    simp only [val_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, congrArg _ ht'⟩
  · intro z
    obtain ⟨⟨n, a, b, hb⟩, rfl⟩ := mk_surjective z
    obtain ⟨i, c, hc, hbc⟩ := hdvd _ hb
    refine ⟨mk ⟨n + i, ⟨a * c, SetLike.mul_mem_graded a.2 hc⟩,
      ⟨b * c, SetLike.mul_mem_graded b.2 hc⟩, hbc⟩, val_injective _ ?_⟩
    rw [key, val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [mul_comm, mul_left_comm]⟩

/-- Mapping `A_{(f)}` to `A_{(fg)}`, sending `a / f ^ n` to `a g ^ n / (f g) ^ n`, and then to the
homogeneous localization at `T`, is the inclusion of `A_{(f)}`. -/
theorem mapId_comp_awayMap {f g : A} {d e : ι} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hfT : Submonoid.powers f ≤ T) (hT : Submonoid.powers (f * g) ≤ T) :
    (mapId 𝒜 hT).comp (awayMap 𝒜 hg rfl) = mapId 𝒜 hfT := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ hf z
  rw [RingHom.comp_apply, awayMap_mk]
  have h₁ : (mapId 𝒜 hT (Away.mk 𝒜 (SetLike.mul_mem_graded hf hg) n (a * g ^ n)
      (by rw [smul_add]; exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n hg)))).val =
      Localization.mk (a * g ^ n) ⟨(f * g) ^ n, hT ⟨n, rfl⟩⟩ := rfl
  have h₂ : (mapId 𝒜 hfT (Away.mk 𝒜 hf n a ha)).val = Localization.mk a ⟨f ^ n, hfT ⟨n, rfl⟩⟩ :=
    rfl
  rw [h₁, h₂, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, mul_pow]; ring⟩

end MapId

section GradedIso

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
variable [GradedRing 𝒜] [GradedRing ℬ]

/-- A graded map with a graded section carries the irrelevant ideal onto the irrelevant ideal. -/
theorem irrelevant_le_map_of_comp_eq_id (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (h : f.comp g = .id ℬ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := fun b hb ↦ by
  have hg : g b ∈ HomogeneousIdeal.irrelevant 𝒜 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      ← map_directSumDecompose ℬ 𝒜 g]
    have hb' : (DirectSum.decompose ℬ b 0 : B) = 0 := by
      simpa [GradedRing.proj_apply] using hb
    rw [hb', map_zero]
  have hfg : f (g b) = b := GradedRingHom.congr_fun h b
  rw [← hfg]
  exact Ideal.mem_map_of_mem _ hg

/-- A graded endomorphism equal to the identity induces the identity of `Proj`. -/
theorem proj_map_eq_id {f : 𝒜 →+*ᵍ 𝒜} (h : f = .id 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf = 𝟙 (Proj 𝒜) := by
  subst h
  exact Proj.map_id

/-- An isomorphism of graded rings induces an isomorphism of their `Proj`. -/
def projIsoOfGraded (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : f.comp g = .id ℬ)
    (hgf : g.comp f = .id 𝒜) : Proj ℬ ≅ Proj 𝒜 where
  hom := Proj.map f (irrelevant_le_map_of_comp_eq_id f g hfg)
  inv := Proj.map g (irrelevant_le_map_of_comp_eq_id g f hgf)
  hom_inv_id := by
    rw [← Proj.map_comp, proj_map_eq_id hfg]
  inv_hom_id := by
    rw [← Proj.map_comp, proj_map_eq_id hgf]

end GradedIso

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

namespace ProjectiveArrangement

variable {P : ProjectiveArrangement k W} {ℓ : Dual k W}

/-- A linear form chosen for each hyperplane of `P`, whose kernel is that hyperplane. Everything
below is stated for all such forms, or does not depend on them. -/
def form (H : P) : Dual k W :=
  (exists_ker_eq H.2).choose

@[simp]
theorem ker_form (H : P) : LinearMap.ker (form H) = H :=
  (exists_ker_eq H.2).choose_spec

section Product

variable (F : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H)

/-- A product of equations, one for each hyperplane of `P`, is homogeneous of degree the number of
hyperplanes. -/
theorem prod_coord_mem_symmetricGrading :
    ∏ H : P, coord (F H).toAffineMap ∈ symmetricGrading k (Dual k W) P.card := by
  have := SetLike.prod_mem_graded (A := symmetricGrading k (Dual k W)) (F := Finset.univ)
    (g := fun H : P ↦ coord (F H).toAffineMap) (i := fun _ ↦ 1)
    fun H _ ↦ coord_toAffineMap_mem (F H)
  simpa using this

include hF in
theorem prod_coord_mem_equationSubmonoid_cone :
    ∏ H : P, coord (F H).toAffineMap ∈ P.cone.equationSubmonoid :=
  Submonoid.prod_mem _ fun H _ ↦ coord_mem_equationSubmonoid_cone (by simp [hF])

include hF in
/-- The powers of a product of equations are products of equations. -/
theorem powers_prod_coord_le :
    Submonoid.powers (∏ H : P, coord (F H).toAffineMap) ≤ P.cone.equationSubmonoid :=
  Submonoid.powers_le.2 (prod_coord_mem_equationSubmonoid_cone F hF)

include hF in
/-- Every product of equations of hyperplanes of `P` multiplies by a homogeneous element into a
power of `∏ H, F H`. -/
theorem exists_mul_mem_powers_prod_coord {t : CoordinateRing k W}
    (ht : t ∈ P.cone.equationSubmonoid) :
    ∃ (i : ℕ) (c : CoordinateRing k W), c ∈ symmetricGrading k (Dual k W) i ∧
      t * c ∈ Submonoid.powers (∏ H : P, coord (F H).toAffineMap) := by
  classical
  refine forall_mem_equationSubmonoid_cone
    (p := fun t ↦ ∃ (i : ℕ) (c : CoordinateRing k W), c ∈ symmetricGrading k (Dual k W) i ∧
      t * c ∈ Submonoid.powers (∏ H : P, coord (F H).toAffineMap))
    ⟨0, 1, SetLike.GradedOne.one_mem, by simp⟩
    (fun x y ⟨i, c, hc, hxc⟩ ⟨j, d, hd, hyd⟩ ↦ ⟨i + j, c * d, SetLike.GradedMul.mul_mem hc hd, by
      rw [mul_mul_mul_comm]
      exact mul_mem hxc hyd⟩)
    (fun ℓ hℓ ↦ ?_) ht
  obtain ⟨u, hu⟩ := exists_eq_smul_of_ker_eq (hF ⟨_, hℓ⟩) (ne_zero_of_ker_mem hℓ)
  have hprod := SetLike.prod_mem_graded (symmetricGrading k (Dual k W))
    (F := Finset.univ.erase (⟨_, hℓ⟩ : P)) (fun _ ↦ 1) (fun H : P ↦ coord (F H).toAffineMap)
    fun H _ ↦ coord_toAffineMap_mem (F H)
  refine ⟨_, _, (symmetricGrading k (Dual k W) _).smul_mem (u : k) hprod, ⟨1, ?_⟩⟩
  beta_reduce
  rw [pow_one, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨_, hℓ⟩ : P)), hu,
    coord_toAffineMap, coord_toAffineMap, map_smul, smul_mul_assoc, mul_smul_comm]

end Product

/-! ### The comparison with `Away` -/

namespace ComplementRing

section Away

variable (F : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H)

/-- For any equations `F H` of the hyperplanes of `P`, the ring `O(U_P)` is Mathlib's homogeneous
localization `Away` of their product, which is the ring of the chart `D₊(∏ H, F H)` of `Proj`.
Allowing denominators in all equations rather than in powers of one product is what makes the
definition of `O(U_P)` free of choices.

Blueprint: `def:projective`. -/
def awayEquiv :
    Away (symmetricGrading k (Dual k W)) (∏ H : P, coord (F H).toAffineMap) ≃+* P.ComplementRing :=
  RingEquiv.ofBijective (mapId (symmetricGrading k (Dual k W)) (powers_prod_coord_le F hF))
    (mapId_bijective_of_forall_exists_mul_mem _ _
      (Arrangement.equationSubmonoid_le_nonZeroDivisors)
      fun _ ht ↦ exists_mul_mem_powers_prod_coord F hF ht)

/-- The comparison with `Away` sends the fraction `a / f ^ n` to the fraction `a / f ^ n`. -/
theorem awayEquiv_mk {n : ℕ} {a : CoordinateRing k W}
    (ha : a ∈ symmetricGrading k (Dual k W) (n • P.card)) :
    awayEquiv F hF (Away.mk _ (prod_coord_mem_symmetricGrading F) n a ha) =
      mk ha (SetLike.pow_mem_graded n (prod_coord_mem_symmetricGrading F))
        (pow_mem (prod_coord_mem_equationSubmonoid_cone F hF) n) :=
  rfl

end Away

end ComplementRing

/-! ### The complement in `Proj` -/

section Proj

variable (P)

/-- The product of the chosen equations of the hyperplanes of `P`. It unfolds at implicit
transparency, so that `Away 𝒜 (formProduct P)`, the ring of the chart `complementOpen P`, is the
ring `Away 𝒜 (∏ H, form H)` of `ComplementRing.awayEquiv` when Lean checks the types of
composites. -/
@[implicit_reducible]
def formProduct : CoordinateRing k W :=
  ∏ H : P, coord (form H).toAffineMap

/-- The product of the chosen equations is homogeneous of degree the number of hyperplanes. -/
theorem formProduct_mem_symmetricGrading :
    formProduct P ∈ symmetricGrading k (Dual k W) P.card :=
  prod_coord_mem_symmetricGrading form

/-- The complement of the hyperplanes of `P` in the projective space `Proj Sym(W*)`, as an open
subscheme. It is the set of points that are on no hyperplane of `P`, by `mem_complementOpen_iff`,
which does not depend on a choice of equations.

Blueprint: `def:projective`. -/
def complementOpen : (Proj (symmetricGrading k (Dual k W))).Opens :=
  Proj.basicOpen (symmetricGrading k (Dual k W)) (formProduct P)

variable {P}

/-- A point of `Proj Sym(W*)` is off the zero locus of a product of equations of the hyperplanes of
`P` exactly when it is off the zero locus of each equation of each hyperplane. -/
theorem prod_coord_notMem_iff (F : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H)
    (x : Proj (symmetricGrading k (Dual k W))) :
    ∏ H : P, coord (F H).toAffineMap ∉ x.asHomogeneousIdeal ↔
      ∀ ℓ : Dual k W, LinearMap.ker ℓ ∈ P → coord ℓ.toAffineMap ∉ x.asHomogeneousIdeal := by
  have hprime : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  change ∏ H : P, coord (F H).toAffineMap ∉ x.asHomogeneousIdeal.toIdeal ↔
    ∀ ℓ : Dual k W, LinearMap.ker ℓ ∈ P → coord ℓ.toAffineMap ∉ x.asHomogeneousIdeal.toIdeal
  rw [Ideal.IsPrime.prod_mem_iff]
  constructor
  · intro h ℓ hℓ hmem
    obtain ⟨u, hu⟩ := exists_eq_smul_of_ker_eq (hF ⟨_, hℓ⟩) (ne_zero_of_ker_mem hℓ)
    refine h ⟨⟨_, hℓ⟩, Finset.mem_univ _, ?_⟩
    rw [hu, coord_toAffineMap, map_smul, Algebra.smul_def, ← coord_toAffineMap]
    exact Ideal.mul_mem_left _ _ hmem
  · rintro h ⟨H, -, hH⟩
    exact h (F H) (by simp [hF]) hH

/-- A point of `Proj Sym(W*)` is in the complement exactly when no equation of a hyperplane of `P`
vanishes at it. -/
theorem mem_complementOpen_iff (x : Proj (symmetricGrading k (Dual k W))) :
    x ∈ complementOpen P ↔
      ∀ ℓ : Dual k W, LinearMap.ker ℓ ∈ P → coord ℓ.toAffineMap ∉ x.asHomogeneousIdeal :=
  prod_coord_notMem_iff form ker_form x

/-- The complement is also the chart of the product of any other equations. -/
theorem complementOpen_eq_basicOpen (F : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H) :
    complementOpen P = Proj.basicOpen (symmetricGrading k (Dual k W))
      (∏ H : P, coord (F H).toAffineMap) :=
  TopologicalSpace.Opens.ext <| Set.ext fun x ↦ by
    change x ∈ complementOpen P ↔ x ∈ Proj.basicOpen _ _
    rw [mem_complementOpen_iff, Proj.mem_basicOpen, prod_coord_notMem_iff F hF]

/-- Every point of the complement lies in the standard chart `ℓ₀ ≠ 0`, for an equation `ℓ₀` of any
hyperplane of `P`.

Blueprint: `lem:decone`. -/
theorem complementOpen_le_basicOpen {ℓ₀ : Dual k W} (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    complementOpen P ≤
      Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ₀.toAffineMap) :=
  fun x hx ↦ (mem_complementOpen_iff x).1 hx ℓ₀ hℓ₀

/-- The chart `D₊(ℓ)` of a linear form depends only on its kernel. In particular, multiplying an
equation by a nonzero scalar does not change its chart.

Blueprint: `def:geo-projective`. -/
theorem basicOpen_coord_eq_of_ker_eq {ℓ ℓ' : Dual k W} (h : LinearMap.ker ℓ = LinearMap.ker ℓ')
    (hℓ' : ℓ' ≠ 0) :
    Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap) =
      Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ'.toAffineMap) := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_ker_eq h hℓ'
  refine TopologicalSpace.Opens.ext <| Set.ext fun x ↦ ?_
  change x ∈ Proj.basicOpen _ _ ↔ x ∈ Proj.basicOpen _ _
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen, coord_toAffineMap, coord_toAffineMap, map_smul,
    Algebra.smul_def]
  exact not_congr (Ideal.unit_mul_mem_iff_mem x.asHomogeneousIdeal.toIdeal
    ((IsUnit.mk0 _ c.ne_zero).map _))

/-- The complement is the intersection of the charts `D₊(ℓ)` of all equations `ℓ` of all hyperplanes
of `P`. It is `⊤` for empty `P`, by `complementOpen_eq_top`.

Blueprint: `def:geo-projective`. -/
theorem complementOpen_eq_iInf :
    complementOpen P = ⨅ (ℓ : Dual k W) (_ : LinearMap.ker ℓ ∈ P),
      Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap) :=
  le_antisymm (le_iInf₂ fun _ hℓ ↦ complementOpen_le_basicOpen hℓ) fun x hx ↦
    (mem_complementOpen_iff x).2 fun ℓ hℓ ↦ iInf₂_le (κ := fun ℓ : Dual k W ↦ LinearMap.ker ℓ ∈ P)
      (f := fun ℓ _ ↦ Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap)) ℓ hℓ hx

/-- The complement is the intersection of the charts of any choice of equations, one for each
hyperplane of `P`.

Blueprint: `def:geo-projective`. -/
theorem complementOpen_eq_iInf_basicOpen (F : P → Dual k W)
    (hF : ∀ H : P, LinearMap.ker (F H) = H) :
    complementOpen P =
      ⨅ H : P, Proj.basicOpen (symmetricGrading k (Dual k W)) (coord (F H).toAffineMap) := by
  rw [complementOpen_eq_iInf]
  refine le_antisymm (le_iInf fun H ↦ iInf₂_le (F H) (by rw [hF]; exact H.2))
    (le_iInf₂ fun ℓ hℓ ↦ ?_)
  rw [basicOpen_coord_eq_of_ker_eq (hF ⟨_, hℓ⟩).symm (ne_zero_of_ker_mem (by rwa [hF]))]
  exact iInf_le _ _

/-- The complement of the empty arrangement is all of `Proj Sym(W*)`.

Blueprint: `def:geo-projective`. -/
@[simp]
theorem complementOpen_eq_top [IsEmpty P] : complementOpen P = ⊤ := by
  rw [complementOpen_eq_iInf_basicOpen form ker_form, iInf_of_empty]

variable (P) [Nonempty P]

/-- For nonempty `P`, the complement of the hyperplanes of `P` in `Proj Sym(W*)` is the spectrum of
`O(U_P)`. In particular it is an affine scheme.

Blueprint: `def:projective`. -/
def complementOpenIso : (complementOpen P).toScheme ≅ Spec (.of P.ComplementRing) :=
  Proj.basicOpenIsoSpec (symmetricGrading k (Dual k W)) (formProduct P)
      (formProduct_mem_symmetricGrading P) (card_pos_of_nonempty P) ≪≫
    Scheme.Spec.mapIso (ComplementRing.awayEquiv (P := P) form ker_form).symm.toCommRingCatIso.op

/-- The ring `O(U_P)` is the ring of global functions on the complement in `Proj`. -/
def complementRingIso :
    .of P.ComplementRing ≅ Γ(Proj (symmetricGrading k (Dual k W)), complementOpen P) :=
  (ComplementRing.awayEquiv (P := P) form ker_form).symm.toCommRingCatIso ≪≫
    Proj.basicOpenIsoAway (symmetricGrading k (Dual k W)) (formProduct P)
      (formProduct_mem_symmetricGrading P) (card_pos_of_nonempty P)

/-- The open immersion `Spec O(U_P) → Proj Sym(W*)` of the complement. -/
def complementι : Spec (.of P.ComplementRing) ⟶ Proj (symmetricGrading k (Dual k W)) :=
  (complementOpenIso P).inv ≫ (complementOpen P).ι

instance : IsOpenImmersion (complementι P) :=
  IsOpenImmersion.comp _ _

/-- The open immersion of the complement is Mathlib's `Proj.awayι` for the chart `D₊(f)` of the
product `f` of equations, through the comparison of `O(U_P)` with `Away 𝒜 f`. -/
theorem complementι_eq_awayι :
    complementι P =
      Spec.map (CommRingCat.ofHom (ComplementRing.awayEquiv (P := P) form ker_form).toRingHom) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) (formProduct P)
          (formProduct_mem_symmetricGrading P) (card_pos_of_nonempty P) :=
  rfl

variable {P} in
/-- For equations `F` and `G` of the hyperplanes of `P`, the chart of `∏ H, F H`, composed with the
comparison of `O(U_P)` with its ring, factors through the chart of `(∏ H, F H) * (∏ H, G H)`. -/
theorem specMap_awayEquiv_comp_awayι (F G : P → Dual k W) (hF : ∀ H : P, LinearMap.ker (F H) = H)
    (hG : ∀ H : P, LinearMap.ker (G H) = H) :
    Spec.map (CommRingCat.ofHom (ComplementRing.awayEquiv F hF).toRingHom) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) (∏ H : P, coord (F H).toAffineMap)
          (prod_coord_mem_symmetricGrading F) (card_pos_of_nonempty P) =
      Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) (Submonoid.powers_le.2
          (mul_mem (prod_coord_mem_equationSubmonoid_cone F hF)
            (prod_coord_mem_equationSubmonoid_cone G hG))))) ≫
        Proj.awayι (symmetricGrading k (Dual k W))
          ((∏ H : P, coord (F H).toAffineMap) * ∏ H : P, coord (G H).toAffineMap)
          (SetLike.mul_mem_graded (prod_coord_mem_symmetricGrading F)
            (prod_coord_mem_symmetricGrading G))
          (Nat.add_pos_left (card_pos_of_nonempty P) _) := by
  rw [← Proj.SpecMap_awayMap_awayι (symmetricGrading k (Dual k W))
    (prod_coord_mem_symmetricGrading F) (card_pos_of_nonempty P)
    (prod_coord_mem_symmetricGrading G) rfl, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    mapId_comp_awayMap _ (prod_coord_mem_symmetricGrading F) (prod_coord_mem_symmetricGrading G)
      (powers_prod_coord_le F hF)]
  rfl

omit [Nonempty P] in
/-- The chart of a product of equations, composed with an inclusion of degree-zero fractions, only
depends on the product through the open subscheme it cuts out. -/
private theorem specMap_mapId_comp_awayι_congr {x y : CoordinateRing k W} (hxy : x = y) {m : ℕ}
    (hx : x ∈ symmetricGrading k (Dual k W) m) (hy : y ∈ symmetricGrading k (Dual k W) m)
    (hm : 0 < m) (hSx : Submonoid.powers x ≤ P.cone.equationSubmonoid)
    (hSy : Submonoid.powers y ≤ P.cone.equationSubmonoid) :
    Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hSx)) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) x hx hm =
      Spec.map (CommRingCat.ofHom (mapId (symmetricGrading k (Dual k W)) hSy)) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) y hy hm := by
  subst hxy
  rfl

/-- The open immersion of the complement does not depend on a choice of equations: for any
equations `F` of the hyperplanes of `P`, it is the chart `Proj.awayι` of `∏ H, F H`, through the
comparison of `O(U_P)` with its ring. So neither does `complementOpenIso`, since the open immersion
of `complementOpen P` is a monomorphism. -/
theorem complementι_eq_awayι_of_ker_eq (F : P → Dual k W)
    (hF : ∀ H : P, LinearMap.ker (F H) = H) :
    complementι P =
      Spec.map (CommRingCat.ofHom (ComplementRing.awayEquiv F hF).toRingHom) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) (∏ H : P, coord (F H).toAffineMap)
          (prod_coord_mem_symmetricGrading F) (card_pos_of_nonempty P) := by
  exact (specMap_awayEquiv_comp_awayι form F ker_form hF).trans
    ((specMap_mapId_comp_awayι_congr P (mul_comm _ _) _ _ _ _ _).trans
      (specMap_awayEquiv_comp_awayι F form hF ker_form).symm)

/-- The image of the open immersion `Spec O(U_P) → Proj Sym(W*)` is the complement of the
hyperplanes of `P`. -/
theorem opensRange_complementι : (complementι P).opensRange = complementOpen P :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (complementOpen P).opensRange_ι

end Proj

end ProjectiveArrangement

/-! ### In a basis -/

section Basis

attribute [local instance] MvPolynomial.gradedAlgebra

variable {κ : Type u} (b : Basis κ k (Dual k W))

/-- A basis of `W*` identifies `Sym(W*)` with the polynomial ring, as graded rings. -/
def symmetricGradingToMvPolynomial :
    symmetricGrading k (Dual k W) →+*ᵍ MvPolynomial.homogeneousSubmodule κ k where
  toRingHom := (SymmetricAlgebra.equivMvPolynomial b : _ →+* MvPolynomial κ k)
  map_mem {n x} hx := by
    rw [← map_equivMvPolynomial_symmetricGrading b n]
    exact Submodule.mem_map_of_mem hx

/-- A basis of `W*` identifies the polynomial ring with `Sym(W*)`, as graded rings. -/
def mvPolynomialToSymmetricGrading :
    MvPolynomial.homogeneousSubmodule κ k →+*ᵍ symmetricGrading k (Dual k W) where
  toRingHom := ((SymmetricAlgebra.equivMvPolynomial b).symm : _ →+* SymmetricAlgebra k (Dual k W))
  map_mem {n x} hx := by
    rw [← map_equivMvPolynomial_symmetricGrading b n] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy

/-- `Proj Sym(W*)`, the projectivization of `W`, is the projective space `Proj k[x_i]` of the
polynomial ring in the variables given by a basis of `W*`, with its usual grading by total degree.
So `complementOpen P` is the complement of hyperplanes in projective space in the usual sense. -/
def projIsoMvPolynomial :
    Proj (symmetricGrading k (Dual k W)) ≅ Proj (MvPolynomial.homogeneousSubmodule κ k) :=
  projIsoOfGraded (mvPolynomialToSymmetricGrading b) (symmetricGradingToMvPolynomial b)
    (GradedRingHom.ext fun x ↦ (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply x)
    (GradedRingHom.ext fun x ↦ (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply x)

end Basis

end OrlikSolomon
