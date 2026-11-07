/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Geometry.ProjectiveScheme
public import OrlikSolomon.Geometry.Schemes.Products

/-!
# Projective space and projective complements as schemes over the base

This file realizes `def:geo-projective` and `thm:geo-projective-geometry` of the geometric refactor
blueprint. For a vector space `W` over a field `k`, the projective space `ℙ(W) = Proj Sym(W*)` is a
scheme over `S = Spec k`, and the complement `U_P` of a projective arrangement `P` is its open
subscheme `complementOpen P`, the intersection of the charts `D₊(ℓ)` of the equations of the
hyperplanes of `P`. For nonempty `P`, the existing `complementOpenIso` becomes the canonical
comparison `s_P : U_P ≅ Spec O(U_P)` of `S`-schemes, so `U_P` is smooth and affine, and belongs to
every admissible domain.

## Main definitions

* `Geometric.projectiveSpace k W`: `ℙ(W) = Proj Sym(W*)`, with the grading by degree, over `S`.
* `Geometric.projectiveComplement P`: the complement `U_P`, an open subscheme of `ℙ(W)`, defined for
  every `P`. It is all of `ℙ(W)` for empty `P`, by `complementOpen_eq_top`.
* `Geometric.projectiveComplementIsoSpec P`: for nonempty `P`, the comparison
  `s_P : U_P ≅ Spec O(U_P)` of `S`-schemes, whose underlying isomorphism is `complementOpenIso P`.
* `Geometric.globalSectionsProjectiveComplementIso P`: `Γ(U_P, 𝒪) ≅ O(U_P)` as `k`-algebras.
* `Geometric.projectiveRatio`: the ratio `ℓ / ℓ'` of two equations, a global unit on `U_P`.
* `SmoothDomain.projectiveComplement D P`: `U_P` as an object of any admissible domain `D`, for
  nonempty `P` and finite-dimensional `W`, with `D.projectiveComplementIsoSpec P` the comparison
  with `D.spec (SmoothAlg.projectiveComplement P)`.
* `SmoothDomain.coneToProjectiveComplement D P`: the canonical projection `q : V_P → U_P`, from the
  spectrum `V_P` of the coordinate ring of the complement of the cone. It is `Spec` of the
  inclusion `projectiveToCone` of the fractions of degree zero.
* `SmoothDomain.projectiveDeconeIso D hℓ₀`, `SmoothDomain.coneIsoProdGm D hℓ₀`: for an equation `ℓ₀`
  of a hyperplane of `P`, the isomorphisms `U_P ≅ U_{decone_{ℓ₀} P}` and `V_P ≅ U_P ×_S 𝔾ₘ`.

## Main results

* `projectiveComplementIsoSpec_inv_left_comp_ι`: `s_P` does not depend on a choice of equations.
* `smooth_projectiveSpace_hom`, `isEmpty_projectiveSpace_left`: `ℙ(W)` is smooth over `S`, and it is
  empty when `W = 0`. So `U_P` is smooth for every `P`, including the empty arrangement.
* `coneIsoProdGm_hom_prodGmFst`, `coneIsoProdGm_hom_snd`: the first coordinate of `V_P ≅ U_P ×_S 𝔾ₘ`
  is the canonical projection `q`, and the second is `ℓ₀`.
* `map_coneToProjectiveComplement_projectiveRatio`: `ℓ = ℓ₀ q^*(ℓ / ℓ₀)` on `V_P`.
* `map_projectiveDeconeIso_complementUnit`: the decone isomorphism identifies `ℓ / ℓ₀` with the
  restriction of `ℓ` to the slice `ℓ₀ = 1`.

## Implementation notes

The complements `U_{decone_{ℓ₀} P}` and `V_P = U_{cone P}` of affine arrangements are the subject of
`Geometry/Schemes/Complement` (#111), which does not exist yet. Here they are the spectra
`D.spec (SmoothAlg.complement _)` of the existing coordinate rings, and the blueprint's isomorphisms
are obtained by composing with that module's comparison `s_𝒜` once it lands.

The structure theorem on `U_P` will be the existing one composed with pullback along
`D.projectiveComplementIsoSpec P`; `map_projectiveComplementIsoSpec_ratioUnit` and
`coneToProjectiveComplement_comp_projectiveComplementIsoSpec_hom` identify the existing ratio units
and the existing `projectiveToCone` on the two sides of `s_P`.

Named objects are `@[implicit_reducible] def`s and equations between objects are not `simp` lemmas,
as explained in `Geometry/Schemes/Basic`. No `k`-point of any scheme is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open Module HomogeneousLocalization
open scoped LaurentPolynomial

universe u

namespace OrlikSolomon.Geometric

open ProjectiveArrangement ProjectiveArrangement.ComplementRing CoordinateRing

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]

/-! ### Projective space -/

variable (k W) in
/-- The structure morphism `Proj Sym(W*) → Spec k`: Mathlib's `Proj.toSpecZero`, to the spectrum
of the degree-zero part of `Sym(W*)`, followed by `Spec` of the inclusion of the scalars. -/
def projToSpec : Proj (symmetricGrading k (Dual k W)) ⟶ Spec (.of k) :=
  Proj.toSpecZero _ ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (symmetricGrading k (Dual k W) 0)))

variable (k W) in
/-- The projective space `ℙ(W) = Proj Sym(W*)` of lines in `W`, with the grading of `Sym(W*)` by
degree, as a scheme over `S = Spec k`. In a basis of `W*` it is `Proj k[x_i]`
(`projIsoMvPolynomial`).

Blueprint: `def:geo-projective`. -/
@[implicit_reducible]
def projectiveSpace : Over (Spec (.of k)) := Over.mk (projToSpec k W)

lemma projectiveSpace_left : (projectiveSpace k W).left = Proj (symmetricGrading k (Dual k W)) :=
  rfl

lemma projectiveSpace_hom : (projectiveSpace k W).hom = projToSpec k W := rfl

/-- The chart `D₊(f) ≅ Spec (Sym(W*)_f)₀` of `ℙ(W)` is a morphism over `S`. -/
@[reassoc]
lemma awayι_projToSpec {f : CoordinateRing k W} {m : ℕ} (hf : f ∈ symmetricGrading k (Dual k W) m)
    (hm : 0 < m) :
    Proj.awayι _ f hf hm ≫ projToSpec k W =
      Spec.map (CommRingCat.ofHom ((fromZeroRingHom _ _).comp
        (algebraMap k (symmetricGrading k (Dual k W) 0)))) := by
  rw [projToSpec, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-! ### The complement -/

section Complement

variable (P : ProjectiveArrangement k W)

/-- The complement `U_P` of a projective arrangement, as a scheme over `S = Spec k`: the open
subscheme `complementOpen P` of `ℙ(W)` of the points on no hyperplane of `P`. It is the intersection
of the charts `D₊(ℓ)` of all equations `ℓ` of hyperplanes of `P` (`complementOpen_eq_iInf`), which
depend only on the hyperplanes (`basicOpen_coord_eq_of_ker_eq`). It is defined for every `P`, and
for empty `P` it is all of `ℙ(W)` (`complementOpen_eq_top`).

Blueprint: `def:geo-projective`. -/
@[implicit_reducible]
def projectiveComplement : Over (Spec (.of k)) :=
  Over.mk ((complementOpen P).ι ≫ projToSpec k W)

lemma projectiveComplement_left : (projectiveComplement P).left = (complementOpen P).toScheme :=
  rfl

lemma projectiveComplement_hom :
    (projectiveComplement P).hom = (complementOpen P).ι ≫ (projectiveSpace k W).hom :=
  rfl

/-- The open immersion `U_P → ℙ(W)`, over `S`.

Blueprint: `def:geo-projective`. -/
def projectiveComplementι : projectiveComplement P ⟶ projectiveSpace k W :=
  Over.homMk (complementOpen P).ι rfl

@[simp] lemma projectiveComplementι_left :
    (projectiveComplementι P).left = (complementOpen P).ι :=
  rfl

instance : IsOpenImmersion (projectiveComplementι P).left :=
  inferInstanceAs (IsOpenImmersion (complementOpen P).ι)

/-- The image of `U_P → ℙ(W)` is `complementOpen P`. -/
lemma opensRange_projectiveComplementι :
    (projectiveComplementι P).left.opensRange = complementOpen P :=
  (complementOpen P).opensRange_ι

end Complement

/-! ### The comparison `s_P` -/

section Comparison

variable (P : ProjectiveArrangement k W) [Nonempty P]

/-- The open immersion `Spec O(U_P) → ℙ(W)` is a morphism over `S`. -/
@[reassoc]
lemma complementι_projToSpec :
    complementι P ≫ projToSpec k W =
      Spec.map (CommRingCat.ofHom (algebraMap k P.ComplementRing)) := by
  rw [complementι_eq_awayι, Category.assoc, awayι_projToSpec, ← Spec.map_comp]
  rfl

/-- The existing comparison `complementOpenIso` is a morphism over `S`: it is the identity on the
scalars. -/
@[reassoc]
lemma complementOpenIso_hom_specMap :
    (complementOpenIso P).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.ComplementRing)) =
      (complementOpen P).ι ≫ projToSpec k W := by
  rw [← complementι_projToSpec, complementι, Category.assoc, Iso.hom_inv_id_assoc]

/-- The canonical comparison `s_P : U_P ≅ Spec O(U_P)` of `S`-schemes, for nonempty `P`: the
existing `complementOpenIso`, with its certificate `complementOpenIso_hom_specMap` that it is a
morphism over `S`. It does not depend on a choice of equations
(`projectiveComplementIsoSpec_inv_left_comp_ι`).

Blueprint: `thm:geo-projective-geometry`. -/
def projectiveComplementIsoSpec :
    projectiveComplement P ≅ spec (CommAlgCat.of k P.ComplementRing) :=
  Over.isoMk (complementOpenIso P) (complementOpenIso_hom_specMap P)

@[simp] lemma projectiveComplementIsoSpec_hom_left :
    (projectiveComplementIsoSpec P).hom.left = (complementOpenIso P).hom :=
  rfl

@[simp] lemma projectiveComplementIsoSpec_inv_left :
    (projectiveComplementIsoSpec P).inv.left = (complementOpenIso P).inv :=
  rfl

/-- `s_P` does not depend on a choice of equations: for any equations `F` of the hyperplanes of `P`,
the inverse of `s_P` followed by the open immersion into `ℙ(W)` is the chart `Proj.awayι` of
`∏ H, F H`, through the comparison `ComplementRing.awayEquiv F` of `O(U_P)` with its ring. Since the
open immersion is a monomorphism, this determines `s_P`.

Blueprint: `thm:geo-projective-geometry`. -/
lemma projectiveComplementIsoSpec_inv_left_comp_ι (F : P → Dual k W)
    (hF : ∀ H : P, LinearMap.ker (F H) = H) :
    (projectiveComplementIsoSpec P).inv.left ≫ (complementOpen P).ι =
      Spec.map (CommRingCat.ofHom (awayEquiv F hF).toRingHom) ≫
        Proj.awayι (symmetricGrading k (Dual k W)) (∏ H : P, coord (F H).toAffineMap)
          (prod_coord_mem_symmetricGrading F) (card_pos_of_nonempty P) :=
  complementι_eq_awayι_of_ker_eq P F hF

/-- For nonempty `P`, the complement `U_P` is affine.

Blueprint: `thm:geo-projective-geometry`. -/
instance isAffine_projectiveComplement_left : IsAffine (projectiveComplement P).left :=
  .of_isIso (projectiveComplementIsoSpec P).hom.left

/-- For nonempty `P` and finite-dimensional `W`, the complement `U_P` is smooth over `S`, since
`O(U_P)` is a smooth `k`-algebra. `smooth_projectiveComplement_hom` extends this to every `P`. -/
lemma smooth_projectiveComplement_hom_of_nonempty [FiniteDimensional k W] :
    Smooth (projectiveComplement P).hom := by
  rw [← Over.w (projectiveComplementIsoSpec P).hom]
  infer_instance

/-- The ring of global functions on `U_P` is `O(U_P)`, as a `k`-algebra, through `s_P`. -/
def globalSectionsProjectiveComplementIso :
    globalSections (projectiveComplement P) ≅ CommAlgCat.of k P.ComplementRing :=
  ((globalSectionsFunctor k).mapIso (projectiveComplementIsoSpec P).op).symm ≪≫
    globalSectionsSpecIso _

@[simp] lemma globalSectionsProjectiveComplementIso_inv_apply (x : P.ComplementRing) :
    (globalSectionsProjectiveComplementIso P).inv x =
      (complementOpenIso P).hom.appTop ((Scheme.ΓSpecIso (.of P.ComplementRing)).inv x) :=
  rfl

@[simp] lemma globalSectionsProjectiveComplementIso_hom_apply
    (x : globalSections (projectiveComplement P)) :
    (globalSectionsProjectiveComplementIso P).hom x =
      (Scheme.ΓSpecIso (.of P.ComplementRing)).hom ((complementOpenIso P).inv.appTop x) :=
  rfl

end Comparison

/-! ### Ratios of equations -/

section Ratio

variable {P : ProjectiveArrangement k W} [Nonempty P] {ℓ ℓ' ℓ'' : Dual k W}

/-- The ratio `ℓ / ℓ'` of two equations of hyperplanes of `P`, a global unit on `U_P`: the unit
`ratioUnit` of `O(U_P)`, through `s_P`. It involves no hyperplane at infinity.

Blueprint: `thm:geo-projective-geometry`. -/
def projectiveRatio (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    Γ((projectiveComplement P).left, ⊤)ˣ :=
  Units.map ((globalSectionsProjectiveComplementIso P).inv.hom :
    P.ComplementRing →* Γ((projectiveComplement P).left, ⊤)) (ratioUnit hℓ hℓ')

lemma coe_projectiveRatio (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    (projectiveRatio hℓ hℓ' : Γ((projectiveComplement P).left, ⊤)) =
      (globalSectionsProjectiveComplementIso P).inv (ratio ℓ hℓ') :=
  rfl

/-- The global unit `ℓ / ℓ'` on `U_P` is the pullback along `s_P` of the existing unit `ratioUnit`
of `O(U_P)`, as a function on `Spec O(U_P)`. This is how the existing ratio formula of the
projective structure theorem transports to `U_P`.

Blueprint: `thm:geo-projective-geometry`. -/
lemma map_projectiveComplementIsoSpec_ratioUnit (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ' : LinearMap.ker ℓ' ∈ P) :
    Units.map (projectiveComplementIsoSpec P).hom.left.appTop.hom
        (Units.map (Scheme.ΓSpecIso (.of P.ComplementRing)).inv.hom (ratioUnit hℓ hℓ')) =
      projectiveRatio hℓ hℓ' :=
  rfl

@[simp] lemma projectiveRatio_self (hℓ : LinearMap.ker ℓ ∈ P) : projectiveRatio hℓ hℓ = 1 := by
  rw [projectiveRatio, ratioUnit_self, map_one]

@[simp] lemma projectiveRatio_inv (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    (projectiveRatio hℓ hℓ')⁻¹ = projectiveRatio hℓ' hℓ := by
  rw [projectiveRatio, ← map_inv, ratioUnit_inv, projectiveRatio]

lemma projectiveRatio_mul (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P)
    (hℓ'' : LinearMap.ker ℓ'' ∈ P) :
    projectiveRatio hℓ hℓ' * projectiveRatio hℓ' hℓ'' = projectiveRatio hℓ hℓ'' := by
  rw [projectiveRatio, projectiveRatio, ← map_mul, ratioUnit_mul_ratioUnit, projectiveRatio]

/-- Scaling the numerator of a ratio by a nonzero constant multiplies it by that constant. With
`projectiveRatio_inv`, changing either equation changes the ratio by a constant. -/
lemma coe_projectiveRatio_smul {c : kˣ} (hcℓ : LinearMap.ker ((c : k) • ℓ) ∈ P)
    (hℓ : LinearMap.ker ℓ ∈ P) (hℓ' : LinearMap.ker ℓ' ∈ P) :
    (projectiveRatio hcℓ hℓ' : Γ((projectiveComplement P).left, ⊤)) =
      algebraMap k (globalSections (projectiveComplement P)) (c : k) * projectiveRatio hℓ hℓ' := by
  rw [coe_projectiveRatio, ← coe_ratioUnit, coe_ratioUnit_smul hcℓ hℓ hℓ', map_mul, AlgHom.commutes,
    coe_ratioUnit, coe_projectiveRatio]

end Ratio

/-! ### Projective space is smooth -/

section Smooth

/-- `ℙ(W)` is covered by the charts `D₊(ℓ)` of the nonzero linear forms `ℓ` on `W`. -/
theorem iSup_basicOpen_coord_eq_top :
    ⨆ ℓ : {ℓ : Dual k W // ℓ ≠ 0},
      Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.1.toAffineMap) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun ℓ ↦ ⟨1, coord_toAffineMap_mem ℓ.1⟩) ?_
  rw [eq_top_iff]
  rintro x -
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem _
      (⟨_, algebraMap_mem_symmetricGrading r⟩ : symmetricGrading k (Dual k W) 0)
  | ι ξ =>
    by_cases hξ : ξ = 0
    · rw [hξ, map_zero]
      exact Subalgebra.zero_mem _
    · exact Algebra.subset_adjoin ⟨⟨ξ, hξ⟩, coord_toAffineMap ξ⟩
  | mul a b ha hb => exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb => exact Subalgebra.add_mem _ ha hb

/-- If `W = 0`, then `ℙ(W)` is empty: `Sym(W*)` is `k`, with no element of positive degree.

Blueprint: `def:geo-projective`. -/
instance isEmpty_projectiveSpace_left [Subsingleton W] : IsEmpty (projectiveSpace k W).left := by
  have : IsEmpty {ℓ : Dual k W // ℓ ≠ 0} := ⟨fun ℓ ↦ ℓ.2 (Subsingleton.elim _ _)⟩
  have h := iSup_basicOpen_coord_eq_top (k := k) (W := W)
  rw [iSup_of_empty] at h
  exact ⟨fun x ↦ (show x ∈ (⊥ : (Proj (symmetricGrading k (Dual k W))).Opens) from h ▸ trivial)⟩

/-- The chart `D₊(ℓ)` of a nonzero linear form is the complement of its hyperplane. -/
lemma complementOpen_ofForms_singleton {ℓ : Dual k W} (hℓ : ℓ ≠ 0) :
    complementOpen (ofForms {ℓ} (by simpa using hℓ)) =
      Proj.basicOpen (symmetricGrading k (Dual k W)) (coord ℓ.toAffineMap) := by
  have : Nonempty (ofForms {ℓ} (by simpa using hℓ)) :=
    nonempty_of_ker_mem (ker_mem_ofForms (Finset.mem_singleton_self ℓ))
  rw [complementOpen_eq_iInf_basicOpen (fun _ ↦ ℓ) fun H ↦ ?_, iInf_const]
  obtain ⟨ℓ', hℓ', h⟩ := mem_ofForms.1 H.2
  rw [Finset.mem_singleton.1 hℓ'] at h
  exact h

variable [FiniteDimensional k W]

/-- For finite-dimensional `W`, the projective space `ℙ(W)` is smooth over `S`: it is covered by the
charts `D₊(ℓ)`, each the complement of one hyperplane, which is smooth.

Blueprint: `def:geo-projective`. -/
instance smooth_projectiveSpace_hom : Smooth (projectiveSpace k W).hom := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top _ iSup_basicOpen_coord_eq_top fun ℓ ↦ ?_
  have := smooth_projectiveComplement_hom_of_nonempty (ofForms {ℓ.1} (by simpa using ℓ.2))
    (nonempty := nonempty_of_ker_mem (ker_mem_ofForms (Finset.mem_singleton_self ℓ.1)))
  rwa [projectiveComplement_hom, complementOpen_ofForms_singleton ℓ.2] at this

/-- The complement `U_P` is smooth over `S` for every `P`, including the empty arrangement, for
which it is `ℙ(W)`.

Blueprint: `def:geo-projective`, `thm:geo-projective-geometry`. -/
instance smooth_projectiveComplement_hom (P : ProjectiveArrangement k W) :
    Smooth (projectiveComplement P).hom :=
  inferInstanceAs (Smooth ((complementOpen P).ι ≫ projToSpec k W))

end Smooth

/-! ### In a domain -/

namespace SmoothDomain

variable (D : SmoothDomain k) [FiniteDimensional k W] (P : ProjectiveArrangement k W) [Nonempty P]
variable {ℓ ℓ₀ : Dual k W}

/-- The complement `U_P` of a nonempty projective arrangement, as an object of any admissible
domain `D`. It is smooth and affine, so its membership needs no hypothesis.

Blueprint: `thm:geo-projective-geometry`. -/
@[implicit_reducible]
def projectiveComplement : D.Obj := D.ofAffine (Geometric.projectiveComplement P)

lemma projectiveComplement_obj :
    (D.projectiveComplement P).obj = Geometric.projectiveComplement P :=
  rfl

/-- The comparison `s_P : U_P ≅ Spec O(U_P)`, in a domain `D`. The structure theorem on `U_P` is
the existing one, on `D.spec (SmoothAlg.projectiveComplement P)`, composed with pullback along
`s_P`.

Blueprint: `thm:geo-projective-geometry`. -/
def projectiveComplementIsoSpec :
    D.projectiveComplement P ≅ D.spec (SmoothAlg.projectiveComplement P) :=
  ObjectProperty.isoMk _ (Geometric.projectiveComplementIsoSpec P)

@[simp] lemma projectiveComplementIsoSpec_hom_hom :
    (D.projectiveComplementIsoSpec P).hom.hom = (Geometric.projectiveComplementIsoSpec P).hom :=
  rfl

@[simp] lemma projectiveComplementIsoSpec_inv_hom :
    (D.projectiveComplementIsoSpec P).inv.hom = (Geometric.projectiveComplementIsoSpec P).inv :=
  rfl

/-! #### The cone -/

/-- The canonical projection `q : V_P → U_P` from the complement of the cone, here the spectrum of
its coordinate ring: `Spec` of the inclusion `projectiveToCone` of the fractions of degree zero,
followed by `s_P⁻¹`. It involves no hyperplane at infinity.

Blueprint: `thm:geo-projective-geometry`. -/
def coneToProjectiveComplement :
    D.spec (SmoothAlg.complement P.cone) ⟶ D.projectiveComplement P :=
  (D.specFunctor.map (SmoothAlg.projectiveToCone P)).unop ≫ (D.projectiveComplementIsoSpec P).inv

/-- Under `s_P`, the projection `q : V_P → U_P` is `Spec` of `projectiveToCone`. This is the square
that makes a structure theorem on `U_P` commute with pullback to the cone.

Blueprint: `thm:geo-projective-geometry`. -/
@[reassoc (attr := simp)]
lemma coneToProjectiveComplement_comp_projectiveComplementIsoSpec_hom :
    D.coneToProjectiveComplement P ≫ (D.projectiveComplementIsoSpec P).hom =
      (D.specFunctor.map (SmoothAlg.projectiveToCone P)).unop := by
  rw [coneToProjectiveComplement, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {P} in
/-- The isomorphism `V_P ≅ U_P ×_S 𝔾ₘ`, for an equation `ℓ₀` of a hyperplane of `P`: `Spec` of the
existing `coneIso`, then `specLaurentIso`, then `s_P⁻¹ × 𝔾ₘ`. Its first coordinate is the
canonical projection (`coneIsoProdGm_hom_prodGmFst`) and its second is `ℓ₀`
(`coneIsoProdGm_hom_snd`), so it depends on `ℓ₀`.

Blueprint: `thm:geo-projective-geometry`. -/
def coneIsoProdGm (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    D.spec (SmoothAlg.complement P.cone) ≅ D.prodGm (D.projectiveComplement P) :=
  (D.specFunctor.mapIso (SmoothAlg.coneIso hℓ₀)).unop.symm ≪≫
    D.specLaurentIso (SmoothAlg.projectiveComplement P) ≪≫
      ObjectProperty.isoMk _
        (whiskerRightIso (Geometric.projectiveComplementIsoSpec P).symm (Geometric.gm k))

variable {P} in
lemma coneIsoProdGm_hom_hom (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (D.coneIsoProdGm hℓ₀).hom.hom =
      specMap (SmoothAlg.coneIso hℓ₀).inv.hom ≫
        (Geometric.specLaurentIso (SmoothAlg.projectiveComplement P)).hom ≫
          ((Geometric.projectiveComplementIsoSpec P).inv ▷ Geometric.gm k) :=
  rfl

variable {P} in
/-- The first coordinate of `V_P ≅ U_P ×_S 𝔾ₘ` is the canonical projection `q`.

Blueprint: `thm:geo-projective-geometry`. -/
@[reassoc (attr := simp)]
lemma coneIsoProdGm_hom_prodGmFst (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (D.coneIsoProdGm hℓ₀).hom ≫ D.prodGmFst (D.projectiveComplement P) =
      D.coneToProjectiveComplement P := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom, coneIsoProdGm_hom_hom, prodGmFst_hom,
    Category.assoc, Category.assoc, whiskerRight_fst, specLaurentIso_hom_fst_assoc,
    ← specMap_comp_assoc, coneToProjectiveComplement, ObjectProperty.FullSubcategory.comp_hom]
  congr 2
  rw [← ObjectProperty.FullSubcategory.comp_hom, SmoothAlg.laurentC_comp_coneIso_inv]
  rfl

variable {P} in
/-- The second coordinate of `V_P ≅ U_P ×_S 𝔾ₘ` is the map of the unit `ℓ₀` of `O(V_P)`.

Blueprint: `thm:geo-projective-geometry`. -/
lemma coneIsoProdGm_hom_snd (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (D.coneIsoProdGm hℓ₀).hom.hom ≫ snd _ _ =
      unitsEquivHomGm _ (Units.map (Scheme.ΓSpecIso (.of (SmoothAlg.complement P.cone))).inv.hom
        (SmoothAlg.complementUnit P.cone ℓ₀.toAffineMap (cone_covers hℓ₀))) := by
  rw [coneIsoProdGm_hom_hom, Category.assoc, Category.assoc, whiskerRight_snd,
    specLaurentIso_hom_snd, ← unitsEquivHomGm_comp]
  congr 1
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [specMap_left_appTop_ΓSpecIso_inv]
  exact congrArg _ (congrArg Units.val (SmoothAlg.mapUnits_coneIso_inv_laurentT hℓ₀))

variable {P} in
/-- On `V_P`, an equation `ℓ` is `ℓ₀ q^*(ℓ / ℓ₀)`, for every equation `ℓ₀` of a hyperplane of `P`,
where `q : V_P → U_P` is the canonical projection.

Blueprint: `thm:geo-projective-geometry`. -/
lemma map_coneToProjectiveComplement_projectiveRatio (hℓ : LinearMap.ker ℓ ∈ P)
    (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    Units.map (Scheme.ΓSpecIso (.of (SmoothAlg.complement P.cone))).inv.hom
        (SmoothAlg.complementUnit P.cone ℓ.toAffineMap (cone_covers hℓ)) =
      Units.map (Scheme.ΓSpecIso (.of (SmoothAlg.complement P.cone))).inv.hom
          (SmoothAlg.complementUnit P.cone ℓ₀.toAffineMap (cone_covers hℓ₀)) *
        Units.map (D.coneToProjectiveComplement P).hom.left.appTop.hom
          (projectiveRatio hℓ hℓ₀) := by
  ext
  simp only [Units.coe_map, Units.val_mul, MonoidHom.coe_coe]
  rw [coe_projectiveRatio, globalSectionsProjectiveComplementIso_inv_apply,
    ← projectiveComplementIsoSpec_hom_left, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Over.comp_left, ← projectiveComplementIsoSpec_hom_hom D,
    ← ObjectProperty.FullSubcategory.comp_hom,
    coneToProjectiveComplement_comp_projectiveComplementIsoSpec_hom]
  change _ = _ * (specMap (SmoothAlg.projectiveToCone P).hom).left.appTop _
  rw [specMap_left_appTop_ΓSpecIso_inv, ← map_mul, SmoothAlg.coe_complementUnit,
    SmoothAlg.coe_complementUnit, mul_comm]
  congr 1
  exact (toCone_ratio_mul ℓ hℓ₀).symm

/-! #### The decone -/

variable {P} in
/-- The isomorphism `U_P ≅ U_{decone_{ℓ₀} P}` with the complement of the decone in the slice
`ℓ₀ = 1`, here the spectrum of its coordinate ring, for an equation `ℓ₀` of a hyperplane of `P`:
`s_P` followed by `Spec` of the existing `deconeIso`, which restricts functions to the slice.

Blueprint: `thm:geo-projective-geometry`. -/
def projectiveDeconeIso (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    D.projectiveComplement P ≅ D.spec (SmoothAlg.complement (P.decone ℓ₀)) :=
  D.projectiveComplementIsoSpec P ≪≫ (D.specFunctor.mapIso (SmoothAlg.deconeIso hℓ₀)).unop.symm

variable {P} in
lemma projectiveDeconeIso_hom (hℓ₀ : LinearMap.ker ℓ₀ ∈ P) :
    (D.projectiveDeconeIso hℓ₀).hom =
      (D.projectiveComplementIsoSpec P).hom ≫
        (D.specFunctor.map (SmoothAlg.deconeIso hℓ₀).inv).unop :=
  rfl

variable {P} in
/-- The decone isomorphism pulls back the restriction of an equation `ℓ` to the slice `ℓ₀ = 1` to
the ratio `ℓ / ℓ₀`.

Blueprint: `thm:geo-projective-geometry`. -/
lemma map_projectiveDeconeIso_complementUnit (hℓ₀ : LinearMap.ker ℓ₀ ∈ P)
    (hℓ : LinearMap.ker ℓ ∈ P) :
    Units.map (D.projectiveDeconeIso hℓ₀).hom.hom.left.appTop.hom
        (Units.map (Scheme.ΓSpecIso (.of (SmoothAlg.complement (P.decone ℓ₀)))).inv.hom
          (SmoothAlg.complementUnit (P.decone ℓ₀) (ℓ.toAffineMap.comp (chart (slice ℓ₀)))
            (decone_covers hℓ₀ hℓ))) =
      projectiveRatio hℓ hℓ₀ := by
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [projectiveDeconeIso_hom, ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change (D.projectiveComplementIsoSpec P).hom.hom.left.appTop
    ((specMap (SmoothAlg.deconeIso hℓ₀).inv.hom).left.appTop _) = _
  rw [specMap_left_appTop_ΓSpecIso_inv, coe_projectiveRatio,
    globalSectionsProjectiveComplementIso_inv_apply, projectiveComplementIsoSpec_hom_hom,
    projectiveComplementIsoSpec_hom_left]
  congr 2
  rw [← SmoothAlg.mapUnits_deconeIso_hom_projectiveRatioUnit_self hℓ₀ hℓ, SmoothAlg.coe_mapUnits,
    ← CategoryTheory.comp_apply, Iso.hom_inv_id, CategoryTheory.id_apply]
  rfl

end SmoothDomain

end OrlikSolomon.Geometric
