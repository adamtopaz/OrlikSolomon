/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import OrlikSolomon.Geometry.CoordinateRing
public import OrlikSolomon.Geometry.Schemes.PrincipalPair.Certificates
import OrlikSolomon.Geometry.Deletion

/-!
# Coordinate-free affine space and hyperplane schemes

This file realizes `def:geo-affine-space` of the geometric refactor blueprint. For a vector space
`V` over a field `k`, the affine space `𝔸_V` is `Spec Sym(V*)`, built from the existing coordinate
ring `CoordinateRing k V`, as a scheme over `S = Spec k`. An affine function `f` gives the global
function `f̃ = ι(f_lin) + f(0)`, an affine map `a : W → V` gives the morphism `𝔸_a : 𝔸_W → 𝔸_V`,
and a hyperplane `H` gives the closed subscheme `𝐇 = Spec (Sym(V*) ⧸ I_H)`, where `I_H` is generated
by the functions of **all** equations of `H`.

## Main definitions

* `Geometric.affineSpace k V`: the `S`-scheme `𝔸_V = Spec Sym(V*)`.
* `Geometric.affineSpaceCoord f`: the global function `f̃` of an affine function `f`.
* `Geometric.affineSpaceMap k a`: the morphism `𝔸_a : 𝔸_W → 𝔸_V` of an affine map `a : W → V`.
* `Geometric.hyperplaneIdeal H`, `Geometric.hyperplaneScheme H`, `Geometric.hyperplaneι H`: the
  ideal `I_H`, the scheme `𝐇` and its closed immersion into `𝔸_V`.
* `Geometric.hyperplaneSchemeIso hH`: `𝔸_{H.direction} ≅ 𝐇` for a hyperplane `H`, under which the
  closed immersion is `𝔸_{chart H}`.
* `Geometric.affineSpaceIsoAffineSpace b`: for a basis `b` of `V*`, the isomorphism of `𝔸_V` with
  Mathlib's indexed affine space `𝔸(ι; Spec k)`, under which the coordinates are the `b i`.
* `SmoothDomain.affineSpace D V`: `𝔸_V` as an object of any admissible domain.

## Main results

* `affineSpaceMap_appTop_affineSpaceCoord`, `affineSpaceMap_id`, `affineSpaceMap_comp`: `𝔸_a` pulls
  back `f̃` to `(f ∘ a)~`, and `a ↦ 𝔸_a` is functorial.
* `hyperplaneIdeal_eq_span`, `ker_hyperplaneι`: `I_H = (f̃)` for every equation `f` of `H`, so the
  kernel of `𝐇 → 𝔸_V` is `f̃ 𝒪` for every equation; `𝐇` does not depend on an equation.
* `smooth_hyperplaneScheme_hom`: `𝐇` is smooth for a hyperplane `H` of a finite-dimensional `V`.

## Implementation notes

The definitions use no basis and no `k`-point. A basis appears only in the comparison with Mathlib's
`AffineSpace`, and smoothness of `𝔸_V` is the existing instance
`CoordinateRing.smooth_coordinateRing`.
As elsewhere in `Geometry/Schemes`, named objects are `@[implicit_reducible] def`s, except the
object `SmoothDomain.affineSpace` of a domain, which is `@[instance_reducible]` (see
`Geometry/Schemes/Basic`), and equations between objects are not `simp` lemmas.

For an affine subspace `H` that is not a hyperplane, `I_H` is the zero ideal and `𝐇` is all of
`𝔸_V`; no result is stated for such `H`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry Module

universe u

namespace OrlikSolomon.Geometric

open CoordinateRing

/-- The function on `Spec A` of a constant `c` is the constant `c` of `Γ(Spec A)`. -/
lemma ΓSpecIso_inv_algebraMap {k : Type u} [CommRing k] (A : CommAlgCat.{u} k) (c : k) :
    (Scheme.ΓSpecIso (.of A)).inv (algebraMap k A c) = algebraMap k (globalSections (spec A)) c :=
  (globalSectionsSpecIso A).inv.hom.commutes c

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]
variable {W : Type u} [AddCommGroup W] [Module k W] {U : Type u} [AddCommGroup U] [Module k U]

/-! ### The affine space -/

variable (k V) in
/-- The affine space `𝔸_V = Spec Sym(V*)` of a vector space `V`, as a scheme over `S = Spec k`. It
is the spectrum of the existing coordinate ring `CoordinateRing k V`, and involves no basis.

Blueprint: `def:geo-affine-space`. -/
@[implicit_reducible]
def affineSpace : Over (Spec (.of k)) := spec (CommAlgCat.of k (CoordinateRing k V))

lemma affineSpace_eq : affineSpace k V = spec (CommAlgCat.of k (CoordinateRing k V)) := rfl

lemma affineSpace_left : (affineSpace k V).left = Spec (.of (CoordinateRing k V)) := rfl

instance : IsAffine (affineSpace k V).left := inferInstanceAs (IsAffine (Spec _))

/-- The affine space of a finite-dimensional vector space is smooth over `S`.

Blueprint: `def:geo-affine-space`. -/
instance [FiniteDimensional k V] : Smooth (affineSpace k V).hom := smooth_spec_hom _

/-- The global function `f̃ = ι(f_lin) + f(0)` on `𝔸_V` of an affine function `f : V → k`.

Blueprint: `def:geo-affine-space`. -/
def affineSpaceCoord (f : V →ᵃ[k] k) : Γ((affineSpace k V).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (CoordinateRing k V))).inv (coord f)

lemma affineSpaceCoord_eq (f : V →ᵃ[k] k) :
    affineSpaceCoord f = (Scheme.ΓSpecIso (.of (CoordinateRing k V))).inv (coord f) := rfl

/-- The function of a constant is that constant. -/
lemma affineSpaceCoord_const (c : k) :
    affineSpaceCoord (AffineMap.const k V c) =
      algebraMap k (globalSections (affineSpace k V)) c := by
  rw [affineSpaceCoord, coord_const]
  exact ΓSpecIso_inv_algebraMap (CommAlgCat.of k (CoordinateRing k V)) c

/-- Scaling an affine function by `c` multiplies its function by the function of the constant `c`,
which is the constant `c` of `Γ(𝔸_V)` by `affineSpaceCoord_const`. -/
lemma affineSpaceCoord_smul (c : k) (f : V →ᵃ[k] k) :
    affineSpaceCoord (c • f) = affineSpaceCoord (AffineMap.const k V c) * affineSpaceCoord f := by
  rw [affineSpaceCoord, affineSpaceCoord, affineSpaceCoord, coord_smul_eq_mul, coord_const, map_mul]

/-- Two morphisms into `𝔸_V` agree when they pull back the function of every affine function to the
same global function. No `k`-point is involved. -/
lemma hom_ext_affineSpace {X : Over (Spec (.of k))} {g₁ g₂ : X ⟶ affineSpace k V}
    (h : ∀ f : V →ᵃ[k] k,
      g₁.left.appTop (affineSpaceCoord f) = g₂.left.appTop (affineSpaceCoord f)) :
    g₁ = g₂ :=
  (specHomEquiv X _).injective (CommAlgCat.hom_ext (CoordinateRing.algHom_ext h))

/-! ### Affine maps -/

variable (k) in
/-- The morphism `𝔸_a : 𝔸_W → 𝔸_V` of an affine map `a : W → V`: `Spec` of the existing pullback
`CoordinateRing.pull a`. It pulls back `f̃` to `(f ∘ a)~`, by
`affineSpaceMap_appTop_affineSpaceCoord`.

Blueprint: `def:geo-affine-space`. -/
def affineSpaceMap (a : W →ᵃ[k] V) : affineSpace k W ⟶ affineSpace k V :=
  specMap (CommAlgCat.ofHom (pull a))

lemma affineSpaceMap_eq (a : W →ᵃ[k] V) :
    affineSpaceMap k a = specMap (CommAlgCat.ofHom (pull a)) := rfl

/-- `𝔸_a` pulls back the function of `f` to the function of `f ∘ a`.

Blueprint: `def:geo-affine-space`. -/
@[simp] lemma affineSpaceMap_appTop_affineSpaceCoord (a : W →ᵃ[k] V) (f : V →ᵃ[k] k) :
    (affineSpaceMap k a).left.appTop (affineSpaceCoord f) = affineSpaceCoord (f.comp a) := by
  rw [affineSpaceMap, affineSpaceCoord, specMap_left_appTop_ΓSpecIso_inv]
  exact congrArg _ (pull_coord a f)

@[simp] lemma affineSpaceMap_id : affineSpaceMap k (AffineMap.id k V) = 𝟙 (affineSpace k V) := by
  rw [affineSpaceMap, pull_id, CommAlgCat.ofHom_id]
  exact specMap_id _

@[reassoc]
lemma affineSpaceMap_comp (a : W →ᵃ[k] V) (b : U →ᵃ[k] W) :
    affineSpaceMap k (a.comp b) = affineSpaceMap k b ≫ affineSpaceMap k a := by
  rw [affineSpaceMap, pull_comp, CommAlgCat.ofHom_comp, specMap_comp]
  rfl

/-! ### Hyperplane schemes -/

section Hyperplane

variable {H : AffineSubspace k V} {f : V →ᵃ[k] k}

variable (H) in
/-- The ideal `I_H` of `Sym(V*)` generated by the functions of all equations of `H`. For a
hyperplane it is generated by any single equation (`hyperplaneIdeal_eq_span`).

Blueprint: `def:geo-affine-space`. -/
def hyperplaneIdeal : Ideal (CoordinateRing k V) :=
  Ideal.span (coord '' {f : V →ᵃ[k] k | IsEquation f H})

/-- Any equation of `H` generates `I_H`, since two equations differ by a unit of `k`.

Blueprint: `def:geo-affine-space`. -/
theorem hyperplaneIdeal_eq_span (hf : IsEquation f H) :
    hyperplaneIdeal H = Ideal.span {coord f} := by
  apply le_antisymm
  · rw [hyperplaneIdeal, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, hc⟩ := hf.exists_coord_eq_mul hg
    rw [SetLike.mem_coe, hc]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨f, hf, rfl⟩

/-- For a hyperplane, `I_H` is the kernel of restriction to `H`. -/
theorem ker_pull_chart_eq_hyperplaneIdeal (hH : IsHyperplane H) :
    RingHom.ker (pull (chart H)) = hyperplaneIdeal H := by
  rw [(isEquation_equation hH).ker_pull_chart, hyperplaneIdeal_eq_span (isEquation_equation hH)]

variable (H) in
/-- The hyperplane scheme `𝐇 = Spec (Sym(V*) ⧸ I_H)`. It does not depend on a choice of equation.

Blueprint: `def:geo-affine-space`. -/
@[implicit_reducible]
def hyperplaneScheme : Over (Spec (.of k)) :=
  spec (CommAlgCat.of k (CoordinateRing k V ⧸ hyperplaneIdeal H))

lemma hyperplaneScheme_eq :
    hyperplaneScheme H = spec (CommAlgCat.of k (CoordinateRing k V ⧸ hyperplaneIdeal H)) := rfl

instance : IsAffine (hyperplaneScheme H).left := inferInstanceAs (IsAffine (Spec _))

variable (H) in
/-- The closed immersion `𝐇 → 𝔸_V`, `Spec` of the quotient map.

Blueprint: `def:geo-affine-space`. -/
def hyperplaneι : hyperplaneScheme H ⟶ affineSpace k V :=
  specMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k (hyperplaneIdeal H)))

instance : IsClosedImmersion (hyperplaneι H).left :=
  IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mkₐ_surjective k (hyperplaneIdeal H))

/-- The kernel of `𝐇 → 𝔸_V` is the ideal sheaf of `f̃`, for **every** equation `f` of `H`: so `𝐇`
is the zero scheme of `f̃`, and the scheme structure does not depend on the equation.

Blueprint: `def:geo-affine-space`. -/
theorem ker_hyperplaneι (hf : IsEquation f H) :
    (hyperplaneι H).left.ker = principalIdealSheaf (affineSpaceCoord f) :=
  ker_specMap_of_ker_eq _ <| (Ideal.Quotient.mkₐ_ker k (hyperplaneIdeal H)).trans
    (hyperplaneIdeal_eq_span hf)

/-- Every equation of `H` vanishes on `𝐇`. -/
@[simp] lemma hyperplaneι_appTop_affineSpaceCoord (hf : IsEquation f H) :
    (hyperplaneι H).left.appTop (affineSpaceCoord f) = 0 :=
  appTop_eq_zero_of_ker_eq _ (ker_hyperplaneι hf)

/-- For a hyperplane, `Sym(V*) ⧸ I_H` is the coordinate ring of `H.direction`, by restriction along
`chart H`. -/
def hyperplaneQuotientEquiv (hH : IsHyperplane H) :
    (CoordinateRing k V ⧸ hyperplaneIdeal H) ≃ₐ[k] CoordinateRing k H.direction :=
  (Ideal.quotientEquivAlgOfEq k (ker_pull_chart_eq_hyperplaneIdeal hH).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (pull_chart_surjective H))

@[simp] lemma hyperplaneQuotientEquiv_mk (hH : IsHyperplane H) (x : CoordinateRing k V) :
    hyperplaneQuotientEquiv hH (Ideal.Quotient.mk _ x) = pull (chart H) x :=
  rfl

/-- For a hyperplane `H`, the scheme `𝐇` is the affine space of `H.direction`, and its closed
immersion into `𝔸_V` is `𝔸_{chart H}` (`hyperplaneSchemeIso_hom_comp_hyperplaneι`).

Blueprint: `def:geo-affine-space`. -/
def hyperplaneSchemeIso (hH : IsHyperplane H) : affineSpace k H.direction ≅ hyperplaneScheme H :=
  (specFunctor k).mapIso (CommAlgCat.isoMk (hyperplaneQuotientEquiv hH)).op

/-- Under `𝔸_{H.direction} ≅ 𝐇`, the closed immersion `𝐇 → 𝔸_V` is `𝔸_{chart H}`.

Blueprint: `def:geo-affine-space`. -/
@[reassoc (attr := simp)]
lemma hyperplaneSchemeIso_hom_comp_hyperplaneι (hH : IsHyperplane H) :
    (hyperplaneSchemeIso hH).hom ≫ hyperplaneι H = affineSpaceMap k (chart H) := by
  change specMap _ ≫ specMap _ = specMap _
  rw [← specMap_comp]
  rfl

/-- For a hyperplane `H` of a finite-dimensional space, `𝐇` is smooth over `S`, being an affine
space.

Blueprint: `def:geo-affine-space`. -/
lemma smooth_hyperplaneScheme_hom [FiniteDimensional k V] (hH : IsHyperplane H) :
    Smooth (hyperplaneScheme H).hom := by
  rw [← Over.w (hyperplaneSchemeIso hH).inv]
  infer_instance

end Hyperplane

/-! ### Comparison with Mathlib's affine space -/

section Basis

variable {ι : Type u} (b : Basis ι k (Dual k V))

/-- The isomorphism of schemes `𝔸_V ≅ 𝔸(ι; Spec k)` given by a basis `b` of `V*`. -/
def affineSpaceLeftIso : (affineSpace k V).left ≅ 𝔸(ι; Spec (.of k)) :=
  Scheme.Spec.mapIso (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv.toCommRingCatIso.symm.op ≪≫
    (AffineSpace.SpecIso ι (.of k)).symm

lemma affineSpaceLeftIso_hom_over :
    (affineSpaceLeftIso b).hom ≫ 𝔸(ι; Spec (.of k)) ↘ Spec (.of k) = (affineSpace k V).hom := by
  change Spec.map _ ≫ (AffineSpace.SpecIso ι (.of k)).inv ≫ _ = _
  rw [AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom (algebraMap k (CoordinateRing k V)))
  congr 1
  ext c
  change (SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.C c) = _
  rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
  rfl

/-- For a basis `b` of `V*`, the affine space `𝔸_V` is Mathlib's indexed affine space
`𝔸(ι; Spec k)` over `S`, and the coordinates of `𝔸(ι; Spec k)` are the linear forms `b i`
(`affineSpaceIsoAffineSpace_hom_appTop_coord`). The basis enters only here.

Blueprint: `def:geo-affine-space`. -/
def affineSpaceIsoAffineSpace : affineSpace k V ≅ 𝔸(ι; Spec (.of k)).asOver (Spec (.of k)) :=
  Over.isoMk (affineSpaceLeftIso b) (affineSpaceLeftIso_hom_over b)

@[simp] lemma affineSpaceIsoAffineSpace_hom_left :
    (affineSpaceIsoAffineSpace b).hom.left = (affineSpaceLeftIso b).hom := rfl

/-- Under `𝔸_V ≅ 𝔸(ι; Spec k)`, the `i`-th coordinate is the function of the linear form `b i`.

Blueprint: `def:geo-affine-space`. -/
lemma affineSpaceIsoAffineSpace_hom_appTop_coord (i : ι) :
    (affineSpaceIsoAffineSpace b).hom.left.appTop (AffineSpace.coord _ i) =
      affineSpaceCoord (b i).toAffineMap := by
  change (Spec.map _ ≫ (AffineSpace.SpecIso ι (.of k)).inv).appTop _ = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.SpecIso_inv_appTop_coord,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
    affineSpaceCoord, coord_toAffineMap]
  congr 1
  exact SymmetricAlgebra.equivMvPolynomial_symm_X b i

end Basis

/-! ### In a domain -/

variable (D : SmoothDomain k) (V) [FiniteDimensional k V] in
/-- The affine space `𝔸_V` of a finite-dimensional space, as an object of any admissible domain `D`.
It is smooth and affine, so its membership is found by instances.

Blueprint: `def:geo-affine-space`. -/
@[instance_reducible]
def SmoothDomain.affineSpace : D.Obj := D.ofAffine (Geometric.affineSpace k V)

lemma SmoothDomain.affineSpace_obj (D : SmoothDomain k) [FiniteDimensional k V] :
    (D.affineSpace V).obj = Geometric.affineSpace k V := rfl

end OrlikSolomon.Geometric
