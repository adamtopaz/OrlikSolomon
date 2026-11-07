/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module
public import OrlikSolomon.DeRham.Schemes.Forms.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Sheaves.Abelian
/-!
# Sheaves of relative forms

For every scheme over `Spec k`, sheafify the presheaves of relative forms in `k`-modules.
Mathlib's sheafification of presheaves of modules equips these same additive sheaves with their
natural structure-sheaf actions. The differential remains only `k`-linear.

## Main definitions and results

* `formsSheaf` and `formsModuleSheaf`: relative forms as sheaves of `k`-modules and as
  structure-sheaf modules, with the same underlying additive presheaf.
* `formsSheafUnit`: the canonical map from algebraic forms on opens to the sheaf.
* `formsSheafD` and `formsSheafD_comp`: the differential and its square-zero identity.
* `formsComplex`: the de Rham complex indexed by integers and zero in negative degrees.

These constructions require only a commutative base ring. No smoothness, affineness,
separatedness or nonemptiness assumption is used.

Blueprint: the sheafification and complex in `def:geo-forms-sheaf`.
-/

@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open OrlikSolomon.DeRham
universe u
namespace OrlikSolomon.Geometric.DeRham
variable (k : Type u) [CommRing k]
variable (X : Over (Spec (CommRingCat.of k)))

/-- Relative forms with the semilinear restriction maps of a structure-sheaf module. -/
def formsModulePresheaf (n : ℕ) : X.left.PresheafOfModules := by
  let F := formsPresheaf k X n ⋙ forget₂ (ModuleCat k) AddCommGrpCat
  letI (U : X.left.Opensᵒᵖ) : Module (X.left.ringCatSheaf.obj.obj U) (F.obj U) :=
    inferInstanceAs (Module (sectionAlgebra k X U.unop)
      (⋀[sectionAlgebra k X U.unop]^n Ω[sectionAlgebra k X U.unop⁄k]))
  exact PresheafOfModules.ofPresheaf F fun {U V} i r x =>
    Forms.mapPower_smul (sectionRestriction k X i.unop) n r x

/-- The sheafification of relative forms in the category of `k`-modules. -/
def formsSheaf (n : ℕ) : TopCat.Sheaf (ModuleCat k) X.left :=
  (presheafToSheaf (_root_.Opens.grothendieckTopology X.left) (ModuleCat k)).obj
    (formsPresheaf k X n)

/-- The canonical map from algebraic forms on opens to their sheafification. -/
def formsSheafUnit (n : ℕ) : formsPresheaf k X n ⟶ (formsSheaf k X n).obj :=
  CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X.left)
    (formsPresheaf k X n)

private def formsAdditiveSheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat X.left :=
  (sheafCompose (_root_.Opens.grothendieckTopology X.left)
    (forget₂ (ModuleCat k) AddCommGrpCat)).obj (formsSheaf k X n)

private def formsModuleUnit (n : ℕ) :
    (formsModulePresheaf k X n).presheaf ⟶ (formsAdditiveSheaf k X n).obj :=
  Functor.whiskerRight (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X.left)
    (formsPresheaf k X n)) (forget₂ (ModuleCat k) AddCommGrpCat)

private instance formsModuleUnit_locallyInjective (n : ℕ) :
    Presheaf.IsLocallyInjective (_root_.Opens.grothendieckTopology X.left)
      (formsModuleUnit k X n) where
  equalizerSieve_mem a b h := Presheaf.equalizerSieve_mem _
    (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X.left)
      (formsPresheaf k X n)) a b h

private instance formsModuleUnit_locallySurjective (n : ℕ) :
    Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X.left)
      (formsModuleUnit k X n) where
  imageSieve_mem a := Presheaf.imageSieve_mem _
    (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X.left)
      (formsPresheaf k X n)) a

/-- The natural structure-sheaf module on the additive sheaf underlying `formsSheaf`. -/
@[no_expose] def formsModuleSheaf (n : ℕ) : X.left.Modules :=
  PresheafOfModules.sheafify (A := formsAdditiveSheaf k X n)
    (𝟙 X.left.ringCatSheaf.obj) (formsModuleUnit k X n)

/-- The two versions of forms have the same underlying additive presheaf. -/
theorem formsModuleSheaf_presheaf (n : ℕ) :
    (formsModuleSheaf k X n).presheaf =
      (formsSheaf k X n).obj ⋙ forget₂ (ModuleCat k) AddCommGrpCat := by
  rfl

/-- The sheafification map with its structure-sheaf linearity. -/
@[no_expose] def formsModuleSheafUnit (n : ℕ) :
    formsModulePresheaf k X n ⟶ (formsModuleSheaf k X n).val :=
  PresheafOfModules.toSheafify (𝟙 X.left.ringCatSheaf.obj) (formsModuleUnit k X n)

/-- The module-valued and base-linear sheafification maps agree under the carrier comparison. -/
theorem formsModuleSheafUnit_presheaf (n : ℕ) :
    (PresheafOfModules.toPresheaf _).map (formsModuleSheafUnit k X n) ≫
      eqToHom (formsModuleSheaf_presheaf k X n) =
      Functor.whiskerRight (formsSheafUnit k X n) (forget₂ (ModuleCat k) AddCommGrpCat) := by
  ext U x
  rfl

/-- Restricting the structure-sheaf action gives the base-ring action on module-valued forms. -/
instance formsModuleSheafBaseModule (n : ℕ) (U : X.left.Opens) :
    Module k Γ(formsModuleSheaf k X n, U) :=
  Module.compHom (R := Γ(X.left, U)) _
    (show k →+* Γ(X.left, U) from algebraMap k (sectionAlgebra k X U))

private theorem formsSheaf_algebraMap_smul (n : ℕ) (U : X.left.Opensᵒᵖ)
    (r : k) (x : (formsSheaf k X n).obj.obj U) :
    PresheafOfModules.Sheafify.smul (𝟙 X.left.ringCatSheaf.obj) (formsModuleUnit k X n)
      (show X.left.ringCatSheaf.obj.obj U from algebraMap k (sectionAlgebra k X U.unop) r) x =
        r • x := by
  apply (formsAdditiveSheaf k X n).isSeparated _ _
    (Presheaf.imageSieve_mem _ (formsModuleUnit k X n) x)
  rintro V f ⟨z, hz⟩
  rw [PresheafOfModules.Sheafify.map_smul_eq _ _ _ _ f.op
    (algebraMap k (sectionAlgebra k X V) r)
    (by exact (sectionRestriction k X f).commutes r |>.symm) z hz]
  let z' : ⋀[sectionAlgebra k X V]^n Ω[sectionAlgebra k X V⁄k] := z
  change (formsSheafUnit k X n).app (op V)
    (algebraMap k (sectionAlgebra k X V) r • z') =
      (formsSheaf k X n).obj.map f.op (r • x)
  rw [algebraMap_smul]
  have hz' : (formsSheafUnit k X n).app (op V) z' =
      (formsSheaf k X n).obj.map f.op x := hz
  exact (((formsSheafUnit k X n).app (op V)).hom.map_smul r z').trans
    ((congrArg (fun t : (formsSheaf k X n).obj.obj (op V) => r • t) hz').trans
      (((formsSheaf k X n).obj.map f.op).hom.map_smul r x).symm)

/-- The natural structure-sheaf action restricts to the original action on sheafified forms. -/
@[no_expose] def formsModuleSheafBaseIso (n : ℕ) (U : X.left.Opens) :
    ModuleCat.of k Γ(formsModuleSheaf k X n, U) ≅ (formsSheaf k X n).obj.obj (op U) :=
  LinearEquiv.toModuleIso
    { __ := AddEquiv.refl _,
      map_smul' r x := formsSheaf_algebraMap_smul k X n (op U) r x }

/-- The sheaf differential, obtained from the existing algebraic differential. -/
def formsSheafD (n : ℕ) : formsSheaf k X n ⟶ formsSheaf k X (n + 1) :=
  (presheafToSheaf (_root_.Opens.grothendieckTopology X.left) (ModuleCat k)).map
    (formsPresheafD k X n)

/-- The sheaf differential squares to zero. -/
theorem formsSheafD_comp (n : ℕ) : formsSheafD k X n ≫ formsSheafD k X (n + 1) = 0 := by
  change (presheafToSheaf _ (ModuleCat k)).map (formsPresheafD k X n) ≫
    (presheafToSheaf _ (ModuleCat k)).map (formsPresheafD k X (n + 1)) = _
  rw [← Functor.map_comp, formsPresheafD_comp, Functor.map_zero]
  rfl

/-- Sheafification of algebraic forms commutes with the differential. -/
theorem formsSheafUnit_d (n : ℕ) :
    formsSheafUnit k X n ≫ (formsSheafD k X n).hom =
      formsPresheafD k X n ≫ formsSheafUnit k X (n + 1) := by
  exact (CategoryTheory.toSheafify_naturality _ (formsPresheafD k X n)).symm

/-- The relative de Rham complex in nonnegative degrees. -/
def formsComplexNat : CochainComplex (TopCat.Sheaf (ModuleCat k) X.left) ℕ :=
  CochainComplex.of (formsSheaf k X) (formsSheafD k X) (formsSheafD_comp k X)

/-- The relative de Rham complex, extended by zero in negative degrees. -/
def formsComplex : CochainComplex (TopCat.Sheaf (ModuleCat k) X.left) ℤ :=
  (formsComplexNat k X).extend ComplexShape.embeddingUpNat

instance formsComplex_isStrictlyGE : (formsComplex k X).IsStrictlyGE 0 := by
  dsimp only [formsComplex]
  infer_instance

/-- The relative de Rham complex has zero terms in every negative degree. -/
theorem formsComplex_isZero_of_neg (i : ℤ) (hi : i < 0) :
    CategoryTheory.Limits.IsZero ((formsComplex k X).X i) :=
  (formsComplex k X).isZero_of_isStrictlyGE 0 i hi

end OrlikSolomon.Geometric.DeRham
