/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Presentation.CokernelGrading
public import OrlikSolomon.Presentation.Realization

/-!
# The affine structure theorem

For every arrangement `𝒜`, in every finite-dimensional space, the realization map
`Φ_𝒜 : OS_B(𝒜) → C(U_𝒜)` is a bigrading-preserving equivalence of `B`-algebras. This is
`OrdinaryTheory.affineEquiv`, the main affine theorem of the project, and the second half of this
file is its public interface. To use the theorem, read that half: the first half is the induction.

The statements with coefficients in `R`, which give the groups `H^{p, w}(U_𝒜)` and the diagonal,
are in `Presentation/Ordinary`.

## Main definitions

* `OrdinaryTheory.affineEquiv 𝒜 : OSAlgebra B 𝒜 ≃ₐ[B] T.C.obj (complement 𝒜)`: the theorem.
* `OrdinaryTheory.affineComponentEquiv 𝒜 i`: its restriction to the pieces of bidegree `i`.
* `OrdinaryTheory.residueComparison H : DeletionCokernel B 𝒜 H →ₗ[B] C(U_𝒜'')`: the map `ψ` induced
  by the residue, in `lem:comparison-residue`.
* `OrdinaryTheory.restrictionCokernelEquiv H`: the equivalence of `A''` with `A / im a` given by
  `s`, and `OrdinaryTheory.restrictionCokernelComponentEquiv H` on the pieces of a given bidegree.

## Main results

* `lem:comparison-residue`: `OrdinaryTheory.residueComparison_cokernelMk`, which says that `ψ` is
  induced by `r Φ_𝒜`, and `OrdinaryTheory.residueComparison_comp_restrictionToCokernel`, which says
  that `ψ s = Φ_𝒜''`. Vanishing on the old image is
  `OrdinaryTheory.deletionResidue_realization_deletionMap`, in `Presentation/Realization`.
* `thm:affine`, the algebra map: `OrdinaryTheory.bijective_realization` and
  `OrdinaryTheory.affineEquiv`, with
  - the bigrading in both directions: `OrdinaryTheory.isHomogeneousOfShift_affineEquiv`,
    `OrdinaryTheory.isHomogeneousOfShift_affineEquiv_symm`,
    `OrdinaryTheory.affineEquiv_mem_grading_iff`,
    `OrdinaryTheory.affineEquiv_symm_mem_bigrading_iff`, `OrdinaryTheory.decompose_affineEquiv`;
  - generators go to logarithms: `OrdinaryTheory.affineEquiv_generator_zeroLocus`,
    `OrdinaryTheory.affineEquiv_generator`, `OrdinaryTheory.affineEquiv_generator_of_isEquation`;
  - independence of the equations: `OrdinaryTheory.toAlgHom_affineEquiv_eq_lift` and
    `OrdinaryTheory.toAlgHom_affineEquiv_unique`.
* `thm:affine`, every deletion: `OrdinaryTheory.injective_deletionMap`,
  `OrdinaryTheory.bijective_restrictionToCokernel`,
  `OrdinaryTheory.isHomogeneousOfShift_restrictionCokernelEquiv`,
  `OrdinaryTheory.isHomogeneousOfShift_restrictionCokernelEquiv_symm` and
  `OrdinaryTheory.bijective_residueComparison`.

## Implementation notes

**The induction.** `Arrangement.induction` is a strong induction on the number of hyperplanes, over
all finite-dimensional ambient spaces, as it must be since a restriction changes the space. The step
is `OrdinaryTheory.injective_realization_of_injective`. It applies the separate conclusions of
`lem:comparison` in `Algebra/Exact`, which are elementwise arguments, with no five lemma and no
chosen inverse to `j^*`. Only injectivity on the two smaller arrangements is needed for the step.
The surjectivity of `Φ_𝒜` is `surjective_realization`, from `thm:generation`. No rank is compared at
any point, so the coefficient ring is arbitrary.

**Why `T` appears in the statements about `OS_B`.** The statements for a deletion, such as
`injective_deletionMap`, are about the presentation only, but they take a theory `T` with
coefficient ring `B`, since they are proved by comparison with cohomology.

**`simp`.** The generator lemmas mirror those of `Presentation/Realization`. The formula for any
equation `f` of `H` is `affineEquiv_generator_of_isEquation`. Since `f` is not on its left side, it
cannot fire as a bare `simp` lemma: give it the equation, as in
`simp [T.affineEquiv_generator_of_isEquation H hf]`. The `simp` lemma
`affineEquiv_generator_zeroLocus` fires with no further input on a label `⟨zeroLocus f, _⟩`.
`affineEquiv_apply`, which relates `affineEquiv` to `realization`, is not a `simp` lemma, so that
the lemmas here fire: use it with `rw`.

`Presentation/Ordinary` and `Examples/Ordinary` show how the theorem is used.

## Blueprint

`lem:comparison-residue`, `thm:affine`.
-/

@[expose] public section

noncomputable section

open CategoryTheory DirectSum
open OrlikSolomon.SmoothAlg OrlikSolomon.Arrangement OrlikSolomon.OSAlgebra

universe u v w z

namespace OrlikSolomon

namespace OrdinaryTheory

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {B : Type w} [CommRing B]
  [Algebra R B] {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] (T : OrdinaryTheory.{u, v, w, z} k ℬ)
  {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {𝒜 : Arrangement k V}

/-! ### `lem:comparison-residue` -/

section Comparison

/-- The residue kills what is pulled back from `U_𝒜'`, as linear maps: the hypothesis `r j = 0` of
`lem:comparison`. -/
theorem deletionResidue_comp_map_complementInclusion {H : AffineSubspace k V} (hH : H ∈ 𝒜) :
    T.deletionResidue hH ∘ₗ (T.C.map (complementInclusion (𝒜.deletion_le H))).hom.toLinearMap = 0 :=
  LinearMap.ext fun x ↦ T.deletionResidue_map_complementInclusion hH x

variable (H : 𝒜)

/-- The map `ψ : A / im a → C(U_𝒜'')` induced by `r Φ_𝒜`, which vanishes on the old image. It is
characterized by `residueComparison_cokernelMk`, and `residueComparison_comp_restrictionToCokernel`
computes its composite with `s`. By `bijective_residueComparison` it is bijective.

Blueprint: `lem:comparison-residue`. -/
def residueComparison :
    DeletionCokernel B 𝒜 H →ₗ[B] T.C.obj (complement (𝒜.restriction H)) :=
  cokernelComparison (T.deletionResidue_comp_map_complementInclusion H.2)
    (T.realization_toLinearMap_comp_deletionMap 𝒜 H)

/-- The map `ψ` sends the class of `x` to `r (Φ_𝒜 x)`.

Blueprint: `lem:comparison-residue`. -/
@[simp]
theorem residueComparison_cokernelMk (x : OSAlgebra B 𝒜) :
    T.residueComparison H (cokernelMk B 𝒜 H x) = T.deletionResidue H.2 (T.realization 𝒜 x) :=
  rfl

/-- The composite `ψ s` is `Φ_𝒜''`, on elements. On a word `e_{L₁} ⋯ e_{Lₜ}` this is the residue
formula with `[f_H]` first, and each old logarithm restricts to the logarithm of its retained
hyperplane, with no scalar surviving.

Blueprint: `lem:comparison-residue`. -/
@[simp]
theorem residueComparison_restrictionToCokernel (x : OSAlgebra B (𝒜.restriction H)) :
    T.residueComparison H (restrictionToCokernel B 𝒜 H x) = T.realization (𝒜.restriction H) x := by
  have h : T.residueComparison H ∘ₗ restrictionToCokernel B 𝒜 H =
      (T.realization (𝒜.restriction H)).toLinearMap := by
    refine linearMap_ext B _ fun I ↦ ?_
    rw [LinearMap.comp_apply, restrictionToCokernel_word, residueComparison_cokernelMk,
      word_representativeGenerator]
    exact T.deletionResidue_realization_generator_mul_word H.2 representative comap_representative I
  exact LinearMap.congr_fun h x

/-- The composite `ψ s` is `Φ_𝒜''`.

Blueprint: `lem:comparison-residue`. -/
theorem residueComparison_comp_restrictionToCokernel :
    T.residueComparison H ∘ₗ restrictionToCokernel B 𝒜 H =
      (T.realization (𝒜.restriction H)).toLinearMap :=
  LinearMap.ext (T.residueComparison_restrictionToCokernel H)

/-- The map `ψ` has shift `(-1, -1)`, since the residue does and `Φ_𝒜` preserves the bigrading.

Blueprint: `lem:comparison-residue`. -/
theorem isHomogeneousOfShift_residueComparison :
    IsHomogeneousOfShift (cokernelGrading 𝒜 ℬ H) (T.grading (complement (𝒜.restriction H))) (-1, -1)
      (T.residueComparison H) := by
  intro i y hy
  obtain ⟨x, hx, rfl⟩ := (mem_cokernelGrading 𝒜 ℬ H).1 hy
  exact T.isHomogeneousOfShift_deletionResidue H.2 (T.realization_mem_grading hx)

end Comparison

/-! ### The second induction -/

section Induction

/-- The inductive step of `thm:affine`: if `Φ` is injective on the deletion and the restriction of a
hyperplane, then it is injective on `𝒜`. The first induction supplies the injectivity of `j^*`, and
`lem:lift-surj` the surjectivity of `s`. -/
theorem injective_realization_of_injective (H : 𝒜)
    (h' : Function.Injective (T.realization (𝒜.deletion H)))
    (h'' : Function.Injective (T.realization (𝒜.restriction H))) :
    Function.Injective (T.realization 𝒜) :=
  injective_of_surjective_of_injective_cokernelComparison_comp
    (T.injective_toLinearMap_complementInclusion H.2) h'
    (T.deletionResidue_comp_map_complementInclusion H.2)
    (T.realization_toLinearMap_comp_deletionMap 𝒜 H) (restrictionToCokernel_surjective B 𝒜 H)
    (show Function.Injective (T.residueComparison H ∘ₗ restrictionToCokernel B 𝒜 H) by
      rw [T.residueComparison_comp_restrictionToCokernel H]
      exact h'')

variable (𝒜) in
/-- **The structure theorem**: the realization map of every arrangement is bijective. This is a
strong induction on the number of hyperplanes, over all finite-dimensional ambient spaces.

Blueprint: `thm:affine`. -/
theorem bijective_realization : Function.Bijective (T.realization 𝒜) := by
  refine ⟨?_, T.surjective_realization 𝒜⟩
  refine Arrangement.induction
    (motive := fun _ _ _ _ 𝒜 ↦ Function.Injective (T.realization 𝒜))
    (fun V _ _ _ ↦ (T.bijective_realization_empty V).1) ?_ V 𝒜
  exact fun _ _ _ _ _ H hH h' h'' ↦ T.injective_realization_of_injective ⟨H, hH⟩ h' h''

end Induction

/-! ### `thm:affine`: the equivalence -/

section Affine

variable (𝒜) in
/-- **The affine structure theorem.** For every arrangement `𝒜` of hyperplanes in a
finite-dimensional space, the realization map `Φ_𝒜`, which sends the generator `e_H` to the
logarithm `[f_H]` of any equation of `H`, is an equivalence of `B`-algebras from the Orlik–Solomon
presentation to the cohomology of the complement.

It preserves the bigrading in both directions, by `isHomogeneousOfShift_affineEquiv` and
`isHomogeneousOfShift_affineEquiv_symm`. It does not depend on the equations, by
`affineEquiv_generator_of_isEquation` and `toAlgHom_affineEquiv_eq_lift`. It holds for every
commutative coefficient ring, including `ℤ / 2` and the zero ring, and in dimension zero.

Blueprint: `thm:affine`. -/
def affineEquiv : OSAlgebra B 𝒜 ≃ₐ[B] T.C.obj (complement 𝒜) :=
  AlgEquiv.ofBijective (T.realization 𝒜) (T.bijective_realization 𝒜)

/-- The structure theorem is the realization map. This is for `rw`, and it is not a `simp` lemma, so
that the lemmas below fire.

Blueprint: `thm:affine`. -/
theorem affineEquiv_apply (x : OSAlgebra B 𝒜) : T.affineEquiv 𝒜 x = T.realization 𝒜 x :=
  rfl

variable (𝒜) in
/-- The structure theorem is the realization map, as algebra maps. -/
@[simp]
theorem toAlgHom_affineEquiv : (T.affineEquiv 𝒜 : OSAlgebra B 𝒜 →ₐ[B] _) = T.realization 𝒜 :=
  AlgHom.ext fun _ ↦ rfl

/-- The equivalence sends a generator to the logarithm of the chosen equation of its hyperplane.
`affineEquiv_generator_of_isEquation` is the same formula for any equation. -/
@[simp]
theorem affineEquiv_generator (H : 𝒜) :
    T.affineEquiv 𝒜 (generator B 𝒜 H) = T.logClass (equationUnit 𝒜 H) :=
  T.realization_generator H

/-- The equivalence sends a generator to the logarithm of **any** equation of its hyperplane. Since
`f` is not on the left, `simp` needs the equation to be given, as in
`simp [T.affineEquiv_generator_of_isEquation H hf]`.

Blueprint: `thm:affine`. -/
theorem affineEquiv_generator_of_isEquation {f : V →ᵃ[k] k} (H : 𝒜)
    (hf : IsEquation f H) :
    T.affineEquiv 𝒜 (generator B 𝒜 H) = T.logClass (complementUnit 𝒜 f (hf.covers H.2)) :=
  T.realization_generator_of_isEquation H hf

/-- The generator formula for a label presented by an equation: if the zero locus of `f` is a
hyperplane of `𝒜`, then the generator of that hyperplane goes to `[f]`. Here `f` is on the left, so
`simp` uses this with no further input, for any equation. It takes priority over
`affineEquiv_generator`, which would replace `f` by the chosen equation.

Blueprint: `thm:affine`. -/
@[simp high]
theorem affineEquiv_generator_zeroLocus {f : V →ᵃ[k] k} (hf : zeroLocus f ∈ 𝒜) :
    T.affineEquiv 𝒜 (generator B 𝒜 ⟨zeroLocus f, hf⟩) =
      T.logClass (complementUnit 𝒜 f (.of_mem hf)) :=
  T.realization_generator_zeroLocus hf

/-- The equivalence sends a word in the generators to the logarithmic monomial of the word. -/
@[simp high]
theorem affineEquiv_word (I : List 𝒜) :
    T.affineEquiv 𝒜 (word (generator B 𝒜) I) = T.logMonomial 𝒜 I :=
  T.realization_word I

/-- The inverse of the equivalence sends the logarithm of any equation of `H` to the generator of
`H`.

Blueprint: `thm:affine`. -/
theorem affineEquiv_symm_logClass {f : V →ᵃ[k] k} (H : 𝒜) (hf : IsEquation f H) :
    (T.affineEquiv 𝒜).symm (T.logClass (complementUnit 𝒜 f (hf.covers H.2))) = generator B 𝒜 H := by
  rw [← T.affineEquiv_generator_of_isEquation H hf, AlgEquiv.symm_apply_apply]

/-- The inverse of the equivalence sends a logarithmic monomial to the word in the generators. -/
@[simp]
theorem affineEquiv_symm_logMonomial (I : List 𝒜) :
    (T.affineEquiv 𝒜).symm (T.logMonomial 𝒜 I) = word (generator B 𝒜) I := by
  rw [← T.affineEquiv_word I, AlgEquiv.symm_apply_apply]

/-- The equivalence does not depend on the equations: it is the lift of the logarithms of **any**
choice of equations.

Blueprint: `thm:affine`. -/
theorem toAlgHom_affineEquiv_eq_lift (F : 𝒜 → V →ᵃ[k] k) (hF : ∀ H : 𝒜, IsEquation (F H) H) :
    (T.affineEquiv 𝒜 : OSAlgebra B 𝒜 →ₐ[B] _) =
      OSAlgebra.lift _ (T.isFamily_logClass_complementUnit F hF) := by
  rw [toAlgHom_affineEquiv, T.realization_eq_lift F hF]

/-- The equivalence is the unique algebra map sending each generator to the logarithm of some
equation of its hyperplane, for equations that may be chosen arbitrarily.

Blueprint: `thm:affine`. -/
theorem toAlgHom_affineEquiv_unique (F : 𝒜 → V →ᵃ[k] k) (hF : ∀ H : 𝒜, IsEquation (F H) H)
    (φ : OSAlgebra B 𝒜 →ₐ[B] T.C.obj (complement 𝒜))
    (hφ : ∀ H : 𝒜, φ (generator B 𝒜 H) = T.logClass (complementUnit 𝒜 (F H) ((hF H).covers H.2))) :
    φ = T.affineEquiv 𝒜 :=
  OSAlgebra.algHom_ext fun H ↦ by
    rw [hφ H]
    exact (T.affineEquiv_generator_of_isEquation H (hF H)).symm

variable (𝒜) in
/-- The equivalence preserves the bigrading of the presentation, with `e_H` in bidegree `(1, 1)` and
`B_w` in bidegree `(0, w)`.

Blueprint: `thm:affine`. -/
theorem isHomogeneousOfShift_affineEquiv :
    IsHomogeneousOfShift (bigrading 𝒜 ℬ) (T.grading (complement 𝒜)) 0 (T.affineEquiv 𝒜) :=
  T.isHomogeneousOfShift_realization

variable (𝒜) in
/-- The inverse of the equivalence preserves the bigrading. This is `lem:extraction`.

Blueprint: `thm:affine`. -/
theorem isHomogeneousOfShift_affineEquiv_symm :
    IsHomogeneousOfShift (T.grading (complement 𝒜)) (bigrading 𝒜 ℬ) 0 (T.affineEquiv 𝒜).symm := by
  simpa only [neg_zero] using (T.isHomogeneousOfShift_affineEquiv 𝒜).algEquiv_symm

/-- An element has bidegree `i` exactly when its image under the equivalence has bidegree `i`.

Blueprint: `thm:affine`. -/
theorem affineEquiv_mem_grading_iff {i : ℤ × ℤ} {x : OSAlgebra B 𝒜} :
    T.affineEquiv 𝒜 x ∈ T.grading (complement 𝒜) i ↔ x ∈ bigrading 𝒜 ℬ i :=
  ⟨(T.isHomogeneousOfShift_affineEquiv 𝒜).mem_of_map_mem (T.affineEquiv 𝒜).injective (add_zero i),
    fun hx ↦ isHomogeneousOfShift_zero_iff.1 (T.isHomogeneousOfShift_affineEquiv 𝒜) hx⟩

/-- A class has bidegree `i` exactly when its image under the inverse has bidegree `i`.

Blueprint: `thm:affine`. -/
theorem affineEquiv_symm_mem_bigrading_iff {i : ℤ × ℤ} {y : T.C.obj (complement 𝒜)} :
    (T.affineEquiv 𝒜).symm y ∈ bigrading 𝒜 ℬ i ↔ y ∈ T.grading (complement 𝒜) i := by
  rw [← T.affineEquiv_mem_grading_iff, AlgEquiv.apply_symm_apply]

/-- The equivalence commutes with taking homogeneous components. -/
theorem decompose_affineEquiv (x : OSAlgebra B 𝒜) (i : ℤ × ℤ) :
    (decompose (T.grading (complement 𝒜)) (T.affineEquiv 𝒜 x) i : T.C.obj (complement 𝒜)) =
      T.affineEquiv 𝒜 (decompose (bigrading 𝒜 ℬ) x i) :=
  (T.isHomogeneousOfShift_affineEquiv 𝒜).decompose_map (add_zero i) x

variable (𝒜) in
/-- The equivalence on the pieces of bidegree `i`. It is `R`-linear, since the pieces are
`R`-submodules. `Presentation/Ordinary` computes these pieces.

Blueprint: `thm:affine`. -/
def affineComponentEquiv (i : ℤ × ℤ) :
    bigrading 𝒜 ℬ i ≃ₗ[R] T.grading (complement 𝒜) i :=
  IsHomogeneousOfShift.componentEquiv (e := (T.affineEquiv 𝒜).toLinearEquiv)
    (T.isHomogeneousOfShift_affineEquiv 𝒜) (add_zero i)

@[simp]
theorem coe_affineComponentEquiv_apply (i : ℤ × ℤ) (x : bigrading 𝒜 ℬ i) :
    (T.affineComponentEquiv 𝒜 i x : T.C.obj (complement 𝒜)) = T.affineEquiv 𝒜 x :=
  rfl

@[simp]
theorem coe_affineComponentEquiv_symm_apply (i : ℤ × ℤ) (y : T.grading (complement 𝒜) i) :
    ((T.affineComponentEquiv 𝒜 i).symm y : OSAlgebra B 𝒜) = (T.affineEquiv 𝒜).symm y :=
  rfl

/-- The equivalence commutes with an inclusion of arrangements and the open pullback. -/
@[simp]
theorem affineEquiv_map {𝒟 : Arrangement k V} (h : 𝒜 ≤ 𝒟) (x : OSAlgebra B 𝒜) :
    T.affineEquiv 𝒟 (OSAlgebra.map B h x) = T.C.map (complementInclusion h) (T.affineEquiv 𝒜 x) :=
  T.realization_map h x

/-- The equivalence commutes with deletion and the open pullback. -/
@[simp]
theorem affineEquiv_deletionMap (H : AffineSubspace k V) (x : OSAlgebra B (𝒜.deletion H)) :
    T.affineEquiv 𝒜 (deletionMap B 𝒜 H x) =
      T.C.map (complementInclusion (𝒜.deletion_le H)) (T.affineEquiv (𝒜.deletion H) x) :=
  T.realization_deletionMap 𝒜 H x

/-- The equivalence commutes with a relabeling along an affine equivalence, which includes an affine
coordinate change, and the isomorphism of complements. -/
@[simp]
theorem affineEquiv_comapEquiv {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {𝒟 : Arrangement k W} (e : W ≃ᵃ[k] V) (h : ∀ K, K ∈ 𝒜 ↔ K.comap (e : W →ᵃ[k] V) ∈ 𝒟)
    (x : OSAlgebra B 𝒜) :
    T.affineEquiv 𝒟 (OSAlgebra.comapEquiv B e h x) =
      T.C.map (complementIso 𝒜 𝒟 e h).hom (T.affineEquiv 𝒜 x) :=
  T.realization_comapEquiv e h x

end Affine

/-! ### `thm:affine`: every deletion -/

section Deletion

variable (H : 𝒜)

include T in
/-- The deletion algebra map `a : OS_B(𝒜') → OS_B(𝒜)` is injective.

Blueprint: `thm:affine`. -/
theorem injective_deletionMap : Function.Injective (deletionMap B 𝒜 H) :=
  injective_of_comp_eq_comp (T.injective_toLinearMap_complementInclusion H.2)
    (T.bijective_realization (𝒜.deletion H)).1 (T.realization_toLinearMap_comp_deletionMap 𝒜 H)

/-- The composite `ψ s = Φ_𝒜''` is bijective. -/
private theorem bijective_residueComparison_comp :
    Function.Bijective (T.residueComparison H ∘ₗ restrictionToCokernel B 𝒜 H) := by
  rw [T.residueComparison_comp_restrictionToCokernel H]
  exact T.bijective_realization _

include T in
/-- The linear map `s : OS_B(𝒜'') → OS_B(𝒜) / im a` is bijective.

Blueprint: `thm:affine`. -/
theorem bijective_restrictionToCokernel :
    Function.Bijective (restrictionToCokernel B 𝒜 H) :=
  bijective_of_surjective_of_injective_cokernelComparison_comp
    (T.deletionResidue_comp_map_complementInclusion H.2)
    (T.realization_toLinearMap_comp_deletionMap 𝒜 H) (restrictionToCokernel_surjective B 𝒜 H)
    (T.bijective_residueComparison_comp H).1

/-- The map `ψ : OS_B(𝒜) / im a → C(U_𝒜'')` induced by the residue is bijective.

Blueprint: `thm:affine`, `lem:comparison`. -/
theorem bijective_residueComparison : Function.Bijective (T.residueComparison H) :=
  cokernelComparison_bijective_of_surjective_of_bijective_comp
    (T.deletionResidue_comp_map_complementInclusion H.2)
    (T.realization_toLinearMap_comp_deletionMap 𝒜 H) (restrictionToCokernel_surjective B 𝒜 H)
    (T.bijective_residueComparison_comp H)

/-- The linear equivalence `OS_B(𝒜'') ≃ OS_B(𝒜) / im a` given by `s`. It has shift `(1, 1)`, by
`isHomogeneousOfShift_restrictionCokernelEquiv`, and its inverse has shift `(-1, -1)`.

Blueprint: `thm:affine`. -/
def restrictionCokernelEquiv :
    OSAlgebra B (𝒜.restriction H) ≃ₗ[B] DeletionCokernel B 𝒜 H :=
  LinearEquiv.ofBijective (restrictionToCokernel B 𝒜 H) (T.bijective_restrictionToCokernel H)

@[simp]
theorem restrictionCokernelEquiv_apply (x : OSAlgebra B (𝒜.restriction H)) :
    T.restrictionCokernelEquiv H x = restrictionToCokernel B 𝒜 H x :=
  rfl

/-- The equivalence given by `s` has shift `(1, 1)`.

Blueprint: `thm:affine`. -/
theorem isHomogeneousOfShift_restrictionCokernelEquiv :
    IsHomogeneousOfShift (bigrading (𝒜.restriction H) ℬ) (cokernelGrading 𝒜 ℬ H) (1, 1)
      (T.restrictionCokernelEquiv H) :=
  restrictionToCokernel_isHomogeneous 𝒜 ℬ H

/-- The inverse of the equivalence given by `s` has shift `(-1, -1)`.

Blueprint: `thm:affine`. -/
theorem isHomogeneousOfShift_restrictionCokernelEquiv_symm :
    IsHomogeneousOfShift (cokernelGrading 𝒜 ℬ H) (bigrading (𝒜.restriction H) ℬ) (-1, -1)
      (T.restrictionCokernelEquiv H).symm :=
  (T.isHomogeneousOfShift_restrictionCokernelEquiv H).linearEquiv_symm

/-- The equivalence given by `s` on the pieces of bidegree `i` of `OS_B(𝒜'')` and `j = i + (1, 1)`
of `OS_B(𝒜) / im a`. This is what the shift by `(1, 1)` means.

Blueprint: `thm:affine`. -/
def restrictionCokernelComponentEquiv {i j : ℤ × ℤ} (hij : i + (1, 1) = j) :
    bigrading (𝒜.restriction H) ℬ i ≃ₗ[R] cokernelGrading 𝒜 ℬ H j :=
  (T.isHomogeneousOfShift_restrictionCokernelEquiv H).componentEquiv hij

@[simp]
theorem coe_restrictionCokernelComponentEquiv_apply {i j : ℤ × ℤ} (hij : i + (1, 1) = j)
    (x : bigrading (𝒜.restriction H) ℬ i) :
    (T.restrictionCokernelComponentEquiv H hij x : DeletionCokernel B 𝒜 H) =
      restrictionToCokernel B 𝒜 H x :=
  rfl

end Deletion

end OrdinaryTheory

end OrlikSolomon
