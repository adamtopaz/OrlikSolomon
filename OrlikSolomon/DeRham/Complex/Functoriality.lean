/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.DeRham.Complex.Differential

/-!
# Functoriality of forms

A `k`-algebra map `φ : A → A'` induces a map on forms, sending `a₀ da₁ ∧ ⋯ ∧ daₙ` to
`φ a₀ d(φ a₁) ∧ ⋯ ∧ d(φ aₙ)`. It is a `k`-algebra map that preserves degrees and commutes with `d`.
It is semilinear over `φ`, and it is not `A'`-linear in any sense, since its source is only an
`A`-module. So it is stated as a `k`-algebra map, and `Forms.map_smul` records the semilinearity.

## Main definitions

* `OrlikSolomon.DeRham.Forms.map φ`: the map on forms induced by `φ : A →ₐ[k] A'`.
* `OrlikSolomon.DeRham.Forms.mapₛₗ φ`: the same map as a map that is semilinear over `φ`.
* `OrlikSolomon.DeRham.Forms.mapEquiv e`: the equivalence on forms of an equivalence
  `e : A ≃ₐ[k] A'`.
* `OrlikSolomon.DeRham.Forms.mapPower φ n`: the map in degree `n`, between the typed pieces.

## Main results

Blueprint `thm:dr-dga`:

* `OrlikSolomon.DeRham.Forms.map_smul_word`: the formula on words.
* `OrlikSolomon.DeRham.Forms.map_d`: the map is a chain map.
* `OrlikSolomon.DeRham.Forms.map_mem_exteriorPower`: the map preserves degrees.
* `OrlikSolomon.DeRham.Forms.map_id` and `OrlikSolomon.DeRham.Forms.map_map`: identities and
  composition.

To use the exterior algebra API of `DeRham/Exterior` on these maps, such as base change along a
localization or the kernel along a surjection, `OrlikSolomon.DeRham.Forms.map_toAlgHom` identifies
the map of an algebra `S` over `A` with `exteriorMap S (KaehlerDifferential.map k k A S)`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

open ExteriorAlgebra (ι)
open KaehlerDifferential (D)

universe u v v' v''

variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {A' : Type v'} [CommRing A'] [Algebra k A']
  {A'' : Type v''} [CommRing A''] [Algebra k A'']

variable (k) in
/-- The grade involution negates the form `da`. -/
@[simp]
theorem involute_diff (a : A) : CliffordAlgebra.involute (diff k a) = -diff k a :=
  CliffordAlgebra.involute_ι _

namespace Forms

/-- The `k`-algebra map on forms induced by a `k`-algebra map `φ : A → A'`, sending
`a₀ da₁ ∧ ⋯ ∧ daₙ` to `φ a₀ d(φ a₁) ∧ ⋯ ∧ d(φ aₙ)`. It is semilinear over `φ`, by `map_smul`.
It is characterized by its values on `a` and on `da`, by `algHom_ext`.

Blueprint: `thm:dr-dga`. -/
noncomputable def map (φ : A →ₐ[k] A') : Forms k A →ₐ[k] Forms k A' :=
  letI : Algebra A A' := φ.toAlgebra
  haveI : IsScalarTower k A A' := .of_algebraMap_eq fun c => (φ.commutes c).symm
  (exteriorMap A' (KaehlerDifferential.map k k A A')).restrictScalars k

@[simp]
theorem map_algebraMap (φ : A →ₐ[k] A') (a : A) :
    map φ (algebraMap A (Forms k A) a) = algebraMap A' (Forms k A') (φ a) := by
  let : Algebra A A' := φ.toAlgebra
  have : IsScalarTower k A A' := .of_algebraMap_eq fun c => (φ.commutes c).symm
  exact IsScalarTower.algebraMap_apply A A' (Forms k A') a ▸ AlgHom.commutes _ a

@[simp]
theorem map_diff (φ : A →ₐ[k] A') (a : A) : map φ (diff k a) = diff k (φ a) := by
  let : Algebra A A' := φ.toAlgebra
  have : IsScalarTower k A A' := .of_algebraMap_eq fun c => (φ.commutes c).symm
  exact (exteriorMap_ι A' _ _).trans (congrArg (ι A') (KaehlerDifferential.map_D k k A A' a))

/-- The map on forms is semilinear over `φ`.

Blueprint: `thm:dr-dga`. -/
@[simp]
theorem map_smul (φ : A →ₐ[k] A') (a : A) (x : Forms k A) : map φ (a • x) = φ a • map φ x := by
  rw [Algebra.smul_def, map_mul, map_algebraMap, ← Algebra.smul_def]

/-- The map on forms, as a map that is semilinear over `φ`. The underlying function is `map φ`. -/
noncomputable def mapₛₗ (φ : A →ₐ[k] A') : Forms k A →ₛₗ[(φ : A →+* A')] Forms k A' where
  toFun := map φ
  map_add' := map_add (map φ)
  map_smul' := map_smul φ

@[simp]
theorem mapₛₗ_apply (φ : A →ₐ[k] A') (x : Forms k A) : mapₛₗ φ x = map φ x :=
  rfl

/-- The formula on the words `da₁ ∧ ⋯ ∧ daₙ`. As a simp lemma this is covered by `map_word` and
`map_diff`, which reindex the family instead of the list. -/
theorem map_word_diff (φ : A →ₐ[k] A') (l : List A) :
    map φ (word (diff k) l) = word (diff k) (l.map φ) := by
  simp [word_map]

/-- The formula on the expressions `a₀ da₁ ∧ ⋯ ∧ daₙ`.

Blueprint: `thm:dr-dga`. -/
theorem map_smul_word (φ : A →ₐ[k] A') (a : A) (l : List A) :
    map φ (a • word (diff k) l) = φ a • word (diff k) (l.map φ) := by
  rw [map_smul, map_word_diff]

/-- The map on forms commutes with the differential: it is a chain map.

Blueprint: `thm:dr-dga`. -/
theorem map_d (φ : A →ₐ[k] A') (x : Forms k A) : map φ (d k x) = d k (map φ x) := by
  induction x using Forms.induction with
  | word a l =>
    rw [d_smul_word, map_mul, map_diff, map_word_diff, map_smul_word, d_smul_word]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The map on forms preserves degrees.

Blueprint: `thm:dr-dga`. -/
theorem map_mem_exteriorPower (φ : A →ₐ[k] A') {n : ℕ} {x : Forms k A}
    (hx : x ∈ ⋀[A]^n Ω[A⁄k]) : map φ x ∈ ⋀[A']^n Ω[A'⁄k] := by
  induction hx using Forms.induction_exteriorPower with
  | word a l hl =>
    rw [map_smul_word]
    exact smul_word_diff_mem_exteriorPower k _ (by simpa using hl)
  | add x _ y _ hx hy =>
    rw [map_add]
    exact add_mem hx hy

/-- The map on forms commutes with the grade involution, which is the sign `(-1)^p` in degree `p`.

Blueprint: `thm:dr-dga`. -/
@[simp]
theorem map_involute (φ : A →ₐ[k] A') (x : Forms k A) :
    map φ (CliffordAlgebra.involute x) = CliffordAlgebra.involute (map φ x) := by
  have key : (map φ).comp (CliffordAlgebra.involute.restrictScalars k) =
      (CliffordAlgebra.involute.restrictScalars k).comp (map φ) := by
    ext a <;> simp
  exact AlgHom.congr_fun key x

/-- The map on forms commutes with taking homogeneous components.

Blueprint: `thm:dr-dga`, since the map preserves degrees. -/
theorem coe_exteriorProj_map (φ : A →ₐ[k] A') (n : ℕ) (x : Forms k A) :
    (exteriorProj n (map φ x) : Forms k A') = map φ (exteriorProj n x : Forms k A) := by
  induction x using Forms.induction with
  | word a l =>
    have hx := smul_word_diff_mem_exteriorPower k a (rfl : l.length = l.length)
    by_cases h : l.length = n
    · subst h
      rw [exteriorProj_of_mem hx, exteriorProj_of_mem (map_mem_exteriorPower φ hx)]
    · rw [exteriorProj_of_mem_of_ne h hx, exteriorProj_of_mem_of_ne h (map_mem_exteriorPower φ hx)]
      simp
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]

/-- The identity induces the identity.

Blueprint: `thm:dr-dga`. -/
@[simp]
theorem map_id : map (AlgHom.id k A) = AlgHom.id k (Forms k A) := by
  ext <;> simp

/-- `map` respects composition, as an equation of algebra maps.

Blueprint: `thm:dr-dga`. -/
theorem map_comp (ψ : A' →ₐ[k] A'') (φ : A →ₐ[k] A') :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  ext <;> simp

/-- `map` respects composition.

Blueprint: `thm:dr-dga`. -/
@[simp]
theorem map_map (ψ : A' →ₐ[k] A'') (φ : A →ₐ[k] A') (x : Forms k A) :
    map ψ (map φ x) = map (ψ.comp φ) x := by
  rw [map_comp, AlgHom.comp_apply]

/-- The map on forms of an equivalence of algebras is an equivalence of algebras. This transports
forms between different presentations of the same algebra. -/
noncomputable def mapEquiv (e : A ≃ₐ[k] A') : Forms k A ≃ₐ[k] Forms k A' :=
  AlgEquiv.ofAlgHom (map e.toAlgHom) (map e.symm.toAlgHom)
    (by rw [← map_comp]; simp) (by rw [← map_comp]; simp)

@[simp]
theorem mapEquiv_apply (e : A ≃ₐ[k] A') (x : Forms k A) : mapEquiv e x = map e.toAlgHom x :=
  rfl

@[simp]
theorem mapEquiv_symm_apply (e : A ≃ₐ[k] A') (x : Forms k A') :
    (mapEquiv e).symm x = map e.symm.toAlgHom x :=
  rfl

section Tower

variable (k A) (S : Type*) [CommRing S] [Algebra k S] [Algebra A S] [IsScalarTower k A S]

/-- `exteriorMap` along `KaehlerDifferential.map` sends `da` to `d (algebraMap a)`. -/
theorem exteriorMap_diff (a : A) :
    exteriorMap S (KaehlerDifferential.map k k A S) (diff k a) = diff k (algebraMap A S a) :=
  (exteriorMap_ι S _ _).trans (congrArg (ι S) (KaehlerDifferential.map_D k k A S a))

/-- For an algebra `S` over `A`, the map on forms is the map of exterior algebras along
`KaehlerDifferential.map k k A S`. This is the bridge to the API of `DeRham/Exterior`, such as
`isBaseChange_exteriorMap` and `ker_exteriorMap`, which is stated for algebras rather than for
algebra maps. -/
theorem map_toAlgHom (x : Forms k A) :
    map (IsScalarTower.toAlgHom k A S) x = exteriorMap S (KaehlerDifferential.map k k A S) x := by
  induction x using Forms.induction with
  | word a l =>
    rw [map_smul_word, word_map, _root_.map_smul, map_word]
    simp only [exteriorMap_diff, IsScalarTower.coe_toAlgHom', algebraMap_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tower

/-! ### The maps in each degree -/

/-- The map on forms in degree `n`, as a `k`-linear map. This is `map φ` with its domain and
codomain restricted, by `coe_mapPower`. It is semilinear over `φ`, by `mapPower_smul`.

Blueprint: `thm:dr-dga`. -/
noncomputable def mapPower (φ : A →ₐ[k] A') (n : ℕ) : ⋀[A]^n Ω[A⁄k] →ₗ[k] ⋀[A']^n Ω[A'⁄k] :=
  LinearMap.codRestrict ((⋀[A']^n Ω[A'⁄k]).restrictScalars k)
    ((map φ).toLinearMap.comp ((⋀[A]^n Ω[A⁄k]).subtype.restrictScalars k))
    fun x => map_mem_exteriorPower φ x.2

@[simp]
theorem coe_mapPower (φ : A →ₐ[k] A') (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    (mapPower φ n x : Forms k A') = map φ (x : Forms k A) :=
  rfl

@[simp]
theorem mapPower_smul (φ : A →ₐ[k] A') (n : ℕ) (a : A) (x : ⋀[A]^n Ω[A⁄k]) :
    mapPower φ n (a • x) = φ a • mapPower φ n x :=
  Subtype.ext (map_smul φ a x)

/-- The map in each degree is a chain map.

Blueprint: `thm:dr-dga`. -/
theorem mapPower_powerD (φ : A →ₐ[k] A') (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    mapPower φ (n + 1) (powerD k A n x) = powerD k A' n (mapPower φ n x) :=
  Subtype.ext (map_d φ x)

@[simp]
theorem mapPower_id (n : ℕ) : mapPower (AlgHom.id k A) n = LinearMap.id :=
  LinearMap.ext fun x => Subtype.ext (by simp)

theorem mapPower_comp (ψ : A' →ₐ[k] A'') (φ : A →ₐ[k] A') (n : ℕ) :
    mapPower (ψ.comp φ) n = mapPower ψ n ∘ₗ mapPower φ n :=
  LinearMap.ext fun x => Subtype.ext (by simp)

/-- For an algebra `S` over `A`, the map in degree `n` is `powerMap` along
`KaehlerDifferential.map k k A S`. -/
theorem mapPower_toAlgHom (S : Type*) [CommRing S] [Algebra k S] [Algebra A S]
    [IsScalarTower k A S] (n : ℕ) (x : ⋀[A]^n Ω[A⁄k]) :
    mapPower (IsScalarTower.toAlgHom k A S) n x =
      powerMap S (KaehlerDifferential.map k k A S) n x :=
  Subtype.ext (map_toAlgHom k A S x)

end Forms

end OrlikSolomon.DeRham
