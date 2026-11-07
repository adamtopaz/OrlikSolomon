/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Cohomology.Geometric.Logarithms
public import OrlikSolomon.DeRham.Corollaries
public import OrlikSolomon.DeRham.Schemes.Affine

/-!
# The de Rham instance on smooth affine schemes

For a field `k` of characteristic zero, this file constructs
`OrlikSolomon.Geometric.DeRham.ordinaryTheory k`, a geometric ordinary theory on the domain
`aff k` of smooth affine schemes over `S = Spec k`, with `R = k`, `B = k[t, t⁻¹]` and
`ℬ w = k t^w`. It is the transport `ofAlgebraic (OrlikSolomon.DeRham.ordinaryTheory k)` of the
existing algebraic de Rham instance along global sections, as the blueprint prescribes, so all 22
fields come from `thm:geo-from-algebraic` and nothing is proved again. This file describes the
result in terms of the de Rham cohomology `Cohomology X` of `DeRham/Schemes/Affine`:

* `C(X) = B ⊗[k] H^•_dR(X/k)` (`objEquiv`), with `C(X)_{p, w} = t^w ⊗ H^p_dR(X/k)`
  (`mem_grading_iff`, `gradingEquiv`) and pullbacks `1 ⊗ f^*` (`pull_twistedClass`);
* on each affine pair `P`, the Gysin map and the residue are `t^w ⊗ y ↦ t^(w+1) ⊗ G_dR(y)` and
  `t^w ⊗ x ↦ t^(w-1) ⊗ r_dR(x)` (`gysin_twistedClass`, `residue_twistedClass`), where `G_dR` and
  `r_dR` (`gysin`, `residue`) are the maps of the global logarithmic sequence of the algebraic pair
  `Γ(P)`: `r_dR[ω + θ ∧ η] = [η|_D]` (`residue_mk_add_theta_mul`) and `G_dR[γ] = [dλ]` for `ρ λ = γ`
  (`gysin_mk_of_logResidue_eq`);
* the coefficients and the value at `S` are nonzero (`nontrivial_coefficients`,
  `nontrivialObjPoint`);
* `[u]_T = t ⊗ [du/u]` (`logClass_eq`).

## Implementation notes

As for the algebraic instance, `ordinaryTheory k` is a `def`, so that the generic lemmas about a
geometric theory `T` fire on it. Its value `(ordinaryTheory k).obj X` is
`TwistedCohomology k Γ(X, 𝒪_X)` only at default transparency, so compute with
`twistedClass w c`, the class `t^w ⊗ c` typed in `(ordinaryTheory k).obj X`.

The hypotheses `[Field k] [CharZero k]` enter only through the algebraic instance, which uses them
to invert positive integers for integration and pole reduction. No smoothness, connectedness,
flatness or nonemptiness hypothesis is added.

The blueprint also compares the Gysin and residue maps with those of the global sections of the
sheaf logarithmic sequence of `thm:geo-log-sheaves`. That theorem is #117, and this file does not
state the comparison: here `G_dR` and `r_dR` are the maps of the algebraic logarithmic sequence of
`Γ(X, 𝒪_X)`, on which the blueprint's proof reduces the comparison.

## Blueprint

`thm:geo-dr-instance`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct LaurentPolynomial
open LaurentPolynomial (T)
open OrlikSolomon.DeRham

universe u

namespace OrlikSolomon.Geometric.DeRham

variable (k : Type u) [Field k] [CharZero k]

/-- **The nonzero geometric de Rham instance.** For a field `k` of characteristic zero, de Rham
cohomology with Laurent coefficients is a geometric ordinary theory on smooth affine schemes over
`S = Spec k`, with `R = k`, `B = k[t, t⁻¹]` and `ℬ w = k t^w`. It is the transport
`ofAlgebraic (OrlikSolomon.DeRham.ordinaryTheory k)` of the algebraic instance
(`ordinaryTheory_eq`), which constructs all 22 fields. Its value is
`C(X) = B ⊗[k] H^•_dR(X/k)`, by `objEquiv`, with `t^w ⊗ H^p_dR(X/k)` in bidegree `(p, w)`, by
`mem_grading_iff`; its Gysin map and residue are those of de Rham cohomology multiplied by `t`
and `t⁻¹`, by `gysin_twistedClass` and `residue_twistedClass`; it is not a zero theory, by
`nontrivialObjPoint`; and its logarithmic classes are `[u]_T = t ⊗ [du/u]`, by `logClass_eq`.

Blueprint: `thm:geo-dr-instance`. -/
@[implicit_reducible]
def ordinaryTheory : OrdinaryTheory (SmoothDomain.aff k) (laurentGrading k) :=
  OrdinaryTheory.ofAlgebraic (OrlikSolomon.DeRham.ordinaryTheory k)

/-- The geometric instance is obtained by applying `thm:geo-from-algebraic` to the algebraic
instance. Not a `simp` lemma. -/
lemma ordinaryTheory_eq :
    ordinaryTheory k = OrdinaryTheory.ofAlgebraic (OrlikSolomon.DeRham.ordinaryTheory k) :=
  rfl

omit [CharZero k] in
/-- The coefficient ring `k[t, t⁻¹]` of the instance is nonzero.

Blueprint: `thm:geo-dr-instance`. -/
theorem nontrivial_coefficients : Nontrivial k[T;T⁻¹] :=
  OrlikSolomon.DeRham.nontrivial_coefficients k

/-- **The value of the instance at `S` is nonzero**, so it is not a zero theory. Nothing says that
`C(X)` is nonzero for every `X`: it is zero for the empty scheme.

Blueprint: `thm:geo-dr-instance`. -/
instance nontrivialObjPoint : Nontrivial ((ordinaryTheory k).obj (SmoothDomain.aff k).point) :=
  have := nontrivial_coefficients k
  (ordinaryTheory k).bijective_algebraMap_point.injective.nontrivial

variable {k} {X Y : (SmoothDomain.aff k).Obj}

/-! ### The value `B ⊗ H^•_dR(X/k)` -/

section TwistedClass

/-- The class `t^w ⊗ c` of `C(X) = k[t, t⁻¹] ⊗[k] H^•_dR(X/k)`, for a de Rham class `c` of `X`. It
is typed in `(ordinaryTheory k).obj X`, so that `simp` computes the structure of the instance on
it. A class of bidegree `(p, w)` is `twistedClass w c` for a unique `c ∈ H^p_dR(X/k)`, by
`mem_grading_iff` and `twistedClass_inj`.

Blueprint: `thm:geo-dr-instance`. -/
def twistedClass (w : ℤ) : Cohomology X →ₗ[k] (ordinaryTheory k).obj X :=
  OrlikSolomon.DeRham.twistedClass (A := (affineGlobalSectionsFunctor k).obj (op X)) w

/-- The class `t^w ⊗ c` is `T w ⊗ₜ c`. Not a `simp` lemma, since its two sides have different
types. -/
lemma twistedClass_apply (w : ℤ) (c : Cohomology X) :
    twistedClass w c = (T w ⊗ₜ[k] c : TwistedCohomology k (globalSections X.obj)) :=
  rfl

variable (X) in
/-- **`C(X) = B ⊗[k] H^•_dR(X/k)`**: the value of the instance is the tensor product of the
coefficients with de Rham cohomology, as a `B`-algebra, with the coefficients on the left.

Blueprint: `thm:geo-dr-instance`. -/
def objEquiv : (ordinaryTheory k).obj X ≃ₐ[k[T;T⁻¹]] k[T;T⁻¹] ⊗[k] Cohomology X :=
  AlgEquiv.refl

@[simp]
lemma objEquiv_twistedClass (w : ℤ) (c : Cohomology X) :
    objEquiv X (twistedClass w c) = T w ⊗ₜ[k] c :=
  rfl

@[simp]
lemma objEquiv_symm_tmul (w : ℤ) (c : Cohomology X) :
    (objEquiv X).symm (T w ⊗ₜ[k] c) = twistedClass w c :=
  rfl

/-- **`C(X)_{p, w} = t^w ⊗ H^p_dR(X/k)`**: a class of bidegree `(p, w)` is `t^w ⊗ c` with `c` of
degree `p`.

Blueprint: `thm:geo-dr-instance`. -/
theorem mem_grading_iff {p w : ℤ} {x : (ordinaryTheory k).obj X} :
    x ∈ (ordinaryTheory k).grading X (p, w) ↔
      ∃ c ∈ OrlikSolomon.DeRham.Cohomology.grading k (globalSections X.obj) p,
        twistedClass w c = x :=
  OrlikSolomon.DeRham.mem_grading_ordinaryTheory_iff

/-- In a natural degree `n`, a class of bidegree `(n, w)` is `t^w ⊗ c` with `c ∈ H^n_dR(X/k)`. -/
theorem mem_grading_natCast_iff {n : ℕ} {w : ℤ} {x : (ordinaryTheory k).obj X} :
    x ∈ (ordinaryTheory k).grading X ((n : ℤ), w) ↔
      ∃ c ∈ Cohomology.degree X n, twistedClass w c = x := by
  rw [mem_grading_iff, OrlikSolomon.DeRham.Cohomology.grading_natCast]

@[simp]
theorem twistedClass_mem_grading_iff {p w : ℤ} {c : Cohomology X} :
    twistedClass w c ∈ (ordinaryTheory k).grading X (p, w) ↔
      c ∈ OrlikSolomon.DeRham.Cohomology.grading k (globalSections X.obj) p :=
  OrlikSolomon.DeRham.twistedClass_mem_grading_iff

/-- In a natural degree, `t^w ⊗ c` has bidegree `(n, w)` exactly when `c ∈ H^n_dR(X/k)`. -/
theorem twistedClass_mem_grading_natCast_iff {n : ℕ} {w : ℤ} {c : Cohomology X} :
    twistedClass w c ∈ (ordinaryTheory k).grading X ((n : ℤ), w) ↔ c ∈ Cohomology.degree X n :=
  OrlikSolomon.DeRham.twistedClass_mem_grading_natCast_iff

variable (X) in
/-- The piece of bidegree `(n, w)` is `H^n_dR(X/k)`, by `c ↦ t^w ⊗ c`.

Blueprint: `thm:geo-dr-instance`. -/
def gradingEquiv (n : ℕ) (w : ℤ) :
    Cohomology.degree X n ≃ₗ[k] (ordinaryTheory k).grading X ((n : ℤ), w) :=
  TwistedCohomology.degreeEquiv k (globalSections X.obj) n w

@[simp]
lemma coe_gradingEquiv_apply (n : ℕ) (w : ℤ) (c : Cohomology.degree X n) :
    (gradingEquiv X n w c : (ordinaryTheory k).obj X) = twistedClass w (c : Cohomology X) :=
  rfl

@[simp]
theorem twistedClass_inj {w : ℤ} {c c' : Cohomology X} :
    twistedClass w c = twistedClass w c' ↔ c = c' :=
  OrlikSolomon.DeRham.twistedClass_inj

@[simp]
theorem twistedClass_eq_zero {w : ℤ} {c : Cohomology X} : twistedClass w c = 0 ↔ c = 0 :=
  OrlikSolomon.DeRham.twistedClass_eq_zero

/-- Removing the power of `t` from `t^w ⊗ c` gives `c`. -/
@[simp]
theorem evalOne_twistedClass (w : ℤ) (c : Cohomology X) :
    TwistedCohomology.evalOne k (globalSections X.obj) (twistedClass w c) = c :=
  TwistedCohomology.evalOne_T_tmul w c

/-- **Pullbacks are `1 ⊗ f^*`.** -/
@[simp]
theorem pull_twistedClass (f : X ⟶ Y) (w : ℤ) (c : Cohomology Y) :
    (ordinaryTheory k).pull f (twistedClass w c) = twistedClass w (Cohomology.pull f c) :=
  rfl

/-- Weights add and de Rham classes multiply. -/
@[simp]
theorem twistedClass_mul_twistedClass (w v : ℤ) (c c' : Cohomology X) :
    twistedClass w c * twistedClass v c' = twistedClass (w + v) (c * c') :=
  TwistedCohomology.T_tmul_mul_T_tmul w v c c'

/-- The unit is `1 ⊗ 1`. -/
@[simp]
theorem twistedClass_zero_one : twistedClass 0 (1 : Cohomology X) = 1 :=
  OrlikSolomon.DeRham.twistedClass_zero_one

/-- The image of `t^w` under `B → C(X)` is `t^w ⊗ 1`. -/
theorem algebraMap_T (w : ℤ) :
    algebraMap k[T;T⁻¹] ((ordinaryTheory k).obj X) (T w) = twistedClass w 1 :=
  rfl

/-- The coefficient `t^v` adds `v` to the weight. -/
@[simp]
theorem T_smul_twistedClass (v w : ℤ) (c : Cohomology X) :
    (T v : k[T;T⁻¹]) • twistedClass w c = twistedClass (v + w) c :=
  TwistedCohomology.T_smul_T_tmul v w c

end TwistedClass

/-! ### Gysin and residue on affine pairs -/

section Pairs

variable (P : DivisorPair (SmoothDomain.aff k))

/-- The de Rham Gysin map `G_dR : H^•_dR(D/k) → H^•_dR(X/k)` of an affine pair `P = (X, D, U, f)`:
the Gysin map of the global logarithmic sequence of the algebraic pair `Γ(P)` of global sections,
`G_dR[γ] = [dλ]` for a logarithmic form `λ` with residue `γ` (`gysin_mk_of_logResidue_eq`).

Blueprint: `thm:geo-dr-instance`. -/
def gysin : Cohomology P.closed →ₗ[k] Cohomology P.ambient :=
  OrlikSolomon.DeRham.gysin (A := (DivisorPair.globalSections P).ambient)
    (S := (DivisorPair.globalSections P).closed) (DivisorPair.globalSections P).compl
    (DivisorPair.globalSections P).isSmoothPrincipalPair

/-- The de Rham residue `r_dR : H^•_dR(U/k) → H^•_dR(D/k)` of an affine pair `P = (X, D, U, f)`:
the residue of the global logarithmic sequence of the algebraic pair `Γ(P)` of global sections,
`r_dR[ω + θ ∧ η] = [η|_D]` for `θ = df/f` (`residue_mk_add_theta_mul`).

Blueprint: `thm:geo-dr-instance`. -/
def residue : Cohomology P.compl →ₗ[k] Cohomology P.closed :=
  OrlikSolomon.DeRham.residue (A := (DivisorPair.globalSections P).ambient)
    (S := (DivisorPair.globalSections P).closed) (DivisorPair.globalSections P).compl
    (isUnit_natCast_add_one k)
    (DivisorPair.globalSections P).isSmoothPrincipalPair

/-- **The Gysin map of the instance** is `t^w ⊗ y ↦ t^(w+1) ⊗ G_dR(y)`.

Blueprint: `thm:geo-dr-instance`. -/
@[simp]
theorem gysin_twistedClass (w : ℤ) (c : Cohomology P.closed) :
    (ordinaryTheory k).gysin P (twistedClass w c) = twistedClass (w + 1) (gysin P c) :=
  OrlikSolomon.DeRham.gysin_twistedClass (DivisorPair.globalSections P) w c

/-- **The residue of the instance** is `t^w ⊗ x ↦ t^(w-1) ⊗ r_dR(x)`.

Blueprint: `thm:geo-dr-instance`. -/
@[simp]
theorem residue_twistedClass (w : ℤ) (c : Cohomology P.compl) :
    (ordinaryTheory k).residue P (twistedClass w c) = twistedClass (w - 1) (residue P c) :=
  OrlikSolomon.DeRham.residue_twistedClass (DivisorPair.globalSections P) w c

/-- `r_dR[λ] = [ρ λ]` for a closed logarithmic form `λ` on `Γ(U, 𝒪_U)`, the residue of the global
logarithmic sequence of `Γ(P)`.

Blueprint: `thm:geo-dr-instance`. -/
theorem residue_mk_of_mem_logForms {x : Forms k (DivisorPair.globalSections P).compl}
    (hx : x ∈ logForms k (DivisorPair.globalSections P).eqn (DivisorPair.globalSections P).compl)
    (hd : d k x = 0) :
    residue P (OrlikSolomon.DeRham.Cohomology.mk x hd) =
      OrlikSolomon.DeRham.Cohomology.mk
        (logResidue (DivisorPair.globalSections P).compl
          (DivisorPair.globalSections P).isSmoothPrincipalPair ⟨x, hx⟩)
        (OrlikSolomon.DeRham.d_logResidue_eq_zero _
          (OrlikSolomon.DeRham.logD_eq_zero_iff.2 hd)) :=
  OrlikSolomon.DeRham.residue_mk_of_mem_logForms _ _ hx hd

/-- `r_dR[ω + θ ∧ η] = [η|_D]` for a closed logarithmic form, with `θ = df/f`: there is no further
sign.

Blueprint: `thm:geo-dr-instance`. -/
theorem residue_mk_add_theta_mul (ω η : Forms k (DivisorPair.globalSections P).ambient)
    (hd : d k (Forms.map (IsScalarTower.toAlgHom k (DivisorPair.globalSections P).ambient
        (DivisorPair.globalSections P).compl) ω +
      theta k (DivisorPair.globalSections P).eqn (DivisorPair.globalSections P).compl *
        Forms.map (IsScalarTower.toAlgHom k (DivisorPair.globalSections P).ambient
          (DivisorPair.globalSections P).compl) η) = 0) :
    residue P (OrlikSolomon.DeRham.Cohomology.mk _ hd) =
      OrlikSolomon.DeRham.Cohomology.mk
        (Forms.map (SmoothAlg.algHom (DivisorPair.globalSections P).i) η)
        (OrlikSolomon.DeRham.logResidue_logMk (T := (DivisorPair.globalSections P).compl)
          (DivisorPair.globalSections P).isSmoothPrincipalPair (ω, η) ▸
          OrlikSolomon.DeRham.d_logResidue_eq_zero _
            (OrlikSolomon.DeRham.logD_eq_zero_iff.2 hd)) :=
  OrlikSolomon.DeRham.residue_mk_add_theta_mul _ _ ω η hd

omit [CharZero k] in
/-- `G_dR[γ] = [dλ]`, for any logarithmic form `λ` on `Γ(U, 𝒪_U)` with residue `γ`, with `dλ` the
image of the regular form `ω` on `Γ(X, 𝒪_X)`.

Blueprint: `thm:geo-dr-instance`. -/
theorem gysin_mk_of_logResidue_eq {γ : Forms k (DivisorPair.globalSections P).closed}
    (hγ : d k γ = 0)
    {x : logForms k (DivisorPair.globalSections P).eqn (DivisorPair.globalSections P).compl}
    (hx : logResidue (DivisorPair.globalSections P).compl
      (DivisorPair.globalSections P).isSmoothPrincipalPair x = γ)
    {ω : Forms k (DivisorPair.globalSections P).ambient}
    (hω : ofRegular k (DivisorPair.globalSections P).eqn (DivisorPair.globalSections P).compl ω =
      logD k (DivisorPair.globalSections P).eqn (DivisorPair.globalSections P).compl x) :
    gysin P (OrlikSolomon.DeRham.Cohomology.mk γ hγ) =
      OrlikSolomon.DeRham.Cohomology.mk ω
        (OrlikSolomon.DeRham.d_eq_zero_of_ofRegular_eq_logD
          (DivisorPair.globalSections P).isSmoothPrincipalPair hω) :=
  OrlikSolomon.DeRham.gysin_mk_of_logResidue_eq _ hγ hx hω

end Pairs

/-! ### Logarithmic classes -/

/-- **`[u]_T = t ⊗ [du/u]`**: the logarithmic class of a global unit `u` of a smooth affine scheme
is `t` times the de Rham class of the closed form `du/u`. Not a `simp` lemma, so that the generic
lemmas about `OrdinaryTheory.logClass` fire on the instance.

Blueprint: `thm:geo-dr-instance`. -/
theorem logClass_eq (u : Γ(X.obj.left, ⊤)ˣ) :
    (ordinaryTheory k).logClass u = twistedClass 1 (dlogClass k (A := globalSections X.obj) u) :=
  (OrdinaryTheory.ofAlgebraic_logClass (OrlikSolomon.DeRham.ordinaryTheory k) u).trans
    (OrlikSolomon.DeRham.ordinaryTheory_logClass
      (A := (affineGlobalSectionsFunctor k).obj (op X)) u)

/-- Removing the power of `t` from the logarithmic class of `u` gives `[du/u]`. -/
@[simp]
theorem evalOne_logClass (u : Γ(X.obj.left, ⊤)ˣ) :
    TwistedCohomology.evalOne k (globalSections X.obj) ((ordinaryTheory k).logClass u) =
      dlogClass k (A := globalSections X.obj) u := by
  rw [logClass_eq, evalOne_twistedClass]

end OrlikSolomon.Geometric.DeRham
