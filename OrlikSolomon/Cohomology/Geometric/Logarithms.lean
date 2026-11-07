/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
module

public import OrlikSolomon.Cohomology.Geometric.Transport
public import OrlikSolomon.Cohomology.Logarithms

/-!
# Logarithmic classes on schemes and the product with `𝔾ₘ`

For a geometric ordinary theory `T` on an admissible domain `D`, this file constructs the
logarithmic class `[u] ∈ C(X)_{1,1}` of a global unit `u` of every object `X` of `D`, affine or
not, proves its identities, and proves the decomposition of the cohomology of `X ×_S 𝔾ₘ`.
Blueprint: `def:geo-log`, `thm:geo-log-laws`, `thm:geo-gm-product`.

The class `τ` of `𝔾ₘ` is the class of `lem:gm` for the algebraic theory `T.toAlgebraic`, on
`Spec k[t, t⁻¹] = 𝔾ₘ`, and `[u] = û^* τ` for the map `û : X ⟶ 𝔾ₘ` of `u` given by
`unitsEquivHomGm`. Every identity on all of `D` is the pullback of an identity of the algebraic
theory on one of the affine schemes `S`, `𝔾ₘ` and `𝔾ₘ²`, or a consequence of the axioms applied to
a standard pair. So no statement here needs `X` to be affine.

## Main definitions

* `SmoothDomain.gmHom u`: the map `û : X ⟶ 𝔾ₘ` of a global unit, in a domain.
* `SmoothDomain.prodGmCoord X`: the coordinate `z`, a global unit of `X ×_S 𝔾ₘ`, which is the
  equation of the standard pair (`SmoothDomain.standardPair_eqnUnit`).
* `OrdinaryTheory.tau`: the class `τ ∈ C(𝔾ₘ)_{1,1}`.
* `OrdinaryTheory.logClass u`: the logarithmic class `[u] = û^* τ`.
* `OrdinaryTheory.gmProductEquiv X`: the equivalence `C(X) ⊕ C(X) ≃ C(X ×_S 𝔾ₘ)`,
  `(a, b) ↦ π^* a + [z] π^* b`.

## Main results

* `def:geo-log`: `tau_mem_grading`, `standardResidue_pull_prodGmSnd_tau`, `eq_tau_of_mem_grading`,
  `existsUnique_tau`, `logClass_mem_grading`.
* `thm:geo-log-laws`: `pull_logClass`, `logClass_eq_zero_of_coe_eq_algebraMap`,
  `logClass_mul_self`, `logClass_mul`, `logClass_inv`, `residue_logClass_eqnUnit` and
  `residue_logClass_eqnUnit_mul`, for every pair. The comparison with the old classes under affine
  duality is `pull_toAlgebraic_logClass` and `toAlgebraic_logClass`, for `T.toAlgebraic`, and
  `ofAlgebraic_logClass`, for the transport of an algebraic theory.
* `thm:geo-gm-product`: `gmProductEquiv`, with `gmProductEquiv_apply`, `gmProductEquiv_symm_apply`,
  its degrees in `gmProductEquiv_mem_grading_iff` and its naturality in
  `pull_prodGmMap_gmProductEquiv`.

## Implementation notes

**The objects.** `τ` lives on the object `D.gm` of the domain, which is the same scheme as
`D.spec (SmoothAlg.gm k)`, where the algebraic theory has its class; `SmoothDomain.specGmIso`
records this. The standard pair of the base has open part `S ×_S 𝔾ₘ`, so the normalization of `τ`
reads `r(p₂^* τ) = 1` for the second projection `p₂ = SmoothDomain.prodGmSnd`.

**Multiplicativity.** As in the blueprint, `[uv] = [u] + [v]` is the pullback of the old identity
on `𝔾ₘ² = Spec k[s, s⁻¹][t, t⁻¹]` along the map of `(u, v)`. No Künneth theorem is involved.

**Squares and constants.** `[u]² = 0` is the pullback of `τ² = 0`, which comes from the vanishing
of `C(𝔾ₘ)` in degree two, not from graded commutativity, so it holds with coefficients in `ℤ/2`. A
constant unit `c ∈ kˣ` has a map to `𝔾ₘ` factoring through the base `S`, whose cohomology vanishes
in degree one. No rational point of any scheme is used.

**For consumers.** To compute a class pulled back along a comparison `g : X ⟶ Spec A`, such as the
comparison of an arrangement complement with the spectrum of its coordinate ring, use
`pull_toAlgebraic_logClass`, whose hypothesis is an equation of global sections. Equations of
functions are stated as equations of global sections; recover equations of units with `Units.ext`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

universe u v w z

namespace OrlikSolomon.Geometric

variable {k : Type u} [CommRing k]

/-! ### Maps to `𝔾ₘ` in a domain -/

namespace SmoothDomain

variable (D : SmoothDomain k)

/-- The map `û : X ⟶ 𝔾ₘ` of a global unit `u` of an object `X` of a domain: the unique morphism
pulling the coordinate of `𝔾ₘ` back to `u` (`unitsEquivHomGm`). Blueprint: `thm:geo-units`. -/
def gmHom {X : D.Obj} (u : Γ(X.obj.left, ⊤)ˣ) : X ⟶ D.gm :=
  ObjectProperty.homMk (unitsEquivHomGm X.obj u)

/-- The second projection `X ×_S 𝔾ₘ → 𝔾ₘ`, in a domain. -/
def prodGmSnd (X : D.Obj) : D.prodGm X ⟶ D.gm :=
  ObjectProperty.homMk (snd X.obj (Geometric.gm k))

/-- The coordinate `z` of `X ×_S 𝔾ₘ`, a global unit: the pullback of the coordinate of `𝔾ₘ` along
the second projection. It is the equation of the standard pair of `X` on its open part
(`standardPair_eqnUnit`). -/
def prodGmCoord (X : D.Obj) : Γ((D.prodGm X).obj.left, ⊤)ˣ :=
  homGmEquiv (D.prodGm X).obj (D.prodGmSnd X).hom

/-- `Spec k[t, t⁻¹]`, the object at which the algebraic theory of a geometric theory has its class
`τ`, is the multiplicative group of the domain. The two are the same scheme. -/
def specGmIso : D.spec (SmoothAlg.gm k) ≅ D.gm := ObjectProperty.isoMk _ (Iso.refl _)

variable {D}

@[simp] lemma gmHom_hom {X : D.Obj} (u : Γ(X.obj.left, ⊤)ˣ) :
    (D.gmHom u).hom = unitsEquivHomGm X.obj u := rfl

@[simp] lemma prodGmSnd_hom (X : D.Obj) : (D.prodGmSnd X).hom = snd X.obj (Geometric.gm k) :=
  rfl

lemma coe_prodGmCoord (X : D.Obj) :
    (D.prodGmCoord X : Γ((D.prodGm X).obj.left, ⊤)) =
      (snd X.obj (Geometric.gm k)).left.appTop (gmCoord k) :=
  rfl

/-- `û` pulls the coordinate of `𝔾ₘ` back to `u`. -/
lemma gmHom_appTop_gmCoord {X : D.Obj} (u : Γ(X.obj.left, ⊤)ˣ) :
    (D.gmHom u).hom.left.appTop (gmCoord k : Γ((Geometric.gm k).left, ⊤)) = u :=
  unitsEquivHomGm_appTop_gmCoord u

/-- Two maps to `𝔾ₘ` agree when they pull its coordinate back to the same function. -/
lemma gm_hom_ext {X : D.Obj} {f g : X ⟶ D.gm}
    (h : f.hom.left.appTop (gmCoord k : Γ((Geometric.gm k).left, ⊤)) =
      g.hom.left.appTop (gmCoord k : Γ((Geometric.gm k).left, ⊤))) : f = g :=
  ObjectProperty.hom_ext _ (hom_ext_gm h)

/-- Naturality of `û`: `\widehat{g^* u} = û ∘ g`. Blueprint: `thm:geo-units`. -/
@[reassoc (attr := simp)]
lemma comp_gmHom {X Y : D.Obj} (g : X ⟶ Y) (u : Γ(Y.obj.left, ⊤)ˣ) :
    g ≫ D.gmHom u = D.gmHom (Units.map g.hom.left.appTop.hom u) :=
  ObjectProperty.hom_ext _ (unitsEquivHomGm_comp g.hom u).symm

/-- The map of the coordinate of `X ×_S 𝔾ₘ` is the second projection. -/
@[simp] lemma gmHom_prodGmCoord (X : D.Obj) : D.gmHom (D.prodGmCoord X) = D.prodGmSnd X := by
  apply gm_hom_ext
  rw [gmHom_appTop_gmCoord, coe_prodGmCoord, prodGmSnd_hom]

/-- The equation of the standard pair of `X`, as a unit on its open part, is the coordinate of
`X ×_S 𝔾ₘ`. -/
lemma standardPair_eqnUnit (X : D.Obj) :
    (DivisorPair.standardPair D X).eqnUnit = D.prodGmCoord X :=
  Units.ext ((DivisorPair.coe_standardPair_eqnUnit X).trans (coe_prodGmCoord X).symm)

@[reassoc (attr := simp)]
lemma oneSection_prodGmFst (X : D.Obj) : D.oneSection X ≫ D.prodGmFst X = 𝟙 X :=
  ObjectProperty.hom_ext _ (Geometric.oneSection_fst X.obj)

@[reassoc (attr := simp)]
lemma zeroSection_prodAffineLineFst (X : D.Obj) :
    D.zeroSection X ≫ D.prodAffineLineFst X = 𝟙 X :=
  ObjectProperty.hom_ext _ (Geometric.zeroSection_fst X.obj)

@[reassoc (attr := simp)]
lemma prodGmToProdAffineLine_prodAffineLineFst (X : D.Obj) :
    D.prodGmToProdAffineLine X ≫ D.prodAffineLineFst X = D.prodGmFst X :=
  ObjectProperty.hom_ext _ (whiskerLeft_fst _ _)

/-- The section `z = 1` is the map of the unit `1` on the second factor. -/
@[reassoc (attr := simp)]
lemma oneSection_prodGmSnd (X : D.Obj) : D.oneSection X ≫ D.prodGmSnd X = D.gmHom 1 :=
  ObjectProperty.hom_ext _ (show Geometric.oneSection X.obj ≫ snd X.obj (Geometric.gm k) =
    unitsEquivHomGm X.obj 1 from lift_snd _ _)

@[reassoc (attr := simp)]
lemma prodGmMap_prodGmFst {X Y : D.Obj} (g : X ⟶ Y) :
    D.prodGmMap g ≫ D.prodGmFst Y = D.prodGmFst X ≫ g :=
  ObjectProperty.hom_ext _ (show g.hom ▷ Geometric.gm k ≫ fst Y.obj (Geometric.gm k) =
    fst X.obj (Geometric.gm k) ≫ g.hom from whiskerRight_fst _ _)

@[reassoc (attr := simp)]
lemma prodGmMap_prodGmSnd {X Y : D.Obj} (g : X ⟶ Y) :
    D.prodGmMap g ≫ D.prodGmSnd Y = D.prodGmSnd X :=
  ObjectProperty.hom_ext _ (show g.hom ▷ Geometric.gm k ≫ snd Y.obj (Geometric.gm k) =
    snd X.obj (Geometric.gm k) from whiskerRight_snd _ _)

/-- The section `z = 1` pulls the coordinate of `X ×_S 𝔾ₘ` back to `1`. -/
@[simp] lemma map_oneSection_prodGmCoord (X : D.Obj) :
    (Units.map (D.oneSection X).hom.left.appTop.hom (D.prodGmCoord X) : Γ(X.obj.left, ⊤)ˣ) = 1 := by
  have h : D.gmHom (X := X) (Units.map (D.oneSection X).hom.left.appTop.hom (D.prodGmCoord X)) =
      D.gmHom 1 := by
    rw [← comp_gmHom, gmHom_prodGmCoord, oneSection_prodGmSnd]
  have h' := congrArg (fun f ↦ f.hom.left.appTop (gmCoord k : Γ((Geometric.gm k).left, ⊤))) h
  simp only [gmHom_appTop_gmCoord] at h'
  exact Units.ext h'

/-- `Spec k[t, t⁻¹] ≅ 𝔾ₘ` pulls the coordinate of `𝔾ₘ` back to the variable `t`. -/
lemma specGmIso_hom_appTop_gmCoord :
    D.specGmIso.hom.hom.left.appTop (gmCoord k : Γ((Geometric.gm k).left, ⊤)) =
      (Scheme.ΓSpecIso (.of (SmoothAlg.gm k))).inv
        (SmoothAlg.laurentT (SmoothAlg.point k) : SmoothAlg.gm k) :=
  rfl

/-- Under `Spec`, the map `SmoothAlg.gmHom u` of a unit `u` of a smooth algebra `A`, followed by
`Spec k[t, t⁻¹] ≅ 𝔾ₘ`, is the map of the global unit given by `u`; this holds after composing with
any `g : X ⟶ Spec A`. -/
lemma comp_specFunctor_map_gmHom_comp_specGmIso_hom {X : D.Obj} {A : SmoothAlg.{u} k}
    (g : X ⟶ D.spec A) (u : Aˣ) {v : Γ(X.obj.left, ⊤)ˣ}
    (hv : (v : Γ(X.obj.left, ⊤)) = g.hom.left.appTop ((Scheme.ΓSpecIso (.of A)).inv u)) :
    g ≫ (D.specFunctor.map (SmoothAlg.gmHom u)).unop ≫ D.specGmIso.hom = D.gmHom v := by
  apply gm_hom_ext
  rw [gmHom_appTop_gmCoord, hv, appTop_comp_apply, appTop_comp_apply,
    specGmIso_hom_appTop_gmCoord]
  refine congrArg _ ((specMap_left_appTop_ΓSpecIso_inv (SmoothAlg.gmHom u).hom _).trans ?_)
  exact congrArg _ (SmoothAlg.gmHom_laurentT u)

/-- The second projection of `Spec k ×_S 𝔾ₘ`, after `Spec k[t, t⁻¹] ≅ Spec k ×_S 𝔾ₘ`, is
`Spec k[t, t⁻¹] ≅ 𝔾ₘ`. -/
lemma specLaurentIso_hom_prodGmSnd :
    (D.specLaurentIso (SmoothAlg.point k)).hom ≫ D.prodGmSnd (D.spec (SmoothAlg.point k)) =
      D.specGmIso.hom := by
  apply gm_hom_ext
  rw [appTop_comp_apply, specGmIso_hom_appTop_gmCoord]
  exact specLaurentIso_hom_appTop_snd_gmCoord (SmoothAlg.point k).obj

end SmoothDomain

namespace OrdinaryTheory

variable {R : Type v} [CommRing R] {B : Type w} [CommRing B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {D : SmoothDomain k}
  (T : OrdinaryTheory.{u, v, w, z} D ℬ)

/-! ### The class `τ` of `𝔾ₘ` -/

section Tau

/-- The standard residue of the algebraic theory at the point, on `Spec k[t, t⁻¹] ≅ 𝔾ₘ`, is the
geometric standard residue of the base, through `Spec k ≅ S`. -/
lemma toAlgebraic_stdResidue_point (x : T.obj D.gm) :
    T.toAlgebraic.stdResidue (SmoothAlg.point k) (T.pull D.specGmIso.hom x) =
      T.pull D.specPointIso.hom
        (T.standardResidue D.point (T.pull (D.prodGmSnd D.point) x)) := by
  have h := T.residue_pull (DivisorPair.standardPairMap D.specPointIso.hom)
    (T.pull (D.prodGmSnd D.point) x)
  rw [DivisorPair.standardPairMap_compl, DivisorPair.standardPairMap_closed, residue_standardPair,
    residue_standardPair] at h
  rw [← h, ← pull_comp, SmoothDomain.prodGmMap_prodGmSnd, ← toAlgebraic_standardResidue,
    ← pull_comp, SmoothDomain.specLaurentIso_hom_prodGmSnd]

/-- The class `τ ∈ C(𝔾ₘ)`: the class of `lem:gm` for the algebraic theory `T.toAlgebraic`, on
`Spec k[t, t⁻¹] = 𝔾ₘ`. It has degree `(1, 1)` (`tau_mem_grading`) and residue `1` in the standard
pair of the base (`standardResidue_pull_prodGmSnd_tau`), and it is the unique such class
(`eq_tau_of_mem_grading`). Blueprint: `def:geo-log`. -/
def tau : T.obj D.gm := T.pull D.specGmIso.inv T.toAlgebraic.tau

/-- On `Spec k[t, t⁻¹]`, `τ` is the class of the algebraic theory. Blueprint: `def:geo-log`. -/
lemma pull_specGmIso_hom_tau : T.pull D.specGmIso.hom T.tau = T.toAlgebraic.tau := by
  rw [tau, ← pull_comp, Iso.hom_inv_id, pull_id]

/-- `τ` has degree `(1, 1)`. Blueprint: `def:geo-log`. -/
lemma tau_mem_grading : T.tau ∈ T.grading D.gm (1, 1) :=
  T.pull_mem_grading _ T.toAlgebraic.tau_mem_grading

/-- `τ` has residue `1` in the standard pair of the base. Blueprint: `def:geo-log`. -/
@[simp] lemma standardResidue_pull_prodGmSnd_tau :
    T.standardResidue D.point (T.pull (D.prodGmSnd D.point) T.tau) = 1 := by
  apply (T.pullIso D.specPointIso).injective
  rw [pullIso_apply, ← toAlgebraic_stdResidue_point, pull_specGmIso_hom_tau,
    OrlikSolomon.OrdinaryTheory.stdResidue_tau, map_one]

/-- `τ` is the unique class of degree `(1, 1)` with residue `1` in the standard pair of the base,
because the old class is. Blueprint: `def:geo-log`. -/
theorem eq_tau_of_mem_grading {x : T.obj D.gm} (hx : x ∈ T.grading D.gm (1, 1))
    (hr : T.standardResidue D.point (T.pull (D.prodGmSnd D.point) x) = 1) : x = T.tau := by
  have hy : T.pull D.specGmIso.hom x = T.toAlgebraic.tau :=
    T.toAlgebraic.eq_tau_of_mem_grading (T.pull_mem_grading _ hx)
      (by rw [toAlgebraic_stdResidue_point, hr, map_one])
  rw [tau, ← hy, ← pull_comp, Iso.inv_hom_id, pull_id]

/-- There is a unique class of degree `(1, 1)` on `𝔾ₘ` with residue `1` in the standard pair of the
base. Blueprint: `def:geo-log`. -/
theorem existsUnique_tau : ∃! τ : T.obj D.gm, τ ∈ T.grading D.gm (1, 1) ∧
    T.standardResidue D.point (T.pull (D.prodGmSnd D.point) τ) = 1 :=
  ⟨T.tau, ⟨T.tau_mem_grading, T.standardResidue_pull_prodGmSnd_tau⟩,
    fun _ h ↦ T.eq_tau_of_mem_grading h.1 h.2⟩

/-- `τ² = 0`, by the old identity on `Spec k[t, t⁻¹]`. -/
@[simp] lemma tau_mul_tau : T.tau * T.tau = 0 := by
  rw [tau, ← map_mul]
  exact (congrArg _ T.toAlgebraic.tau_mul_tau).trans (map_zero _)

end Tau

/-! ### Logarithmic classes -/

section LogClass

/-- The *logarithmic class* `[u] = û^* τ` of a global unit `u` of an object `X` of the domain,
where `û : X ⟶ 𝔾ₘ` is the map of `u` (`SmoothDomain.gmHom`). It is defined for every object,
affine or not, and involves no choice. It has degree `(1, 1)` (`logClass_mem_grading`).
Blueprint: `def:geo-log`. -/
def logClass {X : D.Obj} (u : Γ(X.obj.left, ⊤)ˣ) : T.obj X := T.pull (D.gmHom u) T.tau

/-- A logarithmic class has degree `(1, 1)`. Blueprint: `def:geo-log`. -/
theorem logClass_mem_grading {X : D.Obj} (u : Γ(X.obj.left, ⊤)ˣ) :
    T.logClass u ∈ T.grading X (1, 1) :=
  T.pull_mem_grading _ T.tau_mem_grading

/-- Logarithmic classes commute with pullback: `g^*[u] = [g^* u]`. Blueprint: `thm:geo-log-laws`. -/
@[simp] theorem pull_logClass {X Y : D.Obj} (g : X ⟶ Y) (u : Γ(Y.obj.left, ⊤)ˣ) :
    T.pull g (T.logClass u) = T.logClass (Units.map g.hom.left.appTop.hom u) := by
  rw [logClass, logClass, ← pull_comp, SmoothDomain.comp_gmHom]

/-- Restriction to a smaller domain does not change logarithmic classes. -/
@[simp] theorem restrict_logClass {D₁ : SmoothDomain k} (h : D₁ ≤ D) {X : D₁.Obj}
    (u : Γ(X.obj.left, ⊤)ˣ) :
    (T.restrict h).logClass u = T.logClass (X := (ObjectProperty.ιOfLE h).obj X) u :=
  rfl

/-- The logarithmic class `[z]` of the coordinate of `X ×_S 𝔾ₘ` is the pullback of `τ` along the
second projection. -/
theorem logClass_prodGmCoord (X : D.Obj) :
    T.logClass (D.prodGmCoord X) = T.pull (D.prodGmSnd X) T.tau := by
  rw [logClass, SmoothDomain.gmHom_prodGmCoord]

/-- The logarithmic class of the equation of the standard pair of `X` is `[z]`. -/
theorem logClass_standardPair_eqnUnit (X : D.Obj) :
    T.logClass (DivisorPair.standardPair D X).eqnUnit = T.logClass (D.prodGmCoord X) := by
  rw [SmoothDomain.standardPair_eqnUnit]

/-- `[u]² = 0`, by pulling back `τ² = 0`. It does not come from graded commutativity, so it holds
with coefficients in `ℤ/2`. Blueprint: `thm:geo-log-laws`. -/
@[simp] theorem logClass_mul_self {X : D.Obj} (u : Γ(X.obj.left, ⊤)ˣ) :
    T.logClass u * T.logClass u = 0 := by
  rw [logClass, ← map_mul, tau_mul_tau, map_zero]

/-- Logarithmic classes anticommute, because they have odd cohomological degree. -/
theorem logClass_mul_eq_neg_mul_swap {X : D.Obj} (u v : Γ(X.obj.left, ⊤)ˣ) :
    T.logClass u * T.logClass v = -(T.logClass v * T.logClass u) :=
  (T.isGradedCommutative X).mul_eq_neg_of_odd odd_one odd_one (T.logClass_mem_grading u)
    (T.logClass_mem_grading v)

/-- The logarithmic classes of a family of global units are an exterior family. -/
theorem isExteriorFamily_logClass {X : D.Obj} {I : Type*} (g : I → Γ(X.obj.left, ⊤)ˣ) :
    IsExteriorFamily fun i ↦ T.logClass (g i) where
  mul_self i := T.logClass_mul_self (g i)
  mul_add_mul_swap_of_ne i j _ := by
    rw [logClass_mul_eq_neg_mul_swap, neg_add_cancel]

end LogClass

/-! ### Comparison with the algebraic logarithmic classes -/

section Comparison

/-- **Compatibility with the old logarithms.** For a map `g : X ⟶ Spec A` and a unit `u` of the
smooth algebra `A`, the pullback of the old class `[u]` of `T.toAlgebraic` is the class of the
global unit `g^* u` of `X`. Blueprint: `thm:geo-log-laws`. -/
theorem pull_toAlgebraic_logClass {X : D.Obj} {A : SmoothAlg.{u} k} (g : X ⟶ D.spec A) (u : Aˣ)
    {v : Γ(X.obj.left, ⊤)ˣ}
    (hv : (v : Γ(X.obj.left, ⊤)) = g.hom.left.appTop ((Scheme.ΓSpecIso (.of A)).inv u)) :
    T.pull g (T.toAlgebraic.logClass u) = T.logClass v := by
  rw [OrlikSolomon.OrdinaryTheory.logClass, toAlgebraic_map, ← pull_specGmIso_hom_tau,
    ← pull_comp, ← pull_comp, Category.assoc,
    SmoothDomain.comp_specFunctor_map_gmHom_comp_specGmIso_hom g u hv, logClass]

/-- On `Spec A`, the old class `[u]` of `T.toAlgebraic` is the class of the global unit given by
`u`. Blueprint: `thm:geo-log-laws`. -/
theorem toAlgebraic_logClass {A : SmoothAlg.{u} k} (u : Aˣ) {v : Γ((D.spec A).obj.left, ⊤)ˣ}
    (hv : (v : Γ((D.spec A).obj.left, ⊤)) = (Scheme.ΓSpecIso (.of A)).inv u) :
    T.toAlgebraic.logClass u = T.logClass v := by
  rw [← T.pull_toAlgebraic_logClass (𝟙 _) u (by rw [hv, SmoothDomain.appTop_id_apply]), pull_id]

/-- On `Spec A`, the old class `[u]` of `T.toAlgebraic` is the class of the global unit
`specUnit u`. -/
theorem toAlgebraic_logClass_eq {A : SmoothAlg.{u} k} (u : Aˣ) :
    T.toAlgebraic.logClass u = T.logClass (X := D.spec A) (specUnit (A := A.obj) u) :=
  T.toAlgebraic_logClass u rfl

variable (E : OrlikSolomon.OrdinaryTheory.{u, v, w, z} k ℬ)

/-- The algebraic round-trip comparison `A ≅ Γ(Spec A)` preserves logarithmic classes. -/
theorem algebraicRoundTripEquiv_logClass {A : SmoothAlg.{u} k} (u : Aˣ) :
    algebraicRoundTripEquiv E A (E.logClass u) = (ofAlgebraic E).toAlgebraic.logClass u := by
  have htau : (ofAlgebraic E).toAlgebraic.tau =
      algebraicRoundTripEquiv E (SmoothAlg.gm k) E.tau := by
    symm
    refine (ofAlgebraic E).toAlgebraic.eq_tau_of_mem_grading
      ((algebraicRoundTripEquiv_mem_grading_iff E _).2 E.tau_mem_grading) ?_
    have h := (algebraicRoundTripEquiv_residue E
      (OrlikSolomon.DivisorPair.standardPair (SmoothAlg.point k)) E.tau).symm
    change (ofAlgebraic E).toAlgebraic.stdResidue (SmoothAlg.point k)
        (algebraicRoundTripEquiv E (SmoothAlg.gm k) E.tau) =
      algebraicRoundTripEquiv E (SmoothAlg.point k) (E.stdResidue (SmoothAlg.point k) E.tau) at h
    rw [h, OrlikSolomon.OrdinaryTheory.stdResidue_tau, map_one]
  unfold OrlikSolomon.OrdinaryTheory.logClass
  rw [htau]
  exact algebraicRoundTripEquiv_map E _ _

/-- **Compatibility with the old logarithms, the other way.** On a smooth affine scheme `X`, the
logarithmic class of a global unit `u` for the transport `ofAlgebraic E` of an algebraic theory is
the old class of `u` as a unit of the smooth algebra `Γ(X, 𝒪_X)`. Blueprint: `thm:geo-log-laws`. -/
theorem ofAlgebraic_logClass {X : (SmoothDomain.aff k).Obj} (u : Γ(X.obj.left, ⊤)ˣ) :
    (ofAlgebraic E).logClass u =
      E.logClass (A := (affineGlobalSectionsFunctor k).obj (op X)) u := by
  have h := (ofAlgebraic E).pull_toAlgebraic_logClass (affineEvaluationIso X).inv
    (A := (affineGlobalSectionsFunctor k).obj (op X)) u (v := u) (by
      change (u : Γ(X.obj.left, ⊤)) =
        X.obj.left.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(X.obj.left, ⊤)).inv u)
      rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, ← CommRingCat.comp_apply, Iso.inv_hom_id,
        CommRingCat.id_apply])
  refine h.symm.trans ?_
  have ht := algebraicRoundTripEquiv_triangle E X
    (E.logClass (A := (affineGlobalSectionsFunctor k).obj (op X)) u)
  rw [AlgEquiv.symm_apply_eq, affineRoundTripEquiv_apply] at ht
  rw [← algebraicRoundTripEquiv_logClass, ← ht, ← pull_comp, Iso.inv_hom_id, pull_id]

end Comparison

/-! ### Multiplicativity and constants -/

section Multiplicativity

/-- The smooth algebra `k[s, s⁻¹][t, t⁻¹]` of `𝔾ₘ²`. -/
private abbrev gm2 : SmoothAlg.{u} k := SmoothAlg.laurent (SmoothAlg.gm k)

/-- The map `X ⟶ 𝔾ₘ²` of two global units `u` and `v`. -/
private def gm2Hom {X : D.Obj} (u v : Γ(X.obj.left, ⊤)ˣ) : X ⟶ D.spec (gm2 (k := k)) :=
  ObjectProperty.homMk <| (specHomEquiv X.obj (gm2 (k := k)).obj).symm <|
    laurentAlgLift (laurentAlgLift (A := (SmoothAlg.point k).obj)
      (ConcreteCategory.ofHom (C := CommAlgCat k) (X := (SmoothAlg.point k).obj)
        (Y := globalSections X.obj) (Algebra.ofId k _)) u) v

private lemma gm2Hom_appTop {X : D.Obj} (u v : Γ(X.obj.left, ⊤)ˣ) (a : gm2 (k := k)) :
    (gm2Hom u v).hom.left.appTop ((Scheme.ΓSpecIso (.of (gm2 (k := k)))).inv a) =
      laurentAlgLift (laurentAlgLift (A := (SmoothAlg.point k).obj)
        (ConcreteCategory.ofHom (C := CommAlgCat k) (X := (SmoothAlg.point k).obj)
          (Y := globalSections X.obj) (Algebra.ofId k _)) u) v a := by
  rw [← specHomEquiv_apply_apply]
  exact congrArg (fun φ ↦ φ a) ((specHomEquiv X.obj _).apply_symm_apply _)

private lemma gm2Hom_appTop_s {X : D.Obj} (u v : Γ(X.obj.left, ⊤)ˣ) :
    (gm2Hom u v).hom.left.appTop ((Scheme.ΓSpecIso (.of (gm2 (k := k)))).inv
      (SmoothAlg.mapUnits (SmoothAlg.laurentC (SmoothAlg.gm k))
        (SmoothAlg.laurentT (SmoothAlg.point k)) : gm2 (k := k))) = u := by
  rw [gm2Hom_appTop]
  exact (laurentAlgLift_C _ _ _).trans (laurentAlgLift_T _ _)

private lemma gm2Hom_appTop_t {X : D.Obj} (u v : Γ(X.obj.left, ⊤)ˣ) :
    (gm2Hom u v).hom.left.appTop ((Scheme.ΓSpecIso (.of (gm2 (k := k)))).inv
      (SmoothAlg.laurentT (SmoothAlg.gm k) : gm2 (k := k))) = v := by
  rw [gm2Hom_appTop]
  exact laurentAlgLift_T _ _

/-- `[uv] = [u] + [v]`, by pulling back the old identity on `𝔾ₘ²` along `(û, v̂)`. No Künneth
theorem is involved. Blueprint: `thm:geo-log-laws`. -/
@[simp] theorem logClass_mul {X : D.Obj} (u v : Γ(X.obj.left, ⊤)ˣ) :
    T.logClass (u * v) = T.logClass u + T.logClass v := by
  have h := congrArg (T.pull (gm2Hom u v))
    (T.toAlgebraic.logClass_mul
      (SmoothAlg.mapUnits (SmoothAlg.laurentC (SmoothAlg.gm k))
        (SmoothAlg.laurentT (SmoothAlg.point k)))
      (SmoothAlg.laurentT (SmoothAlg.gm k)))
  rwa [map_add, T.pull_toAlgebraic_logClass _ _ (gm2Hom_appTop_s u v).symm,
    T.pull_toAlgebraic_logClass _ _ (gm2Hom_appTop_t u v).symm,
    T.pull_toAlgebraic_logClass _ _ (v := u * v) (by
      rw [Units.val_mul, Units.val_mul, map_mul, map_mul, gm2Hom_appTop_s, gm2Hom_appTop_t])]
    at h

/-- `[1] = 0`. -/
@[simp] theorem logClass_one (X : D.Obj) : T.logClass (1 : Γ(X.obj.left, ⊤)ˣ) = 0 := by
  have h := T.logClass_mul (1 : Γ(X.obj.left, ⊤)ˣ) 1
  rw [mul_one] at h
  exact left_eq_add.1 h

/-- `[u⁻¹] = -[u]`. Blueprint: `thm:geo-log-laws`. -/
@[simp] theorem logClass_inv {X : D.Obj} (u : Γ(X.obj.left, ⊤)ˣ) :
    T.logClass u⁻¹ = -T.logClass u := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← logClass_mul, inv_mul_cancel, logClass_one]

/-- `[u / v] = [u] - [v]`. -/
@[simp] theorem logClass_div {X : D.Obj} (u v : Γ(X.obj.left, ⊤)ˣ) :
    T.logClass (u / v) = T.logClass u - T.logClass v := by
  rw [div_eq_mul_inv, logClass_mul, logClass_inv, sub_eq_add_neg]

/-- A logarithmic class on the base vanishes, since its cohomology has nothing in cohomological
degree one. -/
theorem logClass_point (c : Γ(D.point.obj.left, ⊤)ˣ) : T.logClass c = 0 :=
  T.eq_zero_of_mem_grading_point one_ne_zero (T.logClass_mem_grading c)

/-- `[c] = 0` for a constant `c ∈ kˣ`: the map of a constant unit factors through the base `S`.
The unit is given by its function, the image of `c` in `Γ(X, 𝒪_X)`. It is essential that `c` is a
unit of `k`. Blueprint: `thm:geo-log-laws`. -/
theorem logClass_eq_zero_of_coe_eq_algebraMap {X : D.Obj} {u : Γ(X.obj.left, ⊤)ˣ} (c : kˣ)
    (h : (u : Γ(X.obj.left, ⊤)) = algebraMap k (globalSections X.obj) c) : T.logClass u = 0 := by
  let c' : Γ(D.point.obj.left, ⊤)ˣ :=
    Units.map (algebraMap k (globalSections D.point.obj) : k →* globalSections D.point.obj) c
  have hu : u = Units.map (D.isTerminalPoint.from X).hom.left.appTop.hom c' := by
    ext
    rw [h, Units.coe_map]
    exact (globalSections_commutes (D.isTerminalPoint.from X).hom c).symm
  rw [hu, ← pull_logClass, logClass_point, map_zero]

/-- `[c] = 0` for a constant `c ∈ kˣ`, in bundled form. -/
@[simp] theorem logClass_units_map_algebraMap (X : D.Obj) (c : kˣ) :
    T.logClass (X := X)
      (Units.map (algebraMap k (globalSections X.obj) : k →* globalSections X.obj) c) = 0 :=
  T.logClass_eq_zero_of_coe_eq_algebraMap c rfl

end Multiplicativity

/-! ### Residues of logarithms -/

section Residue

variable (P : DivisorPair D)

/-- The residue of the logarithm of the equation of a pair is `1`: the pair maps to the standard
pair of the base by `z ↦ f` (`DivisorPair.toStandard`), and the residue is natural.
Blueprint: `thm:geo-log-laws`. -/
@[simp] theorem residue_logClass_eqnUnit : T.residue P (T.logClass P.eqnUnit) = 1 := by
  have hc : (DivisorPair.toStandard P).compl ≫ D.prodGmSnd D.point = D.gmHom P.eqnUnit := by
    rw [DivisorPair.toStandard_compl]
    exact ObjectProperty.hom_ext _
      (show lift (toUnit P.compl.obj) (unitsEquivHomGm _ P.eqnUnit) ≫
        snd (𝟙_ (Over (Spec (.of k)))) (Geometric.gm k) = unitsEquivHomGm _ P.eqnUnit from
        lift_snd _ _)
  have h := T.residue_pull (DivisorPair.toStandard P) (T.pull (D.prodGmSnd D.point) T.tau)
  rwa [← pull_comp, hc, residue_standardPair, standardResidue_pull_prodGmSnd_tau, map_one] at h

/-- `r([f] j^* β) = i^* β`, by the projection formula, with the logarithm on the left.
Blueprint: `thm:geo-log-laws`. -/
@[simp] theorem residue_logClass_eqnUnit_mul (β : T.obj P.ambient) :
    T.residue P (T.logClass P.eqnUnit * T.pull P.j β) = T.pull P.i β := by
  rw [T.residue_mul_pull P (T.logClass_mem_grading P.eqnUnit) β, residue_logClass_eqnUnit,
    one_mul]

/-- The residue vanishes on classes pulled back from the ambient scheme. -/
@[simp] theorem residue_pull_j (β : T.obj P.ambient) : T.residue P (T.pull P.j β) = 0 :=
  (T.exact_pull_residue P).apply_apply_eq_zero β

/-- The logarithm of a global unit of the ambient scheme has zero residue. -/
@[simp] theorem residue_logClass_map_j (u : Γ(P.ambient.obj.left, ⊤)ˣ) :
    T.residue P (T.logClass (Units.map P.j.hom.left.appTop.hom u)) = 0 := by
  rw [← pull_logClass, residue_pull_j]

end Residue

/-! ### The product with `𝔾ₘ` -/

section GmProduct

variable (X : D.Obj)

/-- The standard residue vanishes on classes pulled back from `X`. -/
@[simp] theorem standardResidue_pull_prodGmFst (b : T.obj X) :
    T.standardResidue X (T.pull (D.prodGmFst X) b) = 0 := by
  rw [← SmoothDomain.prodGmToProdAffineLine_prodAffineLineFst, pull_comp]
  exact T.residue_pull_j (DivisorPair.standardPair D X) _

/-- `r([z]) = 1` on `X ×_S 𝔾ₘ`. -/
@[simp] theorem standardResidue_logClass_prodGmCoord :
    T.standardResidue X (T.logClass (D.prodGmCoord X)) = 1 := by
  have h := T.residue_logClass_eqnUnit (DivisorPair.standardPair D X)
  rwa [logClass_standardPair_eqnUnit] at h

/-- `r([z] π^* b) = b` on `X ×_S 𝔾ₘ`. -/
@[simp] theorem standardResidue_logClass_prodGmCoord_mul (b : T.obj X) :
    T.standardResidue X (T.logClass (D.prodGmCoord X) * T.pull (D.prodGmFst X) b) = b := by
  rw [← SmoothDomain.prodGmToProdAffineLine_prodAffineLineFst, pull_comp,
    T.standardResidue_mul_pull X (T.logClass_mem_grading _), standardResidue_logClass_prodGmCoord,
    one_mul, ← pull_comp, SmoothDomain.zeroSection_prodAffineLineFst, pull_id]

/-- The section `z = 1` kills `[z]`, since `[1] = 0`. -/
theorem pull_oneSection_logClass_prodGmCoord :
    T.pull (D.oneSection X) (T.logClass (D.prodGmCoord X)) = 0 := by
  rw [pull_logClass, SmoothDomain.map_oneSection_prodGmCoord, logClass_one]

@[simp] theorem pull_oneSection_pull_prodGmFst (b : T.obj X) :
    T.pull (D.oneSection X) (T.pull (D.prodGmFst X) b) = b := by
  rw [← pull_comp, SmoothDomain.oneSection_prodGmFst, pull_id]

/-- The residue of the standard pair of `X` is surjective: `[z] π^* b` lifts `b`.
Blueprint: `thm:geo-gm-product`. -/
theorem surjective_standardResidue : Function.Surjective (T.standardResidue X) := fun b ↦
  ⟨_, T.standardResidue_logClass_prodGmCoord_mul X b⟩

/-- The Gysin map of the standard pair of `X` vanishes. Blueprint: `thm:geo-gm-product`. -/
theorem standardGysin_eq_zero : T.standardGysin X = 0 := by
  ext x
  obtain ⟨y, rfl⟩ := T.surjective_standardResidue X x
  exact (T.exact_standardResidue_standardGysin X).apply_apply_eq_zero y

/-- The open pullback of the standard pair of `X` is injective. Blueprint: `thm:geo-gm-product`. -/
theorem injective_pull_prodGmToProdAffineLine :
    Function.Injective (T.pull (D.prodGmToProdAffineLine X)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := ((T.exact_standardGysin_pull X) x).1 hx
  rw [standardGysin_eq_zero, LinearMap.zero_apply]

/-- Every class `x` on `X ×_S 𝔾ₘ` is `π^* (s₁^* x) + [z] π^* r(x)`. -/
theorem pull_prodGmFst_add_logClass_mul (x : T.obj (D.prodGm X)) :
    T.pull (D.prodGmFst X) (T.pull (D.oneSection X) x) +
      T.logClass (D.prodGmCoord X) * T.pull (D.prodGmFst X) (T.standardResidue X x) = x := by
  have hd : T.standardResidue X
      (x - T.logClass (D.prodGmCoord X) * T.pull (D.prodGmFst X) (T.standardResidue X x)) = 0 := by
    rw [map_sub, standardResidue_logClass_prodGmCoord_mul, sub_self]
  obtain ⟨y, hy⟩ := ((T.exact_pull_standardResidue X) _).1 hd
  obtain ⟨y, rfl⟩ := (T.bijective_pull_prodAffineLineFst X).2 y
  rw [← pull_comp, SmoothDomain.prodGmToProdAffineLine_prodAffineLineFst] at hy
  have hs : T.pull (D.oneSection X) x = y := by
    have := congrArg (T.pull (D.oneSection X)) hy
    rw [map_sub, map_mul, pull_oneSection_logClass_prodGmCoord, zero_mul, sub_zero,
      pull_oneSection_pull_prodGmFst] at this
    exact this.symm
  rw [hs, hy, sub_add_cancel]

/-- **The product with `𝔾ₘ`.** For every object `X` of the domain, affine or not, the standard pair
gives the equivalence `C(X) ⊕ C(X) ≃ C(X ×_S 𝔾ₘ)`, `(a, b) ↦ π^* a + [z] π^* b`, where `π` is the
projection and `z` the coordinate, the equation of the standard pair. Its second summand is shifted
by `(1, 1)` (`gmProductEquiv_mem_grading_iff`), its inverse is `x ↦ (s₁^* x, r(x))` with `s₁` the
section `z = 1` (`gmProductEquiv_symm_apply`), and it is natural in `X`
(`pull_prodGmMap_gmProductEquiv`). It is an equivalence of `B`-modules, not of algebras.
Blueprint: `thm:geo-gm-product`. -/
@[no_expose] def gmProductEquiv : (T.obj X × T.obj X) ≃ₗ[B] T.obj (D.prodGm X) :=
  { (T.pull (D.prodGmFst X)).toLinearMap.coprod
      (LinearMap.mulLeft B (T.logClass (D.prodGmCoord X)) ∘ₗ
        (T.pull (D.prodGmFst X)).toLinearMap) with
    invFun x := (T.pull (D.oneSection X) x, T.standardResidue X x)
    left_inv := fun ⟨a, b⟩ ↦ by
      change (T.pull (D.oneSection X) (T.pull (D.prodGmFst X) a +
          T.logClass (D.prodGmCoord X) * T.pull (D.prodGmFst X) b),
        T.standardResidue X (T.pull (D.prodGmFst X) a +
          T.logClass (D.prodGmCoord X) * T.pull (D.prodGmFst X) b)) = (a, b)
      rw [map_add, map_add, map_mul, pull_oneSection_logClass_prodGmCoord, zero_mul, add_zero,
        pull_oneSection_pull_prodGmFst, standardResidue_pull_prodGmFst,
        standardResidue_logClass_prodGmCoord_mul, zero_add]
    right_inv := T.pull_prodGmFst_add_logClass_mul X }

variable {X}

/-- `gmProductEquiv` sends `(a, b)` to `π^* a + [z] π^* b`. Blueprint: `thm:geo-gm-product`. -/
@[simp] lemma gmProductEquiv_apply (a b : T.obj X) :
    T.gmProductEquiv X (a, b) =
      T.pull (D.prodGmFst X) a + T.logClass (D.prodGmCoord X) * T.pull (D.prodGmFst X) b := by
  rfl

/-- The inverse of `gmProductEquiv` is given by the section `z = 1` and the standard residue. This
is not a `simp` lemma, so that `LinearEquiv.apply_symm_apply` still fires.
Blueprint: `thm:geo-gm-product`. -/
lemma gmProductEquiv_symm_apply (x : T.obj (D.prodGm X)) :
    (T.gmProductEquiv X).symm x = (T.pull (D.oneSection X) x, T.standardResidue X x) := by
  rfl

/-- The section `z = 1` reads off the first coordinate of `gmProductEquiv`.
Blueprint: `thm:geo-gm-product`. -/
theorem pull_oneSection_gmProductEquiv (a b : T.obj X) :
    T.pull (D.oneSection X) (T.gmProductEquiv X (a, b)) = a := by
  rw [gmProductEquiv_apply, map_add, map_mul, pull_oneSection_logClass_prodGmCoord, zero_mul,
    add_zero, pull_oneSection_pull_prodGmFst]

/-- The standard residue reads off the second coordinate of `gmProductEquiv`.
Blueprint: `thm:geo-gm-product`. -/
theorem standardResidue_gmProductEquiv (a b : T.obj X) :
    T.standardResidue X (T.gmProductEquiv X (a, b)) = b := by
  rw [gmProductEquiv_apply, map_add, standardResidue_pull_prodGmFst, zero_add,
    standardResidue_logClass_prodGmCoord_mul]

/-- `gmProductEquiv` preserves degrees with its second summand shifted by `(1, 1)`.
Blueprint: `thm:geo-gm-product`. -/
theorem gmProductEquiv_mem_grading_iff {i j : ℤ × ℤ} (hij : j + (1, 1) = i) {a b : T.obj X} :
    T.gmProductEquiv X (a, b) ∈ T.grading (D.prodGm X) i ↔
      a ∈ T.grading X i ∧ b ∈ T.grading X j := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨ha, hb⟩ ↦ ?_⟩
  · have hs := T.pull_mem_grading (D.oneSection X) h
    rwa [gmProductEquiv_apply, map_add, map_mul, pull_oneSection_logClass_prodGmCoord, zero_mul,
      add_zero, pull_oneSection_pull_prodGmFst] at hs
  · have hj : i + (-1, -1) = j := by
      rw [← hij]
      ext <;> simp
    have h' := (T.isHomogeneousOfShift_standardResidue X).map_mem hj h
    rwa [gmProductEquiv_apply, map_add, standardResidue_pull_prodGmFst, zero_add,
      standardResidue_logClass_prodGmCoord_mul] at h'
  · rw [gmProductEquiv_apply]
    exact add_mem (T.pull_mem_grading _ ha)
      ((isHomogeneousOfShift_mul_left (T.logClass_mem_grading (D.prodGmCoord X))).map_mem hij
        (T.pull_mem_grading _ hb))

/-- `gmProductEquiv` is natural in `X`. Blueprint: `thm:geo-gm-product`. -/
theorem pull_prodGmMap_gmProductEquiv {Y : D.Obj} (g : X ⟶ Y) (a b : T.obj Y) :
    T.pull (D.prodGmMap g) (T.gmProductEquiv Y (a, b)) =
      T.gmProductEquiv X (T.pull g a, T.pull g b) := by
  rw [gmProductEquiv_apply, gmProductEquiv_apply, map_add, map_mul, logClass_prodGmCoord,
    logClass_prodGmCoord]
  simp only [← pull_comp, SmoothDomain.prodGmMap_prodGmFst, SmoothDomain.prodGmMap_prodGmSnd]

end GmProduct

end OrdinaryTheory

end OrlikSolomon.Geometric
