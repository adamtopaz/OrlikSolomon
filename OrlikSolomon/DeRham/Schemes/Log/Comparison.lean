/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Topology.Sheaves.Abelian
public import OrlikSolomon.DeRham.Log
public import OrlikSolomon.DeRham.Pole.Degree
public import OrlikSolomon.DeRham.Schemes.Log.Restriction

/-!
# Logarithmic comparisons and detection on stalks

The ordinary module stalk functors preserve homology and jointly detect isomorphisms of
sheaves. Consequently they detect quasi-isomorphisms of sheaf complexes of any shape.
This criterion is the sheaf-theoretic step in the logarithmic comparison of
`thm:geo-log-sheaves`; it makes no assertion about applying global sections to a
quasi-isomorphism.

The existing pole comparison is also packaged as a quasi-isomorphism of the actual
algebraic logarithmic complex. Its proof uses the existing comparison on cohomology and
the degreewise primitive criteria, including degree zero.

## Main results

* `sheafComplex_quasiIso_iff_stalk`: a map of complexes of module sheaves is a
  quasi-isomorphism exactly when all of its stalk maps are quasi-isomorphisms.
* `algebraicLogToLocalization_quasiIso`: the algebraic logarithmic inclusion is a
  quasi-isomorphism for a smooth principal pair when positive integers are units.
* `presheafComplex_stalk_quasiIso_of_basis` and `sheafComplex_quasiIso_of_basis`:
  quasi-isomorphisms on the section complexes of a basis induce quasi-isomorphisms on
  stalks and, for sheaves, on the sheaf complexes.
* `logSheafComparison_of_units` and `logSheafComparison`: the actual logarithmic inclusion
  is a quasi-isomorphism of sheaf complexes, proved on affine neighborhoods and then stalks.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace OrlikSolomon.Geometric.DeRham

private theorem moduleCat_homologyπ_eq_zero_iff {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ y, S.f y = S.iCycles z := by
  have hπ := ConcreteCategory.congr_hom S.homology_π_ι z
  simp only [ConcreteCategory.comp_apply] at hπ
  have hi : Function.Injective S.homologyι :=
    (ModuleCat.mono_iff_injective S.homologyι).1 inferInstance
  rw [← hi.eq_iff]
  simp only [map_zero, hπ, S.moduleCat_pOpcycles_eq_zero_iff, LinearMap.mem_range]

private theorem moduleCat_quasiIso_of_representatives {R : Type u} [Ring R]
    {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (hi : ∀ x, S.g x = 0 → (∃ b, T.f b = φ.τ₂ x) → ∃ a, S.f a = x)
    (hs : ∀ y, T.g y = 0 → ∃ x, S.g x = 0 ∧ ∃ b, φ.τ₂ x - y = T.f b) :
    ShortComplex.QuasiIso φ := by
  rw [ShortComplex.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (ShortComplex.homologyMap φ).hom.ker_eq_bot.1
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    change ShortComplex.homologyMap φ a = 0 at ha
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance a
    have he := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) z
    simp only [ConcreteCategory.comp_apply] at he
    have hb := (moduleCat_homologyπ_eq_zero_iff T (ShortComplex.cyclesMap φ z)).1
      (he.symm.trans ha)
    have hc := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) z
    simp only [ConcreteCategory.comp_apply] at hc
    rw [hc] at hb
    have hd : S.g (S.iCycles z) = 0 := ConcreteCategory.congr_hom S.iCycles_g z
    obtain ⟨b, hb⟩ := hi (S.iCycles z) hd hb
    exact (moduleCat_homologyπ_eq_zero_iff S z).2 ⟨b, hb⟩
  · intro a
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).1 inferInstance a
    have hd : T.g (T.iCycles z) = 0 := ConcreteCategory.congr_hom T.iCycles_g z
    obtain ⟨x, hx, b, hb⟩ := hs (T.iCycles z) hd
    let zx := S.cyclesMk x hx
    have hzx : S.iCycles zx = x := S.i_cyclesMk x hx
    refine ⟨S.homologyπ zx, ?_⟩
    have he := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) zx
    simp only [ConcreteCategory.comp_apply] at he
    rw [he]
    apply sub_eq_zero.1
    rw [← map_sub]
    apply (moduleCat_homologyπ_eq_zero_iff T _).2
    refine ⟨b, ?_⟩
    rw [map_sub]
    have hc := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) zx
    simp only [ConcreteCategory.comp_apply] at hc
    rw [hc]
    simpa only [hzx] using hb.symm

section AlgebraicComparison

open OrlikSolomon.DeRham

variable (k : Type u) [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
  (f : A) (T : Type v) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]
  {S : Type v} [CommRing S] [Algebra k S] {π : A →ₐ[k] S}

/-- The inclusion of the algebraic logarithmic complex into localized forms is a
quasi-isomorphism when positive integers are units and the ambient algebra and divisor form a
smooth principal pair. This packages the existing degreewise pole comparison as a statement
about the actual chain map, with the same inclusion on representatives. -/
theorem algebraicLogToLocalization_quasiIso
    (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) (hpair : IsSmoothPrincipalPair f π) :
    QuasiIso (logToLocalization k f T) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' _ ((ComplexShape.up ℕ).prev n) n (n + 1) rfl
    (CochainComplex.next ℕ n)]
  apply moduleCat_quasiIso_of_representatives
  all_goals simp only [HomologicalComplex.shortComplexFunctor'_obj_X₁,
    HomologicalComplex.shortComplexFunctor'_obj_X₂, HomologicalComplex.shortComplexFunctor'_obj_X₃,
    HomologicalComplex.shortComplexFunctor'_obj_f, HomologicalComplex.shortComplexFunctor'_obj_g,
    HomologicalComplex.shortComplexFunctor'_map_τ₂, logComplex_X, complex_X,
    logToLocalization_f, logComplex_d, complex_d]
  · intro x hx hb
    have hdx : logPowerD k f T n x = 0 := hx
    let xl := logPowerToLogForms k f T n x
    have hxl : logD k f T xl = 0 := Subtype.ext
      (congrArg (fun z : logPower k f T (n + 1) => (z : Forms k T)) hdx)
    have hdxt : d k (x : Forms k T) = 0 := congrArg Subtype.val hdx
    have hxzero : Cohomology.mk (x : Forms k T) hdxt = 0 := by
      apply Cohomology.mk_eq_zero_iff.2
      obtain ⟨b, hb⟩ := hb
      have hb' : logPowerToPower k f T n x ∈ Cohomology.rangeD k T n := by
        rw [← range_complex_d_hom_prev]
        exact ⟨b, hb⟩
      exact Cohomology.mem_rangeD_iff.1 hb'
    have hxlzero : LogCohomology.mk xl hxl = 0 := by
      apply (logToLocalizationQuasiIso k f T hUnits hpair).1
      rw [LogCohomology.toCohomology_mk, map_zero]
      exact hxzero
    cases n with
    | zero =>
      have hxzero := (LogCohomology.mk_eq_zero_iff_of_mem_logPower_zero x.2).1 hxlzero
      have hxx : x = 0 := Subtype.ext
        (congrArg (fun z : logForms k f T => (z : Forms k T)) hxzero)
      exact ⟨0, ((logComplex k f T).d ((ComplexShape.up ℕ).prev 0) 0).hom.map_zero.trans
        hxx.symm⟩
    | succ n =>
      obtain ⟨y, hy, hdy⟩ :=
        (LogCohomology.mk_eq_zero_iff_of_mem_logPower_succ x.2).1 hxlzero
      change ∃ b : (logComplex k f T).X ((ComplexShape.up ℕ).prev (n + 1)),
        ((logComplex k f T).d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)).hom b = x
      rw [CochainComplex.prev_nat_succ n]
      refine ⟨⟨(y : Forms k T), hy⟩, ?_⟩
      rw [logComplex_d]
      change logPowerD k f T n ⟨(y : Forms k T), hy⟩ = x
      exact Subtype.ext (congrArg (fun z : logForms k f T => (z : Forms k T)) hdy)
  · intro y hy
    have hdy : powerD k T n y = 0 := hy
    have hdyt : d k (y : Forms k T) = 0 := congrArg Subtype.val hdy
    let cy : Cohomology.degree k T n := ⟨Cohomology.mk (y : Forms k T) hdyt,
      Cohomology.mk_mem_degree y.2 hdyt⟩
    let cl := (logToLocalizationDegreeEquiv k f T hUnits hpair n).symm cy
    obtain ⟨x, hx, hxn, hxc⟩ := LogCohomology.mem_degree_iff.1 cl.2
    let xp : logPower k f T n := ⟨(x : Forms k T), hxn⟩
    refine ⟨xp, ?_, ?_⟩
    · exact Subtype.ext (congrArg (fun z : logForms k f T => (z : Forms k T)) hx)
    · have heq : Cohomology.mk (x : Forms k T) (logD_eq_zero_iff.1 hx) =
          Cohomology.mk (y : Forms k T) hdyt := by
        have h := toCohomology_logToLocalizationDegreeEquiv_symm k f T hUnits hpair n cy
        rw [← hxc, LogCohomology.toCohomology_mk] at h
        exact h
      have hb : logPowerToPower k f T n xp - y ∈ Cohomology.rangeD k T n :=
        Cohomology.mem_rangeD_iff.2 (Cohomology.mk_eq_mk_iff.1 heq)
      rw [← range_complex_d_hom_prev] at hb
      obtain ⟨b, hb⟩ := hb
      exact ⟨b, hb.symm⟩

end AlgebraicComparison

/-- A morphism of complexes of module sheaves is a quasi-isomorphism if and only if its
ordinary stalk maps are quasi-isomorphisms. This compares homology sheaves, without any
exactness assertion for global sections. -/
theorem sheafComplex_quasiIso_iff_stalk (k : Type u) [Ring k] (X : TopCat.{u})
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (TopCat.Sheaf (ModuleCat.{u} k) X) c} (f : K ⟶ L) :
    QuasiIso f ↔ ∀ x : X,
      QuasiIso (((TopCat.Sheaf.forget (ModuleCat.{u} k) X ⋙
        TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).mapHomologicalComplex c).map f) := by
  constructor
  · intro hf x
    infer_instance
  · intro hf
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap,
      TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    let F := TopCat.Sheaf.forget (ModuleCat.{u} k) X ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x
    let g := (HomologicalComplex.shortComplexFunctor _ _ n).map f
    have hg : ShortComplex.QuasiIso (F.mapShortComplex.map g) := by
      have h := (quasiIso_iff _).1 (hf x) n
      exact (quasiIsoAt_iff _ n).1 h
    have hmap := ShortComplex.mapHomologyIso_hom_naturality g F
    have : IsIso ((K.sc n).mapHomologyIso F).hom := inferInstance
    have : IsIso (((K.sc n).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.homologyMap f n)) := by
      change IsIso (((K.sc n).mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap g))
      rw [← hmap]
      have := (ShortComplex.quasiIso_iff _).1 hg
      infer_instance
    change IsIso (F.map (HomologicalComplex.homologyMap f n))
    exact IsIso.of_isIso_comp_left ((K.sc n).mapHomologyIso F).hom _

section BasisComparison

variable (k : Type u) [Ring k] (X : TopCat.{u})

private theorem presheafStalk_preservesHomology (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).PreservesHomology := by
  have : PreservesFiniteLimits ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ
      (ModuleCat.{u} k)).obj (OpenNhds.inclusion x).op) := by infer_instance
  have : PreservesFiniteColimits ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ
      (ModuleCat.{u} k)).obj (OpenNhds.inclusion x).op) := by infer_instance
  have : PreservesFiniteLimits (colim (J := (OpenNhds x)ᵒᵖ) (C := ModuleCat.{u} k)) :=
    inferInstance
  have : PreservesFiniteColimits (colim (J := (OpenNhds x)ᵒᵖ) (C := ModuleCat.{u} k)) :=
    inferInstance
  have : PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x) :=
    comp_preservesFiniteColimits _ _
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

private theorem presheaf_stalkMap_isIso_of_basis {F G : X.Presheaf (ModuleCat.{u} k)}
    {B : Set (Opens X)} (hB : Opens.IsBasis B) (f : F ⟶ G)
    (hf : ∀ U ∈ B, IsIso (f.app (op U))) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).map f) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB
    intro U hU
    have := hf U hU
    exact (ConcreteCategory.bijective_of_isIso _).1
  · intro t
    obtain ⟨U, hxU, hU, s, rfl⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB G x t
    have := hf U hU
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (f.app (op U))).2 s
    refine ⟨F.germ U x hxU a, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ha]

/-- A map of complexes of module presheaves induces a quasi-isomorphism at every stalk if
its maps on section complexes are quasi-isomorphisms on a basis. Filtered colimits of modules
preserve homology; no sheaf condition or assertion about global sections is needed. -/
theorem presheafComplex_stalk_quasiIso_of_basis
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (X.Presheaf (ModuleCat.{u} k)) c} (f : K ⟶ L)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hf : ∀ U ∈ B, QuasiIso
      ((((evaluation (Opens X)ᵒᵖ (ModuleCat.{u} k)).obj (op U)).mapHomologicalComplex c).map f))
    (x : X) :
    QuasiIso
      (((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x).mapHomologicalComplex c).map f) := by
  have := presheafStalk_preservesHomology k X x
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff]
  let S := K.sc n
  let T := L.sc n
  let g := (HomologicalComplex.shortComplexFunctor _ _ n).map f
  have hmap : ∀ U ∈ B, IsIso ((ShortComplex.homologyMap g).app (op U)) := by
    intro U hU
    let E := (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} k)).obj (op U)
    have : E.Additive := by infer_instance
    have : E.PreservesHomology := by infer_instance
    have hg : ShortComplex.QuasiIso (E.mapShortComplex.map g) := by
      exact (quasiIsoAt_iff _ n).1 ((quasiIso_iff _).1 (hf U hU) n)
    have hnat := ShortComplex.mapHomologyIso_hom_naturality g E
    have : IsIso ((S.mapHomologyIso E).hom ≫ E.map (ShortComplex.homologyMap g)) := by
      rw [← hnat]
      have := (ShortComplex.quasiIso_iff _).1 hg
      infer_instance
    change IsIso (E.map (ShortComplex.homologyMap g))
    exact IsIso.of_isIso_comp_left (S.mapHomologyIso E).hom _
  let F := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} k) x
  have : IsIso (F.map (ShortComplex.homologyMap g)) :=
    presheaf_stalkMap_isIso_of_basis k X hB _ hmap x
  have hnat := ShortComplex.mapHomologyIso_hom_naturality g F
  have : IsIso ((S.mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap g)) :=
    inferInstance
  rw [← hnat] at this
  have : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map g)) :=
    IsIso.of_isIso_comp_right _ (T.mapHomologyIso F).hom
  exact (ShortComplex.quasiIso_iff _).2 this

/-- A map of complexes of module sheaves is a quasi-isomorphism if its maps on section
complexes are quasi-isomorphisms on a basis. In particular, affine-open section comparisons
suffice for a scheme; this does not assert that global sections preserve sheaf homology. -/
theorem sheafComplex_quasiIso_of_basis
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (TopCat.Sheaf (ModuleCat.{u} k) X) c} (f : K ⟶ L)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hf : ∀ U ∈ B, QuasiIso
      ((((evaluation (Opens X)ᵒᵖ (ModuleCat.{u} k)).obj (op U)).mapHomologicalComplex c).map
        (((TopCat.Sheaf.forget (ModuleCat.{u} k) X).mapHomologicalComplex c).map f))) :
    QuasiIso f := by
  apply (sheafComplex_quasiIso_iff_stalk k X f).2
  intro x
  exact presheafComplex_stalk_quasiIso_of_basis k X
    (((TopCat.Sheaf.forget (ModuleCat.{u} k) X).mapHomologicalComplex c).map f) hB hf x

end BasisComparison

section GeometricComparison

variable {k : Type u} [CommRing k] {D : SmoothDomain k} (P : DivisorPair D)

/-- The inclusion of logarithmic forms in the ordinary direct-image de Rham complex is a
quasi-isomorphism when positive integers are units in the base ring. The proof compares sections
on every affine neighborhood with the existing pole theorem, then passes to stalks.
It does not apply underived global sections to a quasi-isomorphism.

Blueprint: `thm:geo-log-sheaves`. -/
theorem logSheafComparison_of_units (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k)) :
    QuasiIso (logToOpenComplexNat P) := by
  apply sheafComplex_quasiIso_of_basis k P.ambient.obj.left (logToOpenComplexNat P)
    (B := P.ambient.obj.left.affineOpens)
    (by simpa only [Opens.IsBasis] using P.ambient.obj.left.isBasis_affineOpens)
  intro U hU
  let V : P.ambient.obj.left.affineOpens := ⟨U, hU⟩
  change QuasiIso
    (((sheafSectionsFunctor (k := k) P.ambient.obj.left V.1).mapHomologicalComplex
      (.up ℕ)).map (logToOpenComplexNat P))
  let Q := affineNeighborhoodAlgebraicPair P V
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (affineNeighborhoodLogComplexIso P V) (affineNeighborhoodOpenComplexIso P V)
      (affineNeighborhoodLogComplexIso_toOpen P V))).1
        (algebraicLogToLocalization_quasiIso k Q.eqn Q.compl hUnits Q.isSmoothPrincipalPair)

end GeometricComparison

/-- Over a characteristic-zero field, logarithmic forms are quasi-isomorphic to the ordinary
direct image of forms on the complement, as complexes of sheaves. This is a stalkwise statement;
it makes no comparison with derived direct image or non-affine global cohomology.

Blueprint: `thm:geo-log-sheaves`. -/
theorem logSheafComparison {k : Type u} [Field k] [CharZero k] {D : SmoothDomain k}
    (P : DivisorPair D) : QuasiIso (logToOpenComplexNat P) :=
  logSheafComparison_of_units P fun n => isUnit_iff_ne_zero.2 (Nat.cast_add_one_ne_zero n)

end OrlikSolomon.Geometric.DeRham
