/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.DeRham.Schemes.Corollaries
public import OrlikSolomon.HyperplaneGT.Cohomology.Adapter.Comparison

/-!
# The actual ordinary de Rham diagram and its diagonal comparison

For the existing characteristic-zero de Rham instance, the component `E^(q,q)` is ordinary
`H^q_dR`, and the diagonal direct sum is the actual ordinary total cohomology algebra.
The comparisons commute with actual scheme pullbacks. Evaluation at `t = 1` is used only
on this diagonal; no equivalence from the whole Laurent-weighted algebra is asserted.

The degree-one coordinates and exterior cup map below have actual ordinary cohomology
carriers. Their complete kernels, inclusion arrows and one common marking target are
compared with A04 without constructing another theory.

Blueprint: the ordinary/diagonal comparison in E03 (`cor:e03`).
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace OrlikSolomon.HyperplaneGT.Cohomology.DeRham

variable {k : Type u} [Field k] [CharZero k]

local notation "Daff" => Geometric.SmoothDomain.aff k
local notation "Tdr" => Geometric.DeRham.ordinaryTheory k
local notation "HdR" => Geometric.DeRham.Cohomology
local notation "HdRdegree" => Geometric.DeRham.Cohomology.degree

/-- Removing the Laurent weight from the actual component `E^(q,q)` gives ordinary
degree `q`. Blueprint: E03 (`cor:e03`). -/
def componentUntwist (X : (Daff).Obj) (q : ℕ) :
    (Tdr).grading X ((q : ℤ), (q : ℤ)) ≃ₗ[k] HdRdegree X q :=
  (Geometric.DeRham.gradingEquiv X q (q : ℤ)).symm

/-- On a component the comparison is the existing evaluation at `t = 1`. -/
theorem componentUntwist_apply (X : (Daff).Obj) (q : ℕ)
    (x : (Tdr).grading X ((q : ℤ), (q : ℤ))) :
    (componentUntwist X q x : HdR X) = Geometric.DeRham.untwist X x := by
  obtain ⟨c, rfl⟩ := (Geometric.DeRham.gradingEquiv X q (q : ℤ)).surjective x
  simp [componentUntwist]

/-- The diagonal direct sum of the constructed instance is the actual ordinary total
de Rham algebra. Blueprint: E03 (`cor:e03`). -/
def diagonalUntwist (X : (Daff).Obj) :
    Cohomology.diagonal Tdr X ≃ₐ[k] HdR X :=
  (OrlikSolomon.DeRham.TwistedCohomology.diagonalEquiv k
    (Geometric.globalSections X.obj)).symm

/-- The diagonal comparison is weight forgetting after the diagonal inclusion. -/
theorem diagonalUntwist_apply (X : (Daff).Obj) (x : Cohomology.diagonal Tdr X) :
    diagonalUntwist X x = Geometric.DeRham.untwist X
      (DirectSum.coeAlgHom (OrlikSolomon.diagonalGrading ((Tdr).grading X)) x) :=
  OrlikSolomon.DeRham.TwistedCohomology.diagonalEquiv_symm_apply x

/-- On an actual summand, diagonal and component untwisting agree. -/
@[simp]
theorem diagonalUntwist_of (X : (Daff).Obj) (q : ℕ)
    (x : OrlikSolomon.diagonalGrading ((Tdr).grading X) q) :
    diagonalUntwist X (DirectSum.of _ q x) = (componentUntwist X q x : HdR X) := by
  rw [diagonalUntwist_apply]
  rw [DirectSum.coeAlgHom_of]
  exact (componentUntwist_apply X q x).symm

/-- Every ordinary homogeneous class goes back to the corresponding diagonal summand. -/
theorem diagonalUntwist_symm_of_mem_degree (X : (Daff).Obj) (q : ℕ)
    (x : HdRdegree X q) :
    (diagonalUntwist X).symm (x : HdR X) =
      DirectSum.of _ q ((componentUntwist X q).symm x) := by
  apply (diagonalUntwist X).injective
  rw [AlgEquiv.apply_symm_apply]
  exact ((diagonalUntwist_of X q ((componentUntwist X q).symm x)).trans
    (congrArg Subtype.val ((componentUntwist X q).apply_symm_apply x))).symm

/-- The full diagonal degree submodule maps onto the full ordinary degree submodule. -/
theorem diagonalUntwist_degree (X : (Daff).Obj) (q : ℕ) :
    (Cohomology.diagonalDegree Tdr X q).map (diagonalUntwist X).toLinearMap =
      HdRdegree X q := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact (diagonalUntwist_of X q z).symm ▸ (componentUntwist X q z).property
  · intro hx
    refine ⟨DirectSum.of _ q ((componentUntwist X q).symm ⟨x, hx⟩),
      ⟨(componentUntwist X q).symm ⟨x, hx⟩, rfl⟩, ?_⟩
    exact (diagonalUntwist_of X q _).trans
      (congrArg Subtype.val ((componentUntwist X q).apply_symm_apply ⟨x, hx⟩))

/-- Actual scheme pullback restricted to an ordinary cohomological degree. -/
def componentPull {X Y : (Daff).Obj} (f : X ⟶ Y) (q : ℕ) :
    HdRdegree Y q →ₗ[k] HdRdegree X q :=
  (Geometric.DeRham.Cohomology.pull f).toLinearMap.restrict fun _ hx ↦
    Geometric.DeRham.Cohomology.pull_mem_degree f hx

omit [CharZero k] in
/-- The underlying value of a component pullback is the actual ordinary pullback. -/
@[simp]
theorem componentPull_coe {X Y : (Daff).Obj} (f : X ⟶ Y) (q : ℕ)
    (x : HdRdegree Y q) :
    (componentPull f q x : HdR X) = Geometric.DeRham.Cohomology.pull f x := rfl

omit [CharZero k] in
/-- Ordinary component pullback by the identity is the identity. -/
@[simp]
theorem componentPull_id (X : (Daff).Obj) (q : ℕ) :
    componentPull (𝟙 X) q = LinearMap.id := by
  ext x
  exact Geometric.DeRham.Cohomology.pull_id (x : HdR X)

omit [CharZero k] in
/-- Ordinary component pullbacks compose contravariantly. -/
@[simp]
theorem componentPull_comp {X Y Z : (Daff).Obj} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ) :
    componentPull (f ≫ g) q = (componentPull f q).comp (componentPull g q) := by
  ext x
  exact Geometric.DeRham.Cohomology.pull_comp f g x

/-- Removing a component weight commutes with every actual scheme pullback. -/
theorem componentUntwist_naturality {X Y : (Daff).Obj} (f : X ⟶ Y) (q : ℕ) :
    (componentUntwist X q).toLinearMap.comp (Cohomology.componentPull Tdr f q) =
      (componentPull f q).comp (componentUntwist Y q).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  calc
    _ = Geometric.DeRham.untwist X ((Tdr).pull f x) :=
      componentUntwist_apply X q _
    _ = Geometric.DeRham.Cohomology.pull f (Geometric.DeRham.untwist Y x) :=
      Geometric.DeRham.untwist_pull f x
    _ = _ := congrArg (Geometric.DeRham.Cohomology.pull f)
      (componentUntwist_apply Y q x).symm

/-- Diagonal untwisting commutes with every actual scheme pullback as an algebra map. -/
theorem diagonalUntwist_naturality {X Y : (Daff).Obj} (f : X ⟶ Y) :
    (diagonalUntwist X).toAlgHom.comp (Cohomology.diagonalPull Tdr f) =
      (Geometric.DeRham.Cohomology.pull f).comp (diagonalUntwist Y).toAlgHom := by
  apply AlgHom.ext
  intro x
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, diagonalUntwist_apply,
    Cohomology.coeAlgHom_diagonalPull]
  exact Geometric.DeRham.untwist_pull f _

section Arrangements

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Actual ordinary degree-one de Rham cohomology of an open arrangement complement. -/
def degreeOne (A : Arrangement k V) : Submodule k (HdR ((Daff).complement A)) :=
  HdRdegree ((Daff).complement A) 1

/-- Actual ordinary degree-two de Rham cohomology of an open arrangement complement. -/
def degreeTwo (A : Arrangement k V) : Submodule k (HdR ((Daff).complement A)) :=
  HdRdegree ((Daff).complement A) 2

/-- Canonical hyperplane coordinates on ordinary degree-one de Rham cohomology. -/
def degreeOneEquiv (A : Arrangement k V) : (A →₀ k) ≃ₗ[k] degreeOne A :=
  (osDegreeOneEquiv k A).trans (Geometric.DeRham.affineDegreeEquiv A 1)

/-- Ordinary degree-one coordinates are the existing geometric de Rham realization. -/
@[simp]
theorem coe_degreeOneEquiv (A : Arrangement k V) (x : A →₀ k) :
    (degreeOneEquiv A x : HdR ((Daff).complement A)) =
      Geometric.DeRham.affineEquiv A (osDegreeOneEquiv k A x) := rfl

/-- Any equation of a hyperplane gives the same ordinary logarithmic basis class. -/
theorem degreeOneEquiv_single_of_isEquation (A : Arrangement k V) (H : A)
    {f : V →ᵃ[k] k} (hf : IsEquation f H) :
    (degreeOneEquiv A (Finsupp.single H 1) : HdR ((Daff).complement A)) =
      OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections ((Daff).complement A).obj)
        (Geometric.complementUnit A f (hf.covers H.property)) := by
  rw [coe_degreeOneEquiv, osDegreeOneEquiv_single, one_smul]
  exact Geometric.DeRham.affineEquiv_generator_of_isEquation H hf

/-- The ordinary and weighted canonical degree-one coordinates agree under untwisting. -/
theorem componentUntwist_degreeOneEquiv (A : Arrangement k V) (x : A →₀ k) :
    componentUntwist ((Daff).complement A) 1 (Cohomology.degreeOneEquiv Tdr A x) =
      degreeOneEquiv A x := by
  apply Subtype.ext
  exact (componentUntwist_apply ((Daff).complement A) 1 _).trans
    (Geometric.DeRham.affineEquiv_apply _ _).symm

/-- The component comparison typed on the named ordinary and weighted H¹ carriers. -/
def degreeOneUntwist (A : Arrangement k V) :
    Cohomology.degreeOne Tdr A ≃ₗ[k] degreeOne A :=
  componentUntwist ((Daff).complement A) 1

/-- The component comparison typed on the named ordinary and weighted H² carriers. -/
def degreeTwoUntwist (A : Arrangement k V) :
    Cohomology.degreeTwo Tdr A ≃ₗ[k] degreeTwo A :=
  componentUntwist ((Daff).complement A) 2

/-- The H¹ comparison forgets the Laurent weight of every actual class. -/
@[simp]
theorem coe_degreeOneUntwist (A : Arrangement k V) (x : Cohomology.degreeOne Tdr A) :
    (degreeOneUntwist A x : HdR ((Daff).complement A)) =
      Geometric.DeRham.untwist ((Daff).complement A) x :=
  componentUntwist_apply _ 1 x

/-- The H² comparison forgets the Laurent weight of every actual class. -/
@[simp]
theorem coe_degreeTwoUntwist (A : Arrangement k V) (x : Cohomology.degreeTwo Tdr A) :
    (degreeTwoUntwist A x : HdR ((Daff).complement A)) =
      Geometric.DeRham.untwist ((Daff).complement A) x :=
  componentUntwist_apply _ 2 x

/-- The named H¹ comparison identifies the two canonical hyperplane bases. -/
@[simp]
theorem degreeOneUntwist_degreeOneEquiv (A : Arrangement k V) (x : A →₀ k) :
    degreeOneUntwist A (Cohomology.degreeOneEquiv Tdr A x) = degreeOneEquiv A x :=
  componentUntwist_degreeOneEquiv A x

/-- The named H¹ comparison commutes with actual pullback between complements, including
the scalar-line complement used by every marking. -/
theorem degreeOneUntwist_naturality {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (A : Arrangement k V) (A' : Arrangement k W)
    (f : (Daff).complement A ⟶ (Daff).complement A') :
    (degreeOneUntwist A).toLinearMap.comp (Cohomology.componentPull Tdr f 1) =
      (componentPull f 1).comp (degreeOneUntwist A').toLinearMap :=
  componentUntwist_naturality f 1

/-- The existing full de Rham equivalence is the diagonal comparison followed by
ordinary untwisting. -/
@[simp]
theorem diagonalUntwist_diagonalEquiv (A : Arrangement k V) (x : OSAlgebra k A) :
    diagonalUntwist ((Daff).complement A) ((Tdr).diagonalEquiv A x) =
      Geometric.DeRham.affineEquiv A x := rfl

/-- The actual ordinary alternating cup map. It is transported from A04's actual cup map;
the generator formula below identifies it with ordinary multiplication on all classes. -/
def cupMap (A : Arrangement k V) : (⋀[k]^2 (degreeOne A)) →ₗ[k] degreeTwo A :=
  (degreeTwoUntwist A).toLinearMap.comp
    ((Cohomology.cupMap Tdr A).comp
      (exteriorPower.map 2 (degreeOneUntwist A).symm.toLinearMap))

/-- On an arbitrary two-vector the ordinary cup map is literal multiplication. -/
@[simp]
theorem coe_cupMap_ιMulti (A : Arrangement k V) (x : Fin 2 → degreeOne A) :
    (cupMap A (exteriorPower.ιMulti k 2 x) : HdR ((Daff).complement A)) =
      (x 0 : HdR ((Daff).complement A)) * (x 1 : HdR ((Daff).complement A)) := by
  change (degreeTwoUntwist A (Cohomology.cupMap Tdr A
    (exteriorPower.map 2 (degreeOneUntwist A).symm.toLinearMap
      (exteriorPower.ιMulti k 2 x))) : HdR ((Daff).complement A)) = _
  rw [coe_degreeTwoUntwist, exteriorPower.map_apply_ιMulti,
    Cohomology.coe_cupMap_ιMulti, map_mul]
  simp only [← coe_degreeOneUntwist, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- The cup of an arbitrary pair is the product of their actual ordinary classes. -/
theorem coe_cupMap_pair (A : Arrangement k V) (x y : degreeOne A) :
    (cupMap A (exteriorPower.ιMulti k 2 ![x, y]) : HdR ((Daff).complement A)) =
      (x : HdR ((Daff).complement A)) * (y : HdR ((Daff).complement A)) :=
  coe_cupMap_ιMulti A ![x, y]

/-- Ordinary and weighted actual cup maps form an exact commuting square. -/
theorem cupMap_untwist (A : Arrangement k V) :
    (degreeTwoUntwist A).toLinearMap.comp
        (Cohomology.cupMap Tdr A) =
      (cupMap A).comp
        (exteriorPower.map 2 (degreeOneUntwist A).toLinearMap) := by
  unfold cupMap
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← exteriorPower.map_comp,
    LinearEquiv.symm_comp, exteriorPower.map_id, LinearMap.comp_id]

/-- The entire weighted actual cup kernel maps onto the entire ordinary cup kernel.
Blueprint: the full kernel comparison in E03 (`cor:e03`). -/
theorem map_cupKernel_untwist (A : Arrangement k V) :
    (LinearMap.ker (Cohomology.cupMap Tdr A)).map
        (exteriorPower.map 2 (degreeOneUntwist A).toLinearMap) =
      LinearMap.ker (cupMap A) := by
  have h : (LinearMap.ker (cupMap A)).comap
      (exteriorPower.map 2 (degreeOneUntwist A).toLinearMap) =
      LinearMap.ker (Cohomology.cupMap Tdr A) := by
    rw [← LinearMap.ker_comp, ← cupMap_untwist]
    exact LinearEquiv.ker_comp (degreeTwoUntwist A) _
  have hs : Function.Surjective (exteriorPower.map 2 (degreeOneUntwist A).toLinearMap) :=
    exteriorPower.map_surjective (degreeOneUntwist A).surjective
  exact (congrArg (Submodule.map (exteriorPower.map 2 (degreeOneUntwist A).toLinearMap))
    h.symm).trans (Submodule.map_comap_eq_of_surjective hs _)

/-- The ordinary cup kernel at the common two-puncture target is its whole exterior square.
No rational point of a complement is required. -/
theorem target_cupKernel_eq_top :
    LinearMap.ker (cupMap (twoPunctureArrangement k)) = ⊤ := by
  have h := map_cupKernel_untwist (twoPunctureArrangement k)
  let e := exteriorPower.map 2 (degreeOneUntwist (twoPunctureArrangement k)).toLinearMap
  have hs : Function.Surjective
      (exteriorPower.map 2 (degreeOneUntwist (twoPunctureArrangement k)).toLinearMap) :=
    exteriorPower.map_surjective (degreeOneUntwist (twoPunctureArrangement k)).surjective
  exact h.symm.trans ((congrArg (Submodule.map e)
    (Cohomology.target_cupKernel_eq_top Tdr)).trans
      ((Submodule.map_top e).trans (LinearMap.range_eq_top.mpr hs)))

/-- All ordinary degree-one cup products on the common target vanish. -/
theorem target_cupMap_eq_zero : cupMap (twoPunctureArrangement k) = 0 :=
  LinearMap.ker_eq_top.mp target_cupKernel_eq_top

/-- Ordinary canonical coordinates identify actual inclusion pullback with extension by
zero on the hyperplane labels. -/
theorem degreeOneEquiv_inclusion {A A' : Arrangement k V} (hA : A ≤ A') :
    (componentPull ((Daff).complementInclusion hA) 1).comp (degreeOneEquiv A).toLinearMap =
      (degreeOneEquiv A').toLinearMap.comp
      (Finsupp.lmapDomain k k (Arrangement.inclusion hA)) := by
  apply LinearMap.ext
  intro x
  exact (congrArg (componentPull ((Daff).complementInclusion hA) 1)
    (degreeOneUntwist_degreeOneEquiv A x).symm).trans
      ((DFunLike.congr_fun (degreeOneUntwist_naturality A' A
        ((Daff).complementInclusion hA)) (Cohomology.degreeOneEquiv Tdr A x)).symm.trans
        ((congrArg (degreeOneUntwist A')
          (DFunLike.congr_fun (Cohomology.degreeOneEquiv_inclusion Tdr hA) x)).trans
            (degreeOneUntwist_degreeOneEquiv A' _)))

end Arrangements

/-- Ordered ordinary H¹ coordinates at the one actual two-puncture target. -/
def targetDegreeOneEquiv :
    (Fin 2 →₀ k) ≃ₗ[k] degreeOne (twoPunctureArrangement k) :=
  (Cohomology.targetDegreeOneEquiv Tdr).trans (degreeOneUntwist (twoPunctureArrangement k))

/-- The ordered target coordinates are exactly the actual dlog classes of `t` and `t-1`. -/
@[simp]
theorem coe_targetDegreeOneEquiv_single (a : Fin 2) (c : k) :
    (targetDegreeOneEquiv (Finsupp.single a c) :
      HdR (Cohomology.schemeMarkingTarget Daff)) =
      c • OrlikSolomon.DeRham.dlogClass k
        (A := Geometric.globalSections (Cohomology.schemeMarkingTarget Daff).obj)
        (Cohomology.schemeMarkingTargetUnit Daff a) := by
  change (degreeOneUntwist (twoPunctureArrangement k)
    (Cohomology.targetDegreeOneEquiv Tdr (Finsupp.single a c)) :
      HdR (Cohomology.schemeMarkingTarget Daff)) = _
  rw [coe_degreeOneUntwist, Cohomology.coe_targetDegreeOneEquiv_single]
  exact (map_smul (Geometric.DeRham.untwist _) c _).trans
    (congrArg (c • ·) (Geometric.DeRham.untwist_logClass _))

variable {k₀ : Type v} [Field k₀] [Algebra k₀ k] {S : Set k₀} {n : ℕ}

/-- Ordinary canonical coordinates intertwine actual tagged marking pullback with the
ordered label map. The same target is retained for every stage and tag. -/
theorem degreeOneEquiv_marking (w : Marking S n)
    {A : Arrangement k (Fin n → k)} (hw : w.Available A) :
    (componentPull (w.schemeMap Daff hw) 1).comp targetDegreeOneEquiv.toLinearMap =
      (degreeOneEquiv A).toLinearMap.comp (w.basisMap k hw) := by
  apply LinearMap.ext
  intro x
  exact (DFunLike.congr_fun (degreeOneUntwist_naturality A
    (twoPunctureArrangement k) (w.schemeMap Daff hw))
      (Cohomology.targetDegreeOneEquiv Tdr x)).symm.trans
        ((congrArg (degreeOneUntwist A)
          (DFunLike.congr_fun (Cohomology.degreeOneEquiv_marking Tdr w hw) x)).trans
            (degreeOneUntwist_degreeOneEquiv A _))

/-- The full ordinary de Rham structure theorem commutes with actual inclusions. -/
theorem affineEquiv_inclusion {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {A A' : Arrangement k V} (hA : A ≤ A') :
    (Geometric.DeRham.Cohomology.pull ((Daff).complementInclusion hA)).comp
        (Geometric.DeRham.affineEquiv A).toAlgHom =
      (Geometric.DeRham.affineEquiv A').toAlgHom.comp (OSAlgebra.map k hA) := by
  apply AlgHom.ext
  intro x
  exact (DFunLike.congr_fun (diagonalUntwist_naturality
    ((Daff).complementInclusion hA)) ((Tdr).diagonalEquiv A x)).symm.trans
      (congrArg (diagonalUntwist ((Daff).complement A'))
        (DFunLike.congr_fun (Cohomology.diagonalEquiv_inclusion Tdr hA) x))

/-- The full ordinary de Rham structure theorem commutes with each actual tagged marking,
as an equality on the entire common-target algebra. -/
theorem affineEquiv_marking (w : Marking S n)
    {A : Arrangement k (Fin n → k)} (hw : w.Available A) :
    (Geometric.DeRham.Cohomology.pull (w.schemeMap Daff hw)).comp
        (Geometric.DeRham.affineEquiv (twoPunctureArrangement k)).toAlgHom =
      (Geometric.DeRham.affineEquiv A).toAlgHom.comp (w.osMap k hw) := by
  apply AlgHom.ext
  intro x
  exact (DFunLike.congr_fun (diagonalUntwist_naturality
    (w.schemeMap Daff hw)) ((Tdr).diagonalEquiv (twoPunctureArrangement k) x)).symm.trans
      (congrArg (diagonalUntwist ((Daff).complement A))
        (DFunLike.congr_fun (Cohomology.diagonalEquiv_marking Tdr w hw) x))

end OrlikSolomon.HyperplaneGT.Cohomology.DeRham
