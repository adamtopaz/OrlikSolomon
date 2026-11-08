/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# The conditional Mayer–Vietoris computation for the projective line

After the affine de Rham computations, the two chart groups are `k × k` in degree zero and
zero in positive degrees. The overlap groups are `k` in degrees zero and one and zero above
one. The chart-to-overlap map in degree zero is `(a, b) ↦ b - a`.

`ProjectiveLineMayerVietorisData` records a nonnegative graded family with restriction and
boundary maps forming the normalized Mayer–Vietoris long exact sequence. Its exactness
implies that the global groups are `k` in degrees zero and two and zero otherwise. The
second-degree generator is the boundary of the chosen overlap logarithmic generator.

The algebraic implication holds over every commutative ring. Applying it to a de Rham
extension uses the characteristic-zero affine computations and the extension's two-open
Mayer–Vietoris exact sequence, including compatibility of the restriction maps.

Blueprint: the universal conditional assertion in `prop:geo-nonaffine`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace OrlikSolomon.Geometric.Examples

variable (k : Type u) [CommRing k]

/-- The normalized affine-chart groups: `k × k` in degree zero and zero otherwise. -/
@[implicit_reducible]
def projectiveLineMVCharts : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k (k × k)
  | _ + 1 => ModuleCat.of k PUnit.{u + 1}

/-- The normalized Laurent-overlap groups: `k` in degrees zero and one and zero otherwise. -/
@[implicit_reducible]
def projectiveLineMVOverlap : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k k
  | 1 => ModuleCat.of k k
  | _ + 2 => ModuleCat.of k PUnit.{u + 1}

/-- The normalized chart groups vanish in positive degrees. -/
instance projectiveLineMVCharts_subsingleton (n : ℕ) :
    Subsingleton (projectiveLineMVCharts k (n + 1)) := by
  change Subsingleton PUnit
  infer_instance

/-- The normalized overlap groups vanish above degree one. -/
instance projectiveLineMVOverlap_subsingleton (n : ℕ) :
    Subsingleton (projectiveLineMVOverlap k (n + 2)) := by
  change Subsingleton PUnit
  infer_instance

/-- The normalized difference of chart restrictions: `(a, b) ↦ b - a` in degree zero. -/
def projectiveLineMVDifference :
    (n : ℕ) → projectiveLineMVCharts k n →ₗ[k] projectiveLineMVOverlap k n
  | 0 => LinearMap.snd k k k - LinearMap.fst k k k
  | _ + 1 => 0

/-- In degree zero the normalized difference is second minus first. -/
@[simp]
lemma projectiveLineMVDifference_zero_apply (a b : k) :
    projectiveLineMVDifference k 0 (a, b) = b - a := rfl

/-- The normalized difference vanishes in positive degrees. -/
@[simp]
lemma projectiveLineMVDifference_succ (n : ℕ) :
    projectiveLineMVDifference k (n + 1) = 0 := rfl

/-- The normalized nonnegative Mayer–Vietoris long exact sequence for the projective-line cover.
The affine chart and overlap computations fix the intermediate groups and their difference map;
the fields record restriction, connecting maps, and exactness.

Blueprint: the conditional Mayer–Vietoris conclusion of `prop:geo-nonaffine`. -/
structure ProjectiveLineMayerVietorisData (H : ℕ → ModuleCat.{u} k) where
  /-- Restriction to the normalized pair of affine-chart cohomology groups. -/
  restrict (n : ℕ) : H n →ₗ[k] projectiveLineMVCharts k n
  /-- The connecting map from overlap degree `n` to global degree `n + 1`. -/
  boundary (n : ℕ) : projectiveLineMVOverlap k n →ₗ[k] H (n + 1)
  /-- The first restriction is injective because overlap degree `-1` vanishes. -/
  restrict_zero_injective : Function.Injective (restrict 0)
  /-- Exactness at the sum of the two chart groups. -/
  exact_restrict_difference (n : ℕ) : Function.Exact (restrict n) (projectiveLineMVDifference k n)
  /-- Exactness at the overlap group. -/
  exact_difference_boundary (n : ℕ) : Function.Exact (projectiveLineMVDifference k n) (boundary n)
  /-- Exactness at global degree `n + 1`. -/
  exact_boundary_restrict (n : ℕ) : Function.Exact (boundary n) (restrict (n + 1))

namespace ProjectiveLineMayerVietorisData

variable {k} {H : ℕ → ModuleCat.{u} k} (M : ProjectiveLineMayerVietorisData k H)

/-- The two chart coefficients of a global degree-zero class agree. -/
lemma restrict_zero_diag (x : H 0) : (M.restrict 0 x).2 = (M.restrict 0 x).1 := by
  have h := (M.exact_restrict_difference 0).apply_apply_eq_zero x
  exact sub_eq_zero.mp h

/-- The first chart coefficient of a global degree-zero class. -/
def zeroCoefficient : H 0 →ₗ[k] k := (LinearMap.fst k k k).comp (M.restrict 0)

/-- Every diagonal constant comes from a unique global degree-zero class. -/
private lemma zeroCoefficient_bijective : Function.Bijective M.zeroCoefficient := by
  constructor
  · intro x y h
    apply M.restrict_zero_injective
    apply Prod.ext h
    exact (M.restrict_zero_diag x).trans (h.trans (M.restrict_zero_diag y).symm)
  · intro c
    obtain ⟨x, hx⟩ := ((M.exact_restrict_difference 0) (c, c)).mp (sub_self c)
    exact ⟨x, congrArg Prod.fst hx⟩

/-- Every normalized Mayer–Vietoris sequence has degree-zero group `k`. -/
def homologyZeroEquiv : H 0 ≃ₗ[k] k :=
  LinearEquiv.ofBijective M.zeroCoefficient (by exact M.zeroCoefficient_bijective)

/-- The degree-zero equivalence reads the first chart coefficient. -/
@[simp]
lemma homologyZeroEquiv_apply (x : H 0) : M.homologyZeroEquiv x = (M.restrict 0 x).1 := rfl

/-- A scalar corresponds to a global class restricting to that scalar on both charts. -/
@[simp]
lemma restrict_homologyZeroEquiv_symm (c : k) :
    M.restrict 0 (M.homologyZeroEquiv.symm c) = (c, c) := by
  have h := M.homologyZeroEquiv.apply_symm_apply c
  apply Prod.ext h
  exact (M.restrict_zero_diag _).trans h

/-- The connecting map out of overlap degree zero vanishes, since `b - a` is surjective. -/
lemma boundary_zero (c : k) : M.boundary 0 c = 0 := by
  have h := (M.exact_difference_boundary 0).apply_apply_eq_zero (0, c)
  change M.boundary 0 (c - (0 : k)) = 0 at h
  simpa only [sub_zero] using h

include M in
/-- The degree-one global group vanishes in every normalized Mayer–Vietoris sequence. -/
lemma homologyOne_subsingleton : Subsingleton (H 1) := by
  have hz (x : H 1) : x = 0 := by
    obtain ⟨c, hc⟩ := ((M.exact_boundary_restrict 0) x).mp (Subsingleton.elim _ _)
    exact hc.symm.trans (M.boundary_zero c)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The boundary identifies overlap degree one with global degree two. -/
private lemma boundary_one_bijective : Function.Bijective (M.boundary 1) := by
  constructor
  · exact (LinearMap.injective_iff_eq_zero_of_exact (M.exact_difference_boundary 1)).mpr rfl
  · intro x
    exact ((M.exact_boundary_restrict 1) x).mp (Subsingleton.elim _ _)

/-- Every normalized Mayer–Vietoris sequence has degree-two group `k`, via the boundary. -/
def homologyTwoEquiv : H 2 ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (M.boundary 1) (by exact M.boundary_one_bijective)).symm

/-- The degree-two equivalence returns the coefficient of a boundary class. -/
@[simp]
lemma homologyTwoEquiv_boundary (c : k) : M.homologyTwoEquiv (M.boundary 1 c) = c :=
  (LinearEquiv.ofBijective (M.boundary 1) (by exact M.boundary_one_bijective)).symm_apply_apply c

/-- The inverse degree-two equivalence is the connecting map from overlap degree one. -/
@[simp]
lemma homologyTwoEquiv_symm_apply (c : k) : M.homologyTwoEquiv.symm c = M.boundary 1 c := rfl

include M in
/-- The global groups above degree two vanish in every normalized Mayer–Vietoris sequence. -/
lemma homologyHigh_subsingleton (n : ℕ) : Subsingleton (H (n + 3)) := by
  have hz (x : H (n + 3)) : x = 0 := by
    obtain ⟨c, hc⟩ := ((M.exact_boundary_restrict (n + 2)) x).mp (Subsingleton.elim _ _)
    have hc0 : c = 0 := Subsingleton.elim _ _
    rw [hc0, map_zero] at hc
    exact hc.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The degree-two boundary of the chosen overlap generator `[dT/T]`. -/
def boundaryGenerator : H 2 := M.boundary 1 (1 : k)

/-- The boundary of the overlap generator has coefficient one. -/
@[simp]
lemma homologyTwoEquiv_boundaryGenerator : M.homologyTwoEquiv M.boundaryGenerator = 1 :=
  M.homologyTwoEquiv_boundary 1

/-- The boundary generator is nonzero when the coefficient ring is nontrivial. -/
lemma boundaryGenerator_ne_zero [Nontrivial k] : M.boundaryGenerator ≠ 0 := by
  intro h
  have hh := M.homologyTwoEquiv_boundaryGenerator
  rw [h, map_zero] at hh
  exact zero_ne_one hh

end ProjectiveLineMayerVietorisData

end OrlikSolomon.Geometric.Examples
