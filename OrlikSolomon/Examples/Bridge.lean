/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Cohomology.Bridge
public import OrlikSolomon.Examples.Sanity

/-!
# Zero inputs for the standard localization bridge

The zero coefficient ring gives degreewise cohomology and supported cohomology consisting of
zero groups. These inputs check that the standard bridge permits the zero coefficient ring,
all integer degrees and weights, and every certified divisor pair. They are consistency checks
of the interface rather than checks of the substantive cohomology axioms.

Blueprint: `lem:standard-bridge` and the zero-coefficient-ring regression.
-/

@[expose] public section

noncomputable section

universe u v w z t

namespace OrlikSolomon.Sanity

/-- Zero degreewise cohomology, with zero coefficients, on every smooth algebra. -/
def zeroDegreewiseTheory (k : Type u) [CommRing k] :
    DegreewiseTheory.{u, v, w, z} k zeroWeight.{v, w} where
  H _ _ := PUnit.{z + 1}
  coeff _ _ := 0
  coeff_one _ := Subsingleton.elim _ _
  coeff_mul _ _ _ _ _ := Subsingleton.elim _ _
  bijective_algebraMap_gradeZero :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  graded_comm _ _ _ _ _ := Sigma.ext (add_comm _ _) (heq_of_eq (Subsingleton.elim _ _))
  map _ _ := 0
  map_id _ _ _ := Subsingleton.elim _ _
  map_comp _ _ _ _ := Subsingleton.elim _ _
  map_one _ := Subsingleton.elim _ _
  map_mul _ _ _ _ _ := Subsingleton.elim _ _
  map_coeff _ _ _ := Subsingleton.elim _ _
  bijective_coeff_point _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  eq_zero_point _ _ := Subsingleton.elim _ _
  bijective_map_polynomialC _ _ :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

instance {k : Type u} [CommRing k] (A : SmoothAlg k) (i : ℤ × ℤ) :
    Subsingleton ((zeroDegreewiseTheory.{u, v, w, z} k).H A i) :=
  inferInstanceAs (Subsingleton PUnit)

/-- Zero supported cohomology, with its localization sequence and oriented purity. Every map
has its prescribed source and target degree, including negative cohomological degrees. -/
def zeroSupportsAndPurity (k : Type u) [CommRing k] :
    SupportsAndPurity.{u, v, w, z, t} (zeroDegreewiseTheory.{u, v, w, z} k) where
  support _ _ := PUnit.{t + 1}
  forget _ _ := 0
  boundary _ _ := 0
  purity _ _ :=
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ 0
      left_inv _ := Subsingleton.elim _ _
      right_inv _ := Subsingleton.elim _ _
      map_add' _ _ := Subsingleton.elim _ _
      map_smul' _ _ := Subsingleton.elim _ _ }
  exact_forget_map _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_map_boundary _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  exact_boundary_forget _ _ _ :=
    ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  supportMap _ _ := 0
  forget_natural _ _ _ := Subsingleton.elim _ _
  boundary_natural _ _ _ := Subsingleton.elim _ _
  purity_natural _ _ _ := Subsingleton.elim _ _
  supportMul _ _ _ := 0
  forget_mul _ _ _ _ _ := Subsingleton.elim _ _
  purity_mul _ _ _ _ _ := Sigma.ext (by abel_nf) (heq_of_eq (Subsingleton.elim _ _))
  boundary_mul _ _ _ _ _ := Sigma.ext (by abel_nf) (heq_of_eq (Subsingleton.elim _ _))

instance {k : Type u} [CommRing k] (P : DivisorPair k) (i : ℤ × ℤ) :
    Subsingleton ((zeroSupportsAndPurity.{u, v, w, z, t} k).support P i) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The ordinary theory produced by the standard bridge from the zero degreewise inputs.
Blueprint: `lem:standard-bridge`. -/
def zeroBridgeTheory (k : Type u) [CommRing k] :
    OrdinaryTheory.{u, v, w, z} k zeroWeight.{v, w} :=
  ofSupportsAndPurity (zeroDegreewiseTheory.{u, v, w, z} k)
    (zeroSupportsAndPurity.{u, v, w, z, t} k)

/-- Summing the zero degreewise inputs gives zero total cohomology on every object. -/
instance {k : Type u} [CommRing k] (A : SmoothAlg k) :
    Subsingleton ((zeroBridgeTheory.{u, v, w, z, t} k).C.obj A) :=
  inferInstanceAs (Subsingleton ((zeroDegreewiseTheory.{u, v, w, z} k).Total A))

/-- The Gysin map obtained from zero supported cohomology is zero on every divisor pair. -/
theorem zeroBridgeTheory_gysin (k : Type u) [CommRing k] (P : DivisorPair k) :
    (zeroBridgeTheory.{u, v, w, z, t} k).gysin P = 0 :=
  LinearMap.ext fun _ ↦ Subsingleton.elim _ _

/-- The residue obtained from zero supported cohomology is zero on every divisor pair. -/
theorem zeroBridgeTheory_residue (k : Type u) [CommRing k] (P : DivisorPair k) :
    (zeroBridgeTheory.{u, v, w, z, t} k).residue P = 0 :=
  LinearMap.ext fun _ ↦ Subsingleton.elim _ _

/-- With `R = B = PUnit` in the same universe, the constructed Gysin and residue maps act on
homogeneous components with the prescribed shifts. This also checks the coincident scalar
structures of the total direct sum. -/
theorem zeroBridgeTheory_same_universe (k : Type u) [CommRing k] (P : DivisorPair k)
    (i : ℤ × ℤ) :
    let T := zeroBridgeTheory.{u, v, v, v, v} k
    ∀ (x : T.C.obj P.closed) (y : T.C.obj P.compl),
      T.gysin P (DirectSum.decompose (T.grading P.closed) x i) ∈
          T.grading P.ambient (i + (2, 1)) ∧
        T.residue P (DirectSum.decompose (T.grading P.compl) y i) ∈
          T.grading P.closed (i + (-1, -1)) := by
  intro T x y
  exact ⟨T.isHomogeneousOfShift_gysin P (DirectSum.decompose _ _ _).2,
    T.isHomogeneousOfShift_residue P (DirectSum.decompose _ _ _).2⟩

end OrlikSolomon.Sanity
