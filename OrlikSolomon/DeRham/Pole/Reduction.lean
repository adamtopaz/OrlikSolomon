/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Algebra.ComplexReduction
public import OrlikSolomon.DeRham.Pole.Contraction

/-!
# Finite reduction of pole order

A normal derivation modulo `f` contracts each positive pole quotient whose pole order is a unit
in `k`. The two representative statements of finite reduction therefore lower a cocycle or a
primitive by one pole stage. Exhaustivity and induction on a natural-number pole bound give the
two form-level assertions used by logarithmic comparison. There is no infinite limiting argument.

## Main results

* `OrlikSolomon.DeRham.exists_pole_cocycle_reduction`: subtract a boundary in the same pole stage
  to lower a cocycle by one step.
* `OrlikSolomon.DeRham.exists_pole_primitive_reduction`: lower a primitive whose differential is
  already in the preceding stage.
* `OrlikSolomon.DeRham.exists_closed_logForm_sub_d_eq`: every localized cocycle is cohomologous
  to a logarithmic cocycle.
* `OrlikSolomon.DeRham.exists_logPrimitive_of_exists`: an ambient primitive of a logarithmic form
  can be replaced by a logarithmic primitive.

Blueprint: `lem:dr-filtration-reduction` and the finite inductions of `thm:dr-comparison`.
-/

@[expose] public section

namespace OrlikSolomon.DeRham

variable (k : Type*) [CommRing k] {A : Type*} [CommRing A] [Algebra k A]
  (f : A) (T : Type*) [CommRing T] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
  [IsLocalization.Away f T]

/-- Lower a closed form by one pole stage by subtracting a boundary in its original stage.

Blueprint: the cocycle assertion of `lem:dr-filtration-reduction`. -/
theorem exists_pole_cocycle_reduction (m : ℕ) (v : Derivation k A A) (h : A)
    (hv : v f = 1 + f * h) (hm : IsUnit (m + 1 : k))
    (x : Forms k T) (hx : x ∈ poleForms k f T (m + 1)) (hd : d k x = 0) :
    ∃ b ∈ poleForms k f T (m + 1), x - d k b ∈ poleForms k f T m ∧
      d k (x - d k b) = 0 := by
  have hker : LinearMap.ker ((poleQuotientProjection k f T m).restrictScalars k) =
      (polePrevious k f T m).restrictScalars k := by
    change (LinearMap.ker (poleQuotientProjection k f T m)).restrictScalars k = _
    rw [ker_poleQuotientProjection]
  obtain ⟨b, hb, hdb⟩ := exists_cocycle_reduction_of_contractible_quotient
    (poleD k f T (m + 1)) (LinearMap.ext (poleD_poleD k f T (m + 1)))
    ((polePrevious k f T m).restrictScalars k)
    ((poleQuotientProjection k f T m).restrictScalars k)
    (poleQuotientProjection_surjective k f T m) hker
    (poleQuotientDifferential k f T m) (positivePoleHomotopy k f T m v hm)
    (LinearMap.ext (poleQuotientProjection_poleD k f T m))
    (LinearMap.ext (positivePoleQuotientContractible k f T m v h hv hm))
    (⟨x, hx⟩ : poleForms k f T (m + 1)) (Subtype.ext hd)
  exact ⟨b, b.property, hb, congrArg Subtype.val hdb⟩

/-- A primitive whose differential already has a smaller pole bound can be replaced by a
primitive with that smaller bound.

Blueprint: the primitive assertion of `lem:dr-filtration-reduction`. -/
theorem exists_pole_primitive_reduction (m : ℕ) (v : Derivation k A A) (h : A)
    (hv : v f = 1 + f * h) (hm : IsUnit (m + 1 : k))
    (y : Forms k T) (hy : y ∈ poleForms k f T (m + 1)) (hdy : d k y ∈ poleForms k f T m) :
    ∃ x ∈ poleForms k f T m, d k x = d k y := by
  have hker : LinearMap.ker ((poleQuotientProjection k f T m).restrictScalars k) =
      (polePrevious k f T m).restrictScalars k := by
    change (LinearMap.ker (poleQuotientProjection k f T m)).restrictScalars k = _
    rw [ker_poleQuotientProjection]
  obtain ⟨x, hx, hdx⟩ := exists_primitive_reduction_of_contractible_quotient
    (poleD k f T (m + 1)) (LinearMap.ext (poleD_poleD k f T (m + 1)))
    ((polePrevious k f T m).restrictScalars k)
    ((poleQuotientProjection k f T m).restrictScalars k)
    (poleQuotientProjection_surjective k f T m) hker
    (poleQuotientDifferential k f T m) (positivePoleHomotopy k f T m v hm)
    (LinearMap.ext (poleQuotientProjection_poleD k f T m))
    (LinearMap.ext (positivePoleQuotientContractible k f T m v h hv hm))
    (⟨y, hy⟩ : poleForms k f T (m + 1)) hdy
  exact ⟨x, hx, congrArg Subtype.val hdx⟩

/-- Finite induction on the pole bound replaces every localized cocycle by a cohomologous
logarithmic cocycle. The displayed exact difference is the surjectivity input for the canonical
map on cohomology.

Blueprint: the surjectivity argument of `thm:dr-comparison`. -/
theorem exists_closed_logForm_sub_d_eq (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    (v : Derivation k A A) (h : A) (hv : v f = 1 + f * h)
    (x : Forms k T) (hd : d k x = 0) :
    ∃ y : logForms k f T, logD k f T y = 0 ∧ ∃ z, d k z = x - (y : Forms k T) := by
  have aux (m : ℕ) (x : Forms k T) (hx : x ∈ poleForms k f T m) (hd : d k x = 0) :
      ∃ a ∈ poleForms k f T 0, d k a = 0 ∧ ∃ b : Forms k T, x - a = d k b := by
    induction m generalizing x with
    | zero => exact ⟨x, hx, hd, 0, by simp⟩
    | succ m ih =>
      obtain ⟨b, _, hb, hdb⟩ := exists_pole_cocycle_reduction k f T m v h hv (hUnits m) x hx hd
      obtain ⟨a, ha, hda, c, hc⟩ := ih (x - d k b) hb hdb
      refine ⟨a, ha, hda, c + b, ?_⟩
      rw [map_add, ← hc]
      abel
  obtain ⟨m, hm⟩ := exists_mem_poleForms k f T x
  obtain ⟨a, ha, hda, b, hb⟩ := aux m x hm hd
  refine ⟨⟨a, ?_⟩, Subtype.ext hda, b, hb.symm⟩
  simpa only [poleForms_zero, Subalgebra.mem_toSubmodule] using ha

/-- Finite induction on a primitive's pole bound produces a logarithmic primitive whenever a
logarithmic form is exact among all localized forms. Closedness need not be assumed separately.

Blueprint: the injectivity argument of `thm:dr-comparison`. -/
theorem exists_logPrimitive_of_exists (hUnits : ∀ n : ℕ, IsUnit (n + 1 : k))
    (v : Derivation k A A) (h : A) (hv : v f = 1 + f * h)
    (x : logForms k f T) (hex : ∃ y : Forms k T, d k y = (x : Forms k T)) :
    ∃ y : logForms k f T, logD k f T y = x := by
  have hx : (x : Forms k T) ∈ poleForms k f T 0 := by
    simpa only [poleForms_zero, Subalgebra.mem_toSubmodule] using x.property
  have aux (m : ℕ) (y : Forms k T) (hy : y ∈ poleForms k f T m)
      (hdy : d k y = (x : Forms k T)) :
      ∃ a ∈ poleForms k f T 0, d k a = (x : Forms k T) := by
    induction m generalizing y with
    | zero => exact ⟨y, hy, hdy⟩
    | succ m ih =>
      obtain ⟨a, ha, hda⟩ := exists_pole_primitive_reduction k f T m v h hv (hUnits m) y hy
        (by rw [hdy]; exact poleForms_monotone k f T (Nat.zero_le m) hx)
      exact ih a ha (hda.trans hdy)
  obtain ⟨y, hy⟩ := hex
  obtain ⟨m, hm⟩ := exists_mem_poleForms k f T y
  obtain ⟨a, ha, hda⟩ := aux m y hm hy
  exact ⟨⟨a, by simpa only [poleForms_zero, Subalgebra.mem_toSubmodule] using ha⟩, Subtype.ext hda⟩

end OrlikSolomon.DeRham
