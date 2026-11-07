/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
module

public import OrlikSolomon.Geometry.Schemes.PrincipalPair.Duality

/-!
# Affine neighborhoods of geometric principal pairs

For a geometric principal pair `P = (X, Z, U, f)` and an affine open `V` of `X`,
`affineNeighborhoodPair P V` is the pair of actual open restrictions
`(V, i⁻¹ V, j⁻¹ V, f|V)`. Its three objects are smooth and affine. Smoothness of the
closed and open parts follows from their open inclusions into `Z` and `U`, while
affineness follows from the restricted closed immersion and principal-open certificate.
No closure of the original domain under arbitrary open restrictions is assumed.

`affineNeighborhoodAlgebraicPair` applies the existing affine pair duality to obtain
the smooth algebraic pair of section rings. Its closed part is canonically the quotient
by the equation (`affineNeighborhoodQuotientEquiv`), and its open part is an arbitrary
localization away from that equation through the specified pullback map.
The construction works over any commutative base ring, including unit equations and
empty schemes.

Blueprint: the affine-neighborhood step in `thm:geo-log-sheaves`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace OrlikSolomon.Geometric.DeRham

variable {k : Type u} [CommRing k] {D : SmoothDomain k}

/-- Restrict a geometric principal pair to an affine open of its ambient scheme, as a pair in
`SmoothDomain.aff k`. Its divisor and complement are the literal inverse-image open schemes;
all smoothness and principal-pair certificates are inherited from the original pair.

Blueprint: the affine-neighborhood construction in `thm:geo-log-sheaves`. -/
@[implicit_reducible]
def affineNeighborhoodPair (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) : DivisorPair (SmoothDomain.aff k) := by
  have : IsAffine V.1.toScheme := V.2
  have hi : IsClosedImmersion (P.i.hom.left ∣_ V.1) :=
    IsZariskiLocalAtTarget.restrict P.isClosedImmersion_i V.1
  have hj : IsOpenImmersion (P.j.hom.left ∣_ V.1) :=
    IsZariskiLocalAtTarget.restrict P.isOpenImmersion_j V.1
  have hjRange : (P.j.hom.left ∣_ V.1).opensRange =
      V.1.toScheme.basicOpen (V.1.ι.appTop P.eqn) := by
    have h := Scheme.Hom.opensRange_comp_of_isIso
      (isPullback_morphismRestrict P.j.hom.left V.1).isoPullback.hom
      (pullback.fst V.1.ι P.j.hom.left)
    simpa only [IsPullback.isoPullback_hom_fst] using
      h.trans (opensRange_pullback_fst_of_opensRange_eq P.opensRange_j V.1.ι)
  have : IsAffine (P.i.hom.left ⁻¹ᵁ V.1).toScheme :=
    isAffine_of_isAffineHom (P.i.hom.left ∣_ V.1)
  have : IsAffine (P.j.hom.left ⁻¹ᵁ V.1).toScheme :=
    isAffine_of_opensRange_eq hjRange
  exact {
    ambient := ⟨Over.mk (V.1.ι ≫ P.ambient.obj.hom),
      inferInstanceAs (IsAffine V.1.toScheme),
      inferInstanceAs (Smooth (V.1.ι ≫ P.ambient.obj.hom))⟩
    closed := ⟨Over.mk ((P.i.hom.left ⁻¹ᵁ V.1).ι ≫ P.closed.obj.hom),
      inferInstanceAs (IsAffine (P.i.hom.left ⁻¹ᵁ V.1).toScheme),
      inferInstanceAs (Smooth ((P.i.hom.left ⁻¹ᵁ V.1).ι ≫ P.closed.obj.hom))⟩
    compl := ⟨Over.mk ((P.j.hom.left ⁻¹ᵁ V.1).ι ≫ P.compl.obj.hom),
      inferInstanceAs (IsAffine (P.j.hom.left ⁻¹ᵁ V.1).toScheme),
      inferInstanceAs (Smooth ((P.j.hom.left ⁻¹ᵁ V.1).ι ≫ P.compl.obj.hom))⟩
    i := ObjectProperty.homMk (Over.homMk (P.i.hom.left ∣_ V.1) (by
      dsimp
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w]))
    j := ObjectProperty.homMk (Over.homMk (P.j.hom.left ∣_ V.1) (by
      dsimp
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w]))
    eqn := V.1.ι.appTop P.eqn
    isRegularSection_eqn := by
      intro W
      change P.ambient.obj.left.presheaf.map
          (homOfLE (V.1.ι.image_mono (le_top : W ≤ ⊤))).op
        (P.ambient.obj.left.presheaf.map (homOfLE le_top).op P.eqn) ∈
          nonZeroDivisors Γ(P.ambient.obj.left, V.1.ι ''ᵁ W)
      rw [presheaf_map_presheaf_map]
      exact P.isRegularSection_eqn _
    isClosedImmersion_i := hi
    ker_i := by
      change (P.i.hom.left ∣_ V.1).ker = principalIdealSheaf (V.1.ι.appTop P.eqn)
      rw [← (isPullback_morphismRestrict P.i.hom.left V.1).isoPullback_hom_fst,
        Scheme.Hom.ker_comp_of_isIso]
      exact ker_pullback_fst_of_ker_eq P.ker_i V.1.ι
    isOpenImmersion_j := hj
    opensRange_j := hjRange }


/-- The ambient is the affine open scheme with the restricted structure map to the base. -/
lemma affineNeighborhoodPair_ambient_obj (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).ambient.obj = Over.mk (V.1.ι ≫ P.ambient.obj.hom) := rfl

/-- The divisor is the inverse-image open scheme in the original divisor. -/
lemma affineNeighborhoodPair_closed_obj (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).closed.obj =
      Over.mk ((P.i.hom.left ⁻¹ᵁ V.1).ι ≫ P.closed.obj.hom) := rfl

/-- The complement is the inverse-image open scheme in the original complement. -/
lemma affineNeighborhoodPair_compl_obj (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).compl.obj =
      Over.mk ((P.j.hom.left ⁻¹ᵁ V.1).ι ≫ P.compl.obj.hom) := rfl

/-- The local equation is the restriction of the global equation. -/
@[simp] lemma affineNeighborhoodPair_eqn (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).eqn = V.1.ι.appTop P.eqn := rfl

/-- The closed map is the restriction of the original closed immersion. -/
@[simp] lemma affineNeighborhoodPair_i_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).i.hom.left = P.i.hom.left ∣_ V.1 := rfl

/-- The open map is the restriction of the original open immersion. -/
@[simp] lemma affineNeighborhoodPair_j_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodPair P V).j.hom.left = P.j.hom.left ∣_ V.1 := rfl

/-- The open inclusions of the three restricted schemes form a transverse map to the original
pair in its original domain. The equation multiplier is `1`. -/
def affineNeighborhoodInclusion (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    DivisorPair.ofLE (SmoothDomain.aff_le D) (affineNeighborhoodPair P V) ⟶ P where
  ambient := ObjectProperty.homMk (Over.homMk V.1.ι rfl)
  closed := ObjectProperty.homMk (Over.homMk (P.i.hom.left ⁻¹ᵁ V.1).ι rfl)
  compl := ObjectProperty.homMk (Over.homMk (P.j.hom.left ⁻¹ᵁ V.1).ι rfl)
  i_comp := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (morphismRestrict_ι _ _))
  j_comp := ObjectProperty.hom_ext _ (Over.OverMorphism.ext (morphismRestrict_ι _ _))
  associated_eqn := .refl _

/-- The ambient component of the neighborhood inclusion is the open inclusion of `V`. -/
@[simp] lemma affineNeighborhoodInclusion_ambient_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodInclusion P V).ambient.hom.left = V.1.ι := rfl

/-- The divisor component of the neighborhood inclusion is its inverse-image open inclusion. -/
@[simp] lemma affineNeighborhoodInclusion_closed_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodInclusion P V).closed.hom.left = (P.i.hom.left ⁻¹ᵁ V.1).ι := rfl

/-- The complement component of the neighborhood inclusion is its inverse-image open inclusion. -/
@[simp] lemma affineNeighborhoodInclusion_compl_left (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodInclusion P V).compl.hom.left = (P.j.hom.left ⁻¹ᵁ V.1).ι := rfl

/-- The smooth algebraic principal pair of section rings on an affine neighborhood.
The specified maps are precisely pullback along the restricted immersions, and the
localization certificate applies to the actual section ring of the open complement.

Blueprint: the algebraic local input to `thm:geo-log-sheaves`. -/
@[implicit_reducible]
def affineNeighborhoodAlgebraicPair (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) : OrlikSolomon.DivisorPair k :=
  DivisorPair.globalSections (affineNeighborhoodPair P V)

/-- The algebraic equation is the same restricted regular function. -/
@[simp] lemma affineNeighborhoodAlgebraicPair_eqn (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    (affineNeighborhoodAlgebraicPair P V).eqn = V.1.ι.appTop P.eqn := rfl

/-- The algebraic closed map pulls functions back along the restricted closed immersion. -/
@[simp] lemma affineNeighborhoodAlgebraicPair_i_apply (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (a : (affineNeighborhoodAlgebraicPair P V).ambient) :
    (affineNeighborhoodAlgebraicPair P V).i a = (P.i.hom.left ∣_ V.1).appTop a := rfl

/-- The algebraic open map pulls functions back along the restricted open immersion. -/
@[simp] lemma affineNeighborhoodAlgebraicPair_j_apply (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (a : (affineNeighborhoodAlgebraicPair P V).ambient) :
    (affineNeighborhoodAlgebraicPair P V).j a = (P.j.hom.left ∣_ V.1).appTop a := rfl

/-- The section ring of the restricted divisor is the quotient of the ambient section ring
by the restricted equation, with no nonemptiness or nontriviality hypothesis. -/
def affineNeighborhoodQuotientEquiv (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) :
    let Q := affineNeighborhoodAlgebraicPair P V
    (Q.ambient ⧸ Ideal.span {Q.eqn}) ≃ₐ[k] Q.closed :=
  (Ideal.quotientEquivAlgOfEq k (affineNeighborhoodAlgebraicPair P V).ker_i.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (affineNeighborhoodAlgebraicPair P V).surjective_i)

/-- The quotient comparison sends the class of a function to its pullback to the divisor. -/
@[simp] lemma affineNeighborhoodQuotientEquiv_mk (P : DivisorPair D)
    (V : P.ambient.obj.left.affineOpens) (a : (affineNeighborhoodAlgebraicPair P V).ambient) :
    affineNeighborhoodQuotientEquiv P V (Ideal.Quotient.mk _ a) =
      (affineNeighborhoodAlgebraicPair P V).i a := by
  simp only [affineNeighborhoodQuotientEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

end OrlikSolomon.Geometric.DeRham
