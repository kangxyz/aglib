/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionBaseChangeGeometry
public import Aglib.AlgebraicGeometry.Compactification.Refinements.ClosedAmbient
public import Aglib.AlgebraicGeometry.Compactification.Refinements.OpenSquare

/-! # Actual refinements to normalized Cartesian compactifications

An actual ambient map over the base and the open source factors through the
closed normalized pullback. The resulting map is an original dense refinement,
not a chosen isomorphism of functor values.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.Compactification

variable {X S X' T : Scheme.{u}} {f : X ⟶ S}
  (C : Compactification f) (f' : X' ⟶ T) (a : X' ⟶ X) (b : T ⟶ S)
  (sq : IsPullback a f' f b) [QuasiCompact f']
  (E : DenseCompactification f') (q : E.Xbar ⟶ C.Xbar)
  (hj : E.j ≫ q = a ≫ C.j) (hp : q ≫ C.p = E.p ≫ b)

/-- The actual lift of the ambient map into the raw proper pullback. -/
def cartesianRefinementRawMap : E.Xbar ⟶ pullback b C.p :=
  pullback.lift E.p q hp.symm

omit [QuasiCompact f'] in
@[reassoc (attr := simp)]
lemma cartesianRefinementRawMap_fst :
    cartesianRefinementRawMap C f' b E q hp ≫ pullback.fst b C.p = E.p :=
  pullback.lift_fst _ _ _

omit [QuasiCompact f'] in
@[reassoc (attr := simp)]
lemma cartesianRefinementRawMap_snd :
    cartesianRefinementRawMap C f' b E q hp ≫ pullback.snd b C.p = q :=
  pullback.lift_snd _ _ _

include hj in
omit [QuasiCompact f'] in
/-- The raw lift retains the exact original open-source map. -/
lemma j_cartesianRefinementRawMap :
    E.j ≫ cartesianRefinementRawMap C f' b E q hp = (cartesianBaseChange C f' a b sq).j := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => E.j ≫ k) (cartesianRefinementRawMap_fst C f' b E q hp)).trans
        (E.fac.trans (cartesianBaseChange C f' a b sq).fac.symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => E.j ≫ k) (cartesianRefinementRawMap_snd C f' b E q hp)).trans
        (hj.trans (cartesianBaseChange_j_snd C f' a b sq).symm))

/-- Closed-target factorization gives an actual proper dense refinement. -/
def normalizedCartesianRefinement : E ⟶ normalizedCartesianBaseChange C f' a b sq :=
  DenseCompactification.closedAmbientRefinement E
    (normalizedCartesianBaseChange C f' a b sq) (pullback.fst b C.p)
    (cartesianRefinementRawMap C f' b E q hp) (cartesianBaseChangeNormalization C f' a b sq)
    ((j_cartesianRefinementRawMap C f' a b sq E q hj hp).trans
      (densify_j_ι (cartesianBaseChange C f' a b sq)).symm)
    (cartesianRefinementRawMap_fst C f' b E q hp)
    (densifyι_p (cartesianBaseChange C f' a b sq))

/-- The dense refinement retains the given raw ambient map after normalization. -/
@[reassoc]
lemma normalizedCartesianRefinement_normalization :
    (normalizedCartesianRefinement C f' a b sq E q hj hp).hom ≫
      cartesianBaseChangeNormalization C f' a b sq =
        cartesianRefinementRawMap C f' b E q hp :=
  DenseCompactification.closedAmbientMap_comp E
    (normalizedCartesianBaseChange C f' a b sq) (cartesianRefinementRawMap C f' b E q hp)
    (cartesianBaseChangeNormalization C f' a b sq)
    ((j_cartesianRefinementRawMap C f' a b sq E q hj hp).trans
      (densify_j_ι (cartesianBaseChange C f' a b sq)).symm)

include hj in
/-- The raw refinement is Cartesian over the unchanged original source. -/
lemma isPullback_cartesianRefinementRawMap_open :
    IsPullback E.j (𝟙 X') (cartesianRefinementRawMap C f' b E q hp)
      (cartesianBaseChange C f' a b sq).j := by
  have h := (DenseCompactification.isPullback_open
    (normalizedCartesianRefinement C f' a b sq E q hj hp)).paste_vert
      (isPullback_densify (cartesianBaseChange C f' a b sq))
  change IsPullback E.j (𝟙 X' ≫ 𝟙 X')
    ((normalizedCartesianRefinement C f' a b sq E q hj hp).hom ≫
      cartesianBaseChangeNormalization C f' a b sq) (cartesianBaseChange C f' a b sq).j at h
  rw [Category.comp_id, normalizedCartesianRefinement_normalization] at h
  exact h

include hj hp sq in
/-- The actual ambient map is Cartesian over the old open source. -/
lemma isPullback_cartesianRefinement_open :
    IsPullback a E.j C.j q := by
  have h := (isPullback_cartesianRefinementRawMap_open C f' a b sq E q hj hp).flip.paste_horiz
    (isPullback_cartesianBaseChange_open C f' a b sq)
  rw [Category.id_comp, cartesianRefinementRawMap_snd] at h
  exact h

end AlgebraicGeometry.Scheme.Hom.Compactification
