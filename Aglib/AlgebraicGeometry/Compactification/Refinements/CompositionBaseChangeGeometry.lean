/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Composition

/-! # Compactifications over a given Cartesian presentation

The raw ambient is the original pullback. Normalization retains its closed
inclusion and its Cartesian open-source square. No density preservation or
quasi-compactness of the new base is asserted or required.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.Compactification

variable {X S X' T : Scheme.{u}} {f : X ⟶ S}
  (C : Compactification f) (f' : X' ⟶ T) (a : X' ⟶ X) (b : T ⟶ S)
  (sq : IsPullback a f' f b)

/-- Raw base change along the actual universal source isomorphism. -/
def cartesianBaseChange : Compactification f' :=
  (C.baseChange b).ofSourceIso f' sq.flip.isoPullback sq.flip.isoPullback_hom_fst

/-- The actual raw open source retains its projection to the old ambient. -/
@[reassoc]
lemma cartesianBaseChange_j_snd :
    (cartesianBaseChange C f' a b sq).j ≫ pullback.snd b C.p = a ≫ C.j := by
  change (sq.flip.isoPullback.hom ≫ (C.baseChange b).j) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => sq.flip.isoPullback.hom ≫ k) (baseChange_j_snd C b)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ C.j) sq.flip.isoPullback_hom_snd)))

/-- The raw presented compactification has the original Cartesian open square. -/
lemma isPullback_cartesianBaseChange_open :
    IsPullback a (cartesianBaseChange C f' a b sq).j C.j (pullback.snd b C.p) := by
  have hout : IsPullback
      ((cartesianBaseChange C f' a b sq).j ≫ pullback.fst b C.p) a b (C.j ≫ C.p) := by
    change IsPullback
      ((cartesianBaseChange C f' a b sq).j ≫ (cartesianBaseChange C f' a b sq).p)
      a b (C.j ≫ C.p)
    rw [Compactification.fac, C.fac]
    exact sq.flip
  exact (hout.of_right (cartesianBaseChange_j_snd C f' a b sq)
    (IsPullback.of_hasPullback b C.p)).flip

variable [QuasiCompact f']

instance cartesianBaseChange_open_quasiCompact :
    QuasiCompact (cartesianBaseChange C f' a b sq).j := by
  have : QuasiCompact
      ((cartesianBaseChange C f' a b sq).j ≫ (cartesianBaseChange C f' a b sq).p) := by
    rw [Compactification.fac]
    infer_instance
  exact QuasiCompact.of_comp _ (cartesianBaseChange C f' a b sq).p

/-- Dense normalization for the given Cartesian presentation. -/
def normalizedCartesianBaseChange : DenseCompactification f' :=
  densify (cartesianBaseChange C f' a b sq)

/-- The retained closed inclusion into the actual raw ambient pullback. -/
def cartesianBaseChangeNormalization :
    (normalizedCartesianBaseChange C f' a b sq).Xbar ⟶ pullback b C.p :=
  densifyι (cartesianBaseChange C f' a b sq)

instance cartesianBaseChangeNormalization_isClosedImmersion :
    IsClosedImmersion (cartesianBaseChangeNormalization C f' a b sq) :=
  inferInstanceAs (IsClosedImmersion (densifyι (cartesianBaseChange C f' a b sq)))

/-- The normalized ambient retains the actual map to the original ambient. -/
def cartesianBaseChangeProjection :
    (normalizedCartesianBaseChange C f' a b sq).Xbar ⟶ C.Xbar :=
  cartesianBaseChangeNormalization C f' a b sq ≫ pullback.snd b C.p

@[reassoc (attr := simp)]
lemma normalizedCartesianBaseChange_j_projection :
    (normalizedCartesianBaseChange C f' a b sq).j ≫
      cartesianBaseChangeProjection C f' a b sq = a ≫ C.j := by
  rw [cartesianBaseChangeProjection, ← Category.assoc]
  exact (congrArg (fun k => k ≫ pullback.snd b C.p)
    (densify_j_ι (cartesianBaseChange C f' a b sq))).trans
      (cartesianBaseChange_j_snd C f' a b sq)

@[reassoc (attr := simp)]
lemma cartesianBaseChangeProjection_p :
    cartesianBaseChangeProjection C f' a b sq ≫ C.p =
      (normalizedCartesianBaseChange C f' a b sq).p ≫ b := by
  change (densifyι (cartesianBaseChange C f' a b sq) ≫ pullback.snd b C.p) ≫ C.p =
    (densifyι (cartesianBaseChange C f' a b sq) ≫ pullback.fst b C.p) ≫ b
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => densifyι (cartesianBaseChange C f' a b sq) ≫ k)
      (pullback.condition (f := b) (g := C.p)).symm).trans
        (Category.assoc _ _ _).symm)

/-- Densification is still Cartesian on the actual original open source. -/
lemma isPullback_normalizedCartesianBaseChange_open :
    IsPullback a (normalizedCartesianBaseChange C f' a b sq).j C.j
      (cartesianBaseChangeProjection C f' a b sq) := by
  have h := (isPullback_densify (cartesianBaseChange C f' a b sq)).flip.paste_horiz
    (isPullback_cartesianBaseChange_open C f' a b sq)
  rw [Category.id_comp] at h
  exact h

end AlgebraicGeometry.Scheme.Hom.Compactification
