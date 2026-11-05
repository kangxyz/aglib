/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.NormalMarkedCoverTransport
public import Aglib.CategoryTheory.Over.PullbackMaps

/-! # Original coefficient families over a commuting normal-model square

The base square is only commuting. Pullback pasting nevertheless identifies
the original coefficient-refined family with the family over the normal
source. The original projection, normal-family map and their further cover
pullbacks are retained literally. No Cartesian assertion is made about the
normal-model base square itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

variable {X A R B S : Scheme.{u}} (p : X ⟶ A) (r : R ⟶ A) (b : B ⟶ A)
  (t : S ⟶ B) (β : S ⟶ R) (h : β ≫ r = t ≫ b)

/-- The same original double family, in coefficient-first order, is the
literal base change of the original family over the normal source. -/
def normalCoefficientFamilyIso :
    pullback t (pullback.snd p b) ≅ pullback (pullback.snd p r) β :=
  pullbackSymmetry t (pullback.snd p b) ≪≫
    normalGenericFibreIso p r b β t h.symm

/-- The coefficient-refined original family maps to the whole normal-source
family by the unchanged original two-fibre comparison. -/
def normalCoefficientFamilyMap :
    pullback t (pullback.snd p b) ⟶ pullback p r :=
  (normalCoefficientFamilyIso p r b t β h).hom ≫ pullback.fst (pullback.snd p r) β

@[reassoc]
theorem normalCoefficientFamilyIso_coefficient :
    (normalCoefficientFamilyIso p r b t β h).hom ≫ pullback.snd (pullback.snd p r) β =
      pullback.fst t (pullback.snd p b) := by
  simp only [normalCoefficientFamilyIso, Iso.trans_hom, Category.assoc,
    normalGenericFibreIso_field, pullbackSymmetry_hom_comp_snd]

@[reassoc]
theorem normalCoefficientFamilyMap_source :
    normalCoefficientFamilyMap p r b t β h ≫ pullback.fst p r =
      pullback.snd t (pullback.snd p b) ≫ pullback.fst p b := by
  simp only [normalCoefficientFamilyMap, normalCoefficientFamilyIso, Iso.trans_hom,
    Category.assoc, normalGenericFibreIso_source, pullbackSymmetry_hom_comp_fst_assoc]

/-- This is the actual Cartesian family square, not the possibly
non-Cartesian square of source and coefficient normalizations. -/
theorem normalCoefficientFamilyMap_isPullback :
    IsPullback (normalCoefficientFamilyMap p r b t β h)
      (pullback.fst t (pullback.snd p b)) (pullback.snd p r) β :=
  pullback.isPullback_of_projection_iso (pullback.snd p r) β
    (normalCoefficientFamilyIso p r b t β h)
    (normalCoefficientFamilyMap p r b t β h) (pullback.fst t (pullback.snd p b))
    rfl (normalCoefficientFamilyIso_coefficient p r b t β h)

/-- Under the same canonical family isomorphism, the original normal-family
map is precisely the original coefficient-refinement projection. -/
@[reassoc]
theorem normalCoefficientFamilyIso_original :
    (normalCoefficientFamilyIso p r b t β h).hom ≫ normalizedFamilyMap p r b t β h =
      pullback.snd t (pullback.snd p b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, normalizedFamilyMap_source]
    simpa only [normalCoefficientFamilyMap, Category.assoc] using
      normalCoefficientFamilyMap_source p r b t β h
  · rw [Category.assoc, normalizedFamilyMap_coefficient, ← Category.assoc,
      normalCoefficientFamilyIso_coefficient]
    exact pullback.condition (f := t) (g := pullback.snd p b)

variable {G H : Scheme.{u}} (k : G ⟶ pullback p r) (w : H ⟶ G)

/-- A restriction of the whole source cover maps to its original normal
coefficient pullback. This is the map used to retain the original open zero. -/
def normalCoefficientCoverMap :
    pullback (w ≫ k) (normalCoefficientFamilyMap p r b t β h) ⟶
      pullback k (pullback.fst (pullback.snd p r) β) :=
  pullback.lift
    (pullback.fst (w ≫ k) (normalCoefficientFamilyMap p r b t β h) ≫ w)
    (pullback.snd (w ≫ k) (normalCoefficientFamilyMap p r b t β h) ≫
      (normalCoefficientFamilyIso p r b t β h).hom)
    (by
      rw [Category.assoc, Category.assoc]
      exact pullback.condition (f := w ≫ k)
        (g := normalCoefficientFamilyMap p r b t β h))

@[reassoc]
theorem normalCoefficientCoverMap_family :
    normalCoefficientCoverMap p r b t β h k w ≫
      pullback.snd k (pullback.fst (pullback.snd p r) β) =
      pullback.snd (w ≫ k) (normalCoefficientFamilyMap p r b t β h) ≫
        (normalCoefficientFamilyIso p r b t β h).hom :=
  pullback.lift_snd ..

@[reassoc]
theorem normalCoefficientCoverMap_coefficient :
    normalCoefficientCoverMap p r b t β h k w ≫
      pullback.snd k (pullback.fst (pullback.snd p r) β) ≫
        pullback.snd (pullback.snd p r) β =
      pullback.snd (w ≫ k) (normalCoefficientFamilyMap p r b t β h) ≫
        pullback.fst t (pullback.snd p b) := by
  rw [← Category.assoc, normalCoefficientCoverMap_family, Category.assoc,
    normalCoefficientFamilyIso_coefficient]

/-- The original class is pulled back along the same composite map to the
original coefficient family, even after selecting the section component. -/
@[reassoc]
theorem normalCoefficientCoverMap_original :
    normalCoefficientCoverMap p r b t β h k w ≫
      pullback.snd k (pullback.fst (pullback.snd p r) β) ≫
        normalizedFamilyMap p r b t β h =
      pullback.snd (w ≫ k) (normalCoefficientFamilyMap p r b t β h) ≫
        pullback.snd t (pullback.snd p b) := by
  rw [← Category.assoc, normalCoefficientCoverMap_family, Category.assoc,
    normalCoefficientFamilyIso_original]

/-- The restricted whole source cover still has its actual Cartesian
coefficient family, with the original source morphism as the horizontal leg. -/
theorem normalCoefficientCoverMap_isPullback :
    IsPullback
      (pullback.fst (w ≫ k) (normalCoefficientFamilyMap p r b t β h))
      (pullback.snd (w ≫ k) (normalCoefficientFamilyMap p r b t β h) ≫
        pullback.fst t (pullback.snd p b))
      ((w ≫ k) ≫ pullback.snd p r) β :=
  (IsPullback.of_hasPullback (w ≫ k)
    (normalCoefficientFamilyMap p r b t β h)).paste_vert
      (normalCoefficientFamilyMap_isPullback p r b t β h)

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
