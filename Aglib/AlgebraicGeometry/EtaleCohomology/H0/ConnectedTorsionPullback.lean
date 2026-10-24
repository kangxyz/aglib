/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedTorsionSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback

/-! # Original pullback of connected constant torsion sections

The original constant-adjunction units and their actual pullback comparison
show that restriction between connected qcqs schemes is an isomorphism for
any torsion constant value, including infinite groups. The result transports
along an actual coefficient isomorphism. It concerns sections, not injectivity
of a higher-cohomology edge map or a proper-base-change theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X T : Scheme.{u}}
  [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
  [ConnectedSpace T] [CompactSpace T] [QuasiSeparatedSpace T]
  (f : T ⟶ X) (A : AddCommGrpCat.{u + 1}) (hA : IsAddTorsion A)

include hA

/-- The literal original section pullback is invertible for a torsion constant
coefficient on connected qcqs source and target. -/
theorem globalSectionsPullback_constant_isIso_of_isAddTorsion :
    IsIso (globalSectionsPullback f
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) := by
  let C := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  let : IsIso ((constantAdjunction X).unit.app A) :=
    constantUnit_isIso_of_isAddTorsion X A hA
  let : IsIso ((constantAdjunction T).unit.app A) :=
    constantUnit_isIso_of_isAddTorsion T A hA
  have h := constantTransport_homEquiv f A (𝟙 C)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at h
  rw [(inverseImage f).map_id C, (globalSections X).map_id C] at h
  let ex := asIso ((constantAdjunction X).unit.app A) ≪≫
    Iso.refl ((globalSections X).obj C)
  let et := asIso ((constantAdjunction T).unit.app A) ≪≫
    (globalSections T).mapIso (((inverseImageConstantIso f).app A).symm ≪≫
      Iso.refl ((inverseImage f).obj C))
  let : IsIso ((constantAdjunction X).unit.app A ≫
      𝟙 ((globalSections X).obj C)) := ex.isIso_hom
  have hi : IsIso (((constantAdjunction X).unit.app A ≫
      𝟙 ((globalSections X).obj C)) ≫ globalSectionsPullback f C) := by
    rw [← h]
    exact et.isIso_hom
  exact (isIso_comp_left_iff ((constantAdjunction X).unit.app A ≫
    𝟙 ((globalSections X).obj C)) _).mp hi

/-- The actual coefficient comparison transports the original pullback result;
no arbitrary replacement of the section map is used. -/
theorem globalSectionsPullback_isIso_of_torsionConstantIso
    (F : AbelianSheaf.{u, u + 1} X)
    (e : F ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) :
    IsIso (globalSectionsPullback f F) := by
  have h := globalSectionsPullback_constant_isIso_of_isAddTorsion f A hA
  exact (NatTrans.isIso_app_iff_of_iso (globalSectionsPullbackNatTrans f) e).mpr h

/-- Vanishing of the original restricted section detects the original section.
In a proper-family application the coefficient isomorphism is still supplied
by the actual proper-base-change theorem, not by this lemma. -/
theorem globalSectionsPullback_eq_zero_iff_of_torsionConstantIso
    (F : AbelianSheaf.{u, u + 1} X)
    (e : F ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    (x : (globalSections X).obj F) : globalSectionsPullback f F x = 0 ↔ x = 0 := by
  let := globalSectionsPullback_isIso_of_torsionConstantIso f A hA F e
  constructor
  · intro hx
    apply (ConcreteCategory.bijective_of_isIso (globalSectionsPullback f F)).injective
    exact hx.trans (map_zero (globalSectionsPullback f F).hom).symm
  · rintro rfl
    exact map_zero (globalSectionsPullback f F).hom

end AlgebraicGeometry.Scheme.EtaleCohomology
