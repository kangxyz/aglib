/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedPullbackSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SectionComparison

/-! # The original connected pullback unit for bounded coefficients

The original adjunction unit is tested on every original etale chart. The
base-changed projection retains all four geometric hypotheses, and the
original coefficient pullback retains its specified annihilator. The existing
whole unit square identifies the actual component; no replacement unit or
coefficient model is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/-- A whole comparison square transports componentwise invertibility in
one choice of the original functors. Evaluation, composition and cancellation
are performed here before any native chart is supplied. -/
theorem unitComponent_isIso_of_whole_square
    {C D : Type*} [Category C] [Category D]
    {A B L M R : C ⥤ D} (α : A ⟶ B)
    (l : A ≅ L) (r : B ≅ R) (p : L ⟶ M) (t : M ≅ R)
    (h : α ≫ r.hom = l.hom ≫ (p ≫ t.hom))
    (F : C) [IsIso (p.app F)] : IsIso (α.app F) := by
  have he : α.app F ≫ r.hom.app F =
      l.hom.app F ≫ (p.app F ≫ t.hom.app F) := NatTrans.congr_app h F
  have : IsIso (α.app F ≫ r.hom.app F) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right (α.app F) (r.hom.app F)

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

open Continuity
attribute [local instance] hasSheafifyLarge

/-- Original inverse image retains a specified annihilator. -/
theorem inverseImage_nsmul_id_eq_zero_of_killed
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (n : ℕ) (hF : n • 𝟙 F = 0) : n • 𝟙 ((inverseImage f).obj F) = 0 := by
  have h := congrArg (fun a : F ⟶ F => (inverseImage f).map a) hF
  simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] using h

/-- Original bounded-coefficient section pullback is an isomorphism. -/
theorem globalSectionsPullback_isIso_of_geometricallyConnected
    {X S : Scheme.{u}} (f : S ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [GeometricallyConnected f] [UniversallyOpen f]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsIso (globalSectionsPullback f F) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (globalSectionsPullback_bijective_of_geometricallyConnected f F n hn hF)

/-- The actual unit component on an arbitrary original etale chart. -/
theorem adjunctionUnit_app_isIso_of_geometricallyConnected
    {X S : Scheme.{u}} (f : S ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [GeometricallyConnected f] [UniversallyOpen f]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0)
    (U : X.Etale) :
    IsIso (((inverseImageAdjunction f).unit.app F).hom.app (op U)) := by
  let V := (siteBaseChange f).obj U
  let b := pullback.fst U.hom f
  let G := (inverseImage U.hom).obj F
  have hpb : IsIso (globalSectionsPullback b G) :=
    globalSectionsPullback_isIso_of_geometricallyConnected b G n hn
      (inverseImage_nsmul_id_eq_zero_of_killed U.hom F n hF)
  let p := Functor.whiskerLeft (inverseImage U.hom) (globalSectionsPullbackNatTrans b)
  let : IsIso (p.app F) := hpb
  have hu : IsIso ((unitSectionNatTrans f (𝟙 V)).app F) :=
    unitComponent_isIso_of_whole_square
      (unitSectionNatTrans f (𝟙 V))
      (pullbackSectionsEtaleEvaluationNatIso U).symm
      (Functor.isoWhiskerLeft (inverseImage f)
        (pullbackSectionsEtaleEvaluationNatIso V).symm)
      p
      (Functor.isoWhiskerRight
        (inverseImageSquareIso U.hom V.hom f b pullback.condition.symm).symm
        (globalSections V.left))
      (unitSectionNatTrans_baseChangeChart_square f U) F
  change IsIso (unitSectionMap f F (𝟙 V)) at hu
  rw [unitSectionMap_identity] at hu
  exact hu

/-- The literal inverse-image adjunction unit is invertible for every bounded
original abelian coefficient along a universally open qcqs geometrically
connected morphism. No local constancy or finite stalk condition is used. -/
theorem adjunctionUnit_isIso_of_geometricallyConnected
    {X S : Scheme.{u}} (f : S ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [GeometricallyConnected f] [UniversallyOpen f]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsIso ((inverseImageAdjunction f).unit.app F) := by
  let η := (inverseImageAdjunction f).unit.app F
  let : ∀ U, IsIso (η.hom.app U) := fun U =>
    adjunctionUnit_app_isIso_of_geometricallyConnected f F n hn hF U.unop
  let : IsIso ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map η) :=
    show IsIso η.hom from NatIso.isIso_of_isIso_app η.hom
  exact isIso_of_reflects_iso η (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

end AlgebraicGeometry.Scheme.EtaleCohomology
