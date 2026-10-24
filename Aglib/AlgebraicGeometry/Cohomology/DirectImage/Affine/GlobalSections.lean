/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Single
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.GlobalSectionsComposition.SingleUnit
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived

/-!
# Original global sections after an affine direct image

For an affine morphism and a quasicoherent coefficient, the installed
derived global sections of its ordinary direct image are the installed
derived global sections of the original coefficient. The forward map is
the image of the original direct-image single unit followed by the
inverse of the native composition comparison. The original section map,
units and coefficient arrows are retained.

Taking homology gives a linear equivalence between the original additive
sheaf cohomology groups for the specified structural ring map and its
actual composite with the morphism. The target need not be affine.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived category of the original module sheaves. -/
local instance affineGlobalSectionsSource (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

/-- The standard derived category of modules over the structural ring. -/
local instance affineGlobalSectionsTarget (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  (f : X ⟶ Y) [IsAffineHom f] (α : R →+* Γ(Y, ⊤))

private theorem inverse_of_unit_square
    {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (a : D ≅ B) (η : A ⟶ D)
    (h : η ≫ a.hom = e.hom) : a.inv = e.inv ≫ η := by
  apply (cancel_mono a.hom).mp
  rw [Category.assoc, h, e.inv_hom_id, a.inv_hom_id]

private theorem inverse_naturality
    {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ e'.hom = e.hom ≫ b) : b ≫ e'.inv = e.inv ≫ a := by
  apply (cancel_mono e'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, e.inv_hom_id_assoc]

private theorem compose_squares
    {C : Type*} [Category C] {A B D E F G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E}
    {d : A ⟶ F} {e : F ⟶ D} {k : F ⟶ G} {q : G ⟶ E}
    (h : a ≫ b = d ≫ e) (h' : e ≫ c = k ≫ q) :
    a ≫ (b ≫ c) = (d ≫ k) ≫ q := by
  rw [← Category.assoc, h, Category.assoc, h', Category.assoc]

private theorem affineSingle_inv_eq_unit (M : X.Modules) [M.IsQuasicoherent] :
    (affineDerivedPushforwardSingleIso f M).inv =
      (pushforward f).rightDerivedSingleUnit M := by
  let P := pushforward f
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let e := (exactSingleComplexNatIso P).app M
  let a : P.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) ≅
      DerivedCategory.Plus.Q.obj
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj (P.obj M)) :=
    affineDerivedPushforwardSingleIso f M
  have hu : P.rightDerivedFunctorPlusUnit.app K ≫ a.hom =
      DerivedCategory.Plus.Q.map e.hom :=
    affineDerivedPushforwardSingleIso_unit f M
  exact inverse_of_unit_square (DerivedCategory.Plus.Q.mapIso e) a
    (P.rightDerivedFunctorPlusUnit.app K) hu

/-- Derived global sections of the original ordinary affine direct image
are the actual source derived global sections for the induced scalars. -/
def moduleDerivedGlobalSectionsAffineSingleIso (M : X.Modules) [M.IsQuasicoherent] :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((pushforward f).obj M)) ≅
      (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) :=
  (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.mapIso
      (affineDerivedPushforwardSingleIso f M).symm ≪≫
    ((moduleDerivedGlobalSectionsPushforwardCompIso f α).app
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)).symm

/-- The forward arrow uses the original affine single unit and the inverse
of the same original global-sections composition comparison. -/
theorem moduleDerivedGlobalSectionsAffineSingleIso_hom
    (M : X.Modules) [M.IsQuasicoherent] :
    (moduleDerivedGlobalSectionsAffineSingleIso f α M).hom =
      (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
          ((pushforward f).rightDerivedSingleUnit M) ≫
        (moduleDerivedGlobalSectionsPushforwardCompIso f α).inv.app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) := by
  change (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
      (affineDerivedPushforwardSingleIso f M).inv ≫ _ = _
  exact congrArg
    (fun q => (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map q ≫
      (moduleDerivedGlobalSectionsPushforwardCompIso f α).inv.app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))
    (affineSingle_inv_eq_unit f M)

/-- The original section isomorphism and both single units normalize this
affine comparison. -/
theorem moduleDerivedGlobalSectionsAffineSingleIso_singleUnit
    (M : X.Modules) [M.IsQuasicoherent] :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedSingleUnit ((pushforward f).obj M) ≫
        (moduleDerivedGlobalSectionsAffineSingleIso f α M).hom =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
          ((modulePushforwardGlobalSectionsIso f α).hom.app M) ≫
        (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedSingleUnit M := by
  rw [moduleDerivedGlobalSectionsAffineSingleIso_hom, ← Category.assoc,
    moduleDerivedGlobalSectionsPushforwardCompIso_singleUnit]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Every original coefficient arrow into the ordinary direct image has
its original section map under the affine comparison. -/
theorem moduleDerivedGlobalSectionsAffineSingleIso_coefficientUnit
    {M : Y.Modules} {N : X.Modules} [N.IsQuasicoherent]
    (φ : M ⟶ (pushforward f).obj N) :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedSingleUnit M ≫
        (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map φ) ≫
        (moduleDerivedGlobalSectionsAffineSingleIso f α N).hom =
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map
          ((moduleGlobalSectionsFunctorOfHom Y α).map φ ≫
            (modulePushforwardGlobalSectionsIso f α).hom.app N) ≫
        (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedSingleUnit N := by
  simpa only [moduleDerivedGlobalSectionsAffineSingleIso_hom, Functor.map_comp,
    Category.assoc] using
    moduleDerivedGlobalSectionsPushforwardCompIso_coefficientUnit f α φ

/-- The comparison preserves each original quasicoherent coefficient morphism. -/
theorem moduleDerivedGlobalSectionsAffineSingleIso_naturality
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (g : M ⟶ N) :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map ((pushforward f).map g)) ≫
        (moduleDerivedGlobalSectionsAffineSingleIso f α N).hom =
      (moduleDerivedGlobalSectionsAffineSingleIso f α M).hom ≫
        (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map g) := by
  let F := (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus
  let SX := DerivedCategory.Plus.singleFunctor X.Modules 0
  let SY := DerivedCategory.Plus.singleFunctor Y.Modules 0
  let P := (pushforward f).rightDerivedFunctorPlus
  let eM : P.obj (SX.obj M) ≅ SY.obj ((pushforward f).obj M) :=
    affineDerivedPushforwardSingleIso f M
  let eN : P.obj (SX.obj N) ≅ SY.obj ((pushforward f).obj N) :=
    affineDerivedPushforwardSingleIso f N
  have ha : P.map (SX.map g) ≫ eN.hom = eM.hom ≫ SY.map ((pushforward f).map g) :=
    affineDerivedPushforwardSingleIso_hom_naturality f M g
  have hi : SY.map ((pushforward f).map g) ≫ eN.inv = eM.inv ≫ P.map (SX.map g) :=
    inverse_naturality eM eN _ _ ha
  have hF : F.map (SY.map ((pushforward f).map g)) ≫ F.map eN.inv =
      F.map eM.inv ≫ F.map (P.map (SX.map g)) :=
    (F.map_comp _ _).symm.trans ((congrArg F.map hi).trans (F.map_comp _ _))
  have hC : F.map (P.map (SX.map g)) ≫
      (moduleDerivedGlobalSectionsPushforwardCompIso f α).inv.app (SX.obj N) =
      (moduleDerivedGlobalSectionsPushforwardCompIso f α).inv.app (SX.obj M) ≫
        (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlus.map
          (SX.map g) :=
    (moduleDerivedGlobalSectionsPushforwardCompIso f α).inv.naturality (SX.map g)
  change F.map (SY.map ((pushforward f).map g)) ≫ (F.map eN.inv ≫ _) =
    (F.map eM.inv ≫ _) ≫ _
  exact compose_squares hF hC

/-- Original additive sheaf cohomology is unchanged by ordinary affine
direct image of a quasicoherent coefficient, linearly for the original
structural action and its actual composite. -/
def moduleAffinePushforwardCohomologyLinearEquiv
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    letI := moduleCohomologyModuleOfHom Y α ((pushforward f).obj M) n
    letI := moduleCohomologyModuleOfHom X (f.appTop.hom.comp α) M n
    Sheaf.H.{u + 1} (moduleAddSheaf Y ((pushforward f).obj M)) n ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  letI := moduleCohomologyModuleOfHom Y α ((pushforward f).obj M) n
  letI := moduleCohomologyModuleOfHom X (f.appTop.hom.comp α) M n
  exact
    (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv Y α
      (injectiveResolution ((pushforward f).obj M)) n).symm.trans
      (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).mapIso
        (moduleDerivedGlobalSectionsAffineSingleIso f α M)).toLinearEquiv.trans
          (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X (f.appTop.hom.comp α)
            (injectiveResolution M) n))

end AlgebraicGeometry.Scheme.Cohomology
