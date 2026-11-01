/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.FiniteBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.CoverConservativity

/-! # Original finite image on and off a closed source

Finite base change computes the original module direct image on the closed
source and makes it zero on any disjoint inverse image. Coefficient universes
are independent, and neither finite presentation nor Noetherianity is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Every actual module sheaf on the empty scheme is zero, by the empty
jointly surjective etale family. -/
theorem finiteImage_isZero_of_empty {X : Scheme.{u}} [IsEmpty X]
    (F : ModuleSheaf R X) : IsZero F := by
  have : IsIso (0 : F ⟶ F) := isIso_of_module_etale_inverseImages R
    (fun i : PEmpty.{u + 1} => nomatch i)
    (fun x => isEmptyElim x) (0 : F ⟶ F) (fun i => nomatch i)
  exact (isIsoZero_iff_source_target_isZero F F).mp inferInstance |>.1

/-- The native direct image of a coefficient on the empty scheme is zero. -/
theorem finiteImage_isZero_directImage_of_empty {X S : Scheme.{u}} [IsEmpty X]
    (f : X ⟶ S) (F : ModuleSheaf R X) :
    IsZero ((moduleDirectImage R f).obj F) := by
  have hzero : @Functor.PreservesZeroMorphisms
      (ModuleSheaf R X) inferInstance (ModuleSheaf R S) inferInstance
      inferInstance inferInstance (moduleDirectImage R f) :=
    @Functor.preservesZeroMorphisms_of_isRightAdjoint
      (ModuleSheaf R X) inferInstance (ModuleSheaf R S) inferInstance
      inferInstance inferInstance (moduleDirectImage R f)
      (moduleImageAdjunction R f).isRightAdjoint
  exact @Functor.map_isZero
    (ModuleSheaf R X) inferInstance (ModuleSheaf R S) inferInstance
    inferInstance inferInstance (moduleDirectImage R f) hzero F
    (finiteImage_isZero_of_empty R F)

/-- The original finite module base-change isomorphism, kept as a whole
natural transformation before evaluating at coefficients. -/
def finiteImageBaseChangeIso {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [IsFinite f] (h : IsPullback g' f' f g) :
    moduleDirectImage R f ⋙ moduleInverseImage R g ≅
      moduleInverseImage R g' ⋙ moduleDirectImage R f' := by
  let a := moduleBaseChangeMap R f f' g g' h.w.symm
  have : IsIso a := Finite.finiteModuleBaseChange_isIso R f f' g g' h
  exact asIso a

/-- On any base change disjoint from the original finite source, the actual
inverse image of the actual direct image is zero. -/
theorem finiteImage_isZero_pullback_of_disjoint {X S T : Scheme.{u}}
    (f : X ⟶ S) [IsFinite f] (g : T ⟶ S)
    (h : Disjoint (Set.range f) (Set.range g)) (F : ModuleSheaf R X) :
    IsZero ((moduleInverseImage R g).obj ((moduleDirectImage R f).obj F)) := by
  have : IsEmpty (pullback f g : Scheme.{u}) := Scheme.isEmpty_pullback_iff.mpr h
  let e := finiteImageBaseChangeIso R f (pullback.snd f g) g (pullback.fst f g)
    (IsPullback.of_hasPullback f g)
  exact (finiteImage_isZero_directImage_of_empty R (pullback.snd f g)
    ((moduleInverseImage R (pullback.fst f g)).obj F)).of_iso (e.app F)

/-- On its original closed source, finite base change computes the original
module direct image as the original coefficient. -/
def finiteImageClosedRestrictionIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : ModuleSheaf R Z) :
    (moduleInverseImage R i).obj ((moduleDirectImage R i).obj F) ≅ F := by
  have h : IsPullback (𝟙 Z) (𝟙 Z) i i :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  let a := (moduleBaseChangeMap R i (𝟙 Z) i (𝟙 Z) h.w.symm).app F
  have : IsIso a := Finite.finiteModuleBaseChange_app_isIso R i (𝟙 Z) i (𝟙 Z) h F
  let e : moduleDirectImage R (𝟙 Z) ≅ 𝟭 (ModuleSheaf R Z) :=
    Functor.sheafPushforwardContinuousId' (siteBaseChangeId Z)
      (ModuleCat.{u + 1} R) Z.smallEtaleTopology
  let eId : moduleInverseImage R (𝟙 Z) ≅ 𝟭 (ModuleSheaf R Z) :=
    ((moduleImageAdjunction R (𝟙 Z)).ofNatIsoRight e).leftAdjointUniq Adjunction.id
  exact asIso a ≪≫ e.app _ ≪≫ eId.app F

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
