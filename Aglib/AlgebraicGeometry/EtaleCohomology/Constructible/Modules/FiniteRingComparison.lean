/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ScalarExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ZModComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ScalarRestrictionExact
public import Aglib.CategoryTheory.Adjunction.BarCokernel

/-! # Constructibility of original modules over a finite coefficient ring

The reverse implication uses the actual counit bar cokernel. Its two terms
are induced from the actual ZMod restriction, and the terminal object retains
its original coefficient action. Full scalar forgetting is never assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Actual restriction to the canonical characteristic coefficient ring. -/
abbrev characteristicRestriction (X : Scheme.{u}) :
    ModuleSheaf Λ X ⥤ ModuleSheaf (ZMod (ringChar Λ)) X :=
  ModuleCat.Sheaf.valuedScalarRestriction X.smallEtaleTopology
    (ZMod.castHom (dvd_refl (ringChar Λ)) Λ)

/-- Restriction keeps the same underlying abelian sheaf. -/
def characteristicRestrictionUnderlyingIso (X : Scheme.{u}) :
    characteristicRestriction (Λ := Λ) X ⋙ moduleUnderlying (ZMod (ringChar Λ)) X ≅
      moduleUnderlying Λ X := Iso.refl _

/-- This is the already established forward implication, applied after restriction. -/
theorem isConstructible_characteristicRestriction {X : Scheme.{u}}
    {F : ModuleSheaf Λ X} (hF : IsConstructible F) :
    IsConstructible ((characteristicRestriction X).obj F) := by
  apply isConstructible_of_zmodUnderlying
  exact (Constructible.isConstructible_iff_of_iso
    ((characteristicRestrictionUnderlyingIso X).app F)).mpr
      (isConstructible_underlying hF)

/-- Finite underlying constructibility recovers the original finite-ring action
by the actual bar cokernel, not by falsely making every additive map linear. -/
theorem isConstructible_of_finiteRingUnderlying {X : Scheme.{u}}
    {F : ModuleSheaf Λ X}
    (hF : Constructible.IsConstructible ((moduleUnderlying Λ X).obj F)) :
    IsConstructible F := by
  let n := ringChar Λ
  let φ : ZMod n →+* Λ := ZMod.castHom (dvd_refl n) Λ
  let L := scalarExtensionSheaf φ X
  let U := ModuleCat.Sheaf.valuedScalarRestriction X.smallEtaleTopology φ
  let adj : L ⊣ U := Sheaf.adjunction X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} φ)
  let : IsNoetherianRing Λ := inferInstance
  have hUF : IsConstructible (U.obj F) := by
    apply isConstructible_of_zmodUnderlying
    exact (Constructible.isConstructible_iff_of_iso
      ((characteristicRestrictionUnderlyingIso X).app F)).mpr hF
  exact adj.property_of_restricted
    (IsConstructible (R := Λ) (X := X))
    (IsConstructible (R := ZMod n) (X := X))
    (fun N hN => isConstructible_scalarExtension φ hN)
    (fun N hN => isConstructible_characteristicRestriction hN) F hUF

/-- Over a finite coefficient ring, the two intrinsic predicates agree on the
same original module-valued sheaf and its original underlying abelian sheaf. -/
theorem isConstructible_finiteRing_iff {X : Scheme.{u}} (F : ModuleSheaf Λ X) :
    IsConstructible F ↔
      Constructible.IsConstructible ((moduleUnderlying Λ X).obj F) :=
  ⟨isConstructible_underlying, isConstructible_of_finiteRingUnderlying⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
