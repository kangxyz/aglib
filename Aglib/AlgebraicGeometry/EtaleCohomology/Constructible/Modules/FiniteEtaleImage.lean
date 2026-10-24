/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtaleProduct
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructibleSums
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.DescentEtaleConstructible

/-! # Finite-etale direct images of native constructible module coefficients

Actual finite-etale covers split on a jointly surjective family indexed by the
base points. On each chart the original module direct image is the finite
product of the original component restrictions. This proves finite-type local
constancy first, then constructibility by unrestricted etale descent. The
coefficient ring is arbitrary and retains its independent universe; no finite
underlying-group, Noetherian, quasi-compact, or constant-rank hypothesis is used.
No assertion for a ramified finite morphism is made here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.EtaleCohomology.Fields.FiniteDirectImage

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

local instance finiteEtaleImageHasModuleLimits :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, r}

/-- On an actual splitting chart, the original finite direct image of a
finite-type local system is finite-type locally constant. -/
theorem isFiniteTypeLocallyConstant_directImage_on_split
    {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) {V : X.Etale} {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y)
    {F : ModuleSheaf R Y.obj.left} (hF : IsFiniteTypeLocallyConstant F) :
    IsFiniteTypeLocallyConstant
      ((moduleInverseImage R V.hom).obj ((moduleDirectImage R Y.obj.hom).obj F)) := by
  apply (isFiniteTypeLocallyConstant_iff_of_iso
    ((moduleInverseImageEtaleIso R V.hom).app ((moduleDirectImage R Y.obj.hom).obj F) ≪≫
      moduleLocalProductObjIso R Y e F)).mpr
  apply isFiniteTypeLocallyConstant_product
  intro a
  exact (isFiniteTypeLocallyConstant_iff_of_iso
    ((moduleInverseImageEtaleIso R (splitComponent Y e a)).app F)).mp
      (isFiniteTypeLocallyConstant_pullback (splitComponent Y e a) hF)

/-- Actual finite-etale direct image preserves finite-type local constancy,
including empty fibres and rank varying over the original arbitrary base. -/
theorem isFiniteTypeLocallyConstant_finiteEtaleDirectImage
    {X S : Scheme.{u}} (f : S ⟶ X) [IsFinite f] [Etale f]
    {F : ModuleSheaf R S} (hF : IsFiniteTypeLocallyConstant F) :
    IsFiniteTypeLocallyConstant ((moduleDirectImage R f).obj F) := by
  let Y : Scheme.FiniteEtale X := Scheme.FiniteEtale.mk f
  choose V A e v hv using exists_labelled_chart Y
  apply isFiniteTypeLocallyConstant_of_etaleCover V
    (fun x => ⟨x, v x, hv x⟩) ((moduleDirectImage R f).obj F)
  intro x
  exact isFiniteTypeLocallyConstant_directImage_on_split Y (e x) hF

/-- On a labelled splitting chart, actual module constructibility follows
from finite-product closure on the original component pullbacks. -/
theorem isConstructible_directImage_on_split
    {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) {V : X.Etale} {A : FintypeCat.{u}}
    (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y)
    {F : ModuleSheaf R Y.obj.left} (hF : IsConstructible F) :
    IsConstructible
      ((moduleInverseImage R V.hom).obj ((moduleDirectImage R Y.obj.hom).obj F)) := by
  apply (isConstructible_iff_of_iso
    ((moduleInverseImageEtaleIso R V.hom).app ((moduleDirectImage R Y.obj.hom).obj F) ≪≫
      moduleLocalProductObjIso R Y e F)).mpr
  apply isConstructible_product
  intro a
  exact (isConstructible_iff_of_iso
    ((moduleInverseImageEtaleIso R (splitComponent Y e a)).app F)).mp
      (isConstructible_pullback (splitComponent Y e a) hF)

/-- The original finite-etale direct image preserves constructibility for
arbitrary commutative coefficients on arbitrary schemes. -/
theorem isConstructible_finiteEtaleDirectImage
    {X S : Scheme.{u}} (f : S ⟶ X) [IsFinite f] [Etale f]
    {F : ModuleSheaf R S} (hF : IsConstructible F) :
    IsConstructible ((moduleDirectImage R f).obj F) := by
  let Y : Scheme.FiniteEtale X := Scheme.FiniteEtale.mk f
  choose V A e v hv using exists_labelled_chart Y
  apply isConstructible_of_etaleCover V (fun x => ⟨x, v x, hv x⟩)
  intro x
  exact isConstructible_directImage_on_split Y (e x) hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
