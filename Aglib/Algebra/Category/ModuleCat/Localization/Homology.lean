/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Homology of the original exact-functor localization unit

If the components of an original natural transformation from the identity
to an exact module endofunctor are localization maps, then its actual map
on homology is a localization map. Native homology comparisons give the
normalization; neither the unit nor the homology object is replaced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory HomologicalComplex

namespace ModuleCat

universe r m w

variable {R : Type r} [CommRing R] (S : Submonoid R)
  {F : ModuleCat.{m} R ⥤ ModuleCat.{m} R} [F.Additive] [F.PreservesHomology]
  (τ : 𝟭 (ModuleCat.{m} R) ⟶ F)
  (hτ : ∀ M, IsLocalizedModule S (τ.app M).hom)

include hτ in
/-- The native homology map of an original localization natural transformation is localizing. -/
theorem isLocalizedModule_shortComplex_homologyMap (C : ShortComplex (ModuleCat.{m} R)) :
    IsLocalizedModule S (ShortComplex.homologyMap (C.mapNatTrans τ)).hom := by
  have h := hτ C.homology
  have he := τ.app_homology C
  rw [he] at h
  change IsLocalizedModule S
    ((C.mapHomologyIso F).hom.hom.comp
      ((ShortComplex.homologyMap (C.mapNatTrans τ)).hom.comp
        (C.mapHomologyIso (𝟭 (ModuleCat.{m} R))).inv.hom)) at h
  have h' := (IsLocalizedModule.comp_iff_of_bijective_left S
    (C.mapHomologyIso F).hom.hom
    (ConcreteCategory.bijective_of_isIso (C.mapHomologyIso F).hom)).mp h
  exact (IsLocalizedModule.comp_iff_of_bijective_right S
    (C.mapHomologyIso (𝟭 (ModuleCat.{m} R))).inv.hom
    (ConcreteCategory.bijective_of_isIso (C.mapHomologyIso (𝟭 (ModuleCat.{m} R))).inv)).mp h'

variable {ι : Type w} (d : ComplexShape ι)

/-- The actual unit on complexes, with only the native identity-complex comparison. -/
def localizationComplexUnit (C : HomologicalComplex (ModuleCat.{m} R) d) :
    C ⟶ (F.mapHomologicalComplex d).obj C :=
  (Functor.mapHomologicalComplexIdIso (ModuleCat.{m} R) d).inv.app C ≫
    (NatTrans.mapHomologicalComplex τ d).app C

omit [F.PreservesHomology] in
theorem localizationComplexUnit_f (C : HomologicalComplex (ModuleCat.{m} R) d) (i : ι) :
    (localizationComplexUnit τ d C).f i = τ.app (C.X i) := rfl

include hτ in
/-- The actual unit complex map localizes native homology in every shape and degree. -/
theorem isLocalizedModule_homologyMap_localizationComplexUnit
    (C : HomologicalComplex (ModuleCat.{m} R) d) (i : ι) :
    IsLocalizedModule S (homologyMap (localizationComplexUnit τ d C) i).hom := by
  change IsLocalizedModule S (ShortComplex.homologyMap ((C.sc i).mapNatTrans τ)).hom
  exact isLocalizedModule_shortComplex_homologyMap S τ hτ (C.sc i)

end ModuleCat
