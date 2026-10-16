/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Perfect objects in the native derived category

An intrinsic perfect derived object is locally the native derived image
of an actual strict perfect complex. This property is equivalent to an
actual locally perfect chain representative and defines a full triangulated
derived subcategory. The native chain category Complex.Perfect remains
distinct; the comparison functor uses the original Q and restriction factors.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPerfect.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `8afd6b0d5fe44cd9f4258cc6f405af23095640878becb170a8e44c2f7b327ebc`.
Selected declaration ranges: 52–54, 56–59, 63–71, 75–87, 89–92, 94–101, 103–118, 120–121,
  123–123, 126–126, 129–131, 134–137, 140–146, 149–152, 156–158, 162–167.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme.Modules.Complex
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

/-- Intrinsic local perfectness of an object of the original ambient derived category. -/
def perfectDerivedObjects (X : Scheme.{u}) : ObjectProperty (DerivedCategory X.Modules) := fun K =>
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : StrictPerfect U.toScheme,
    Nonempty ((derivedRestrict U.ι).obj K ≅ (DerivedCategory.Q (C := U.toScheme.Modules)).obj P.obj)

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsClosedUnderIsomorphisms where
  of_iso e h x := by
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := h x
    exact ⟨U, hx, P, ⟨(derivedRestrict U.ι).mapIso e.symm ≪≫ eP⟩⟩

lemma perfectDerivedObjects_toDerived_iff (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    perfectDerivedObjects X ((DerivedCategory.Q (C := X.Modules)).obj K) ↔ locallyPerfect X K := by
  constructor
  · intro h x
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := h x
    exact ⟨U, hx, P, ⟨((derivedRestrictFactors U.ι).app K).symm ≪≫ eP⟩⟩
  · intro h x
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := h x
    exact ⟨U, hx, P, ⟨(derivedRestrictFactors U.ι).app K ≪≫ eP⟩⟩

lemma perfectDerivedObjects_iff_exists_representative (X : Scheme.{u})
    (K : DerivedCategory X.Modules) :
    perfectDerivedObjects X K ↔
      ∃ P : Perfect X, Nonempty ((DerivedCategory.Q (C := X.Modules)).obj P.obj ≅ K) := by
  constructor
  · intro h
    let P := (DerivedCategory.Q (C := X.Modules)).objPreimage K
    let e := (DerivedCategory.Q (C := X.Modules)).objObjPreimageIso K
    have hP := (perfectDerivedObjects X).prop_of_iso e.symm h
    exact ⟨⟨P, (perfectDerivedObjects_toDerived_iff X P).mp hP⟩, ⟨e⟩⟩
  · rintro ⟨P, ⟨e⟩⟩
    exact (perfectDerivedObjects X).prop_of_iso e
      ((perfectDerivedObjects_toDerived_iff X P.obj).mpr P.property)

instance (X : Scheme.{u}) : (perfectDerivedObjects X).ContainsZero where
  exists_zero := ⟨(DerivedCategory.Q (C := X.Modules)).obj 0,
    (DerivedCategory.Q (C := X.Modules)).map_isZero (isZero_zero _),
    (perfectDerivedObjects_toDerived_iff X 0).mpr ((locallyPerfect X).prop_zero)⟩

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro K hK
    obtain ⟨P, ⟨eP⟩⟩ := (perfectDerivedObjects_iff_exists_representative X K).mp hK
    apply (perfectDerivedObjects_iff_exists_representative X _).mpr
    exact ⟨⟨P.obj⟦n⟧, locallyPerfect_shift P.property n⟩,
      ⟨((DerivedCategory.Q (C := X.Modules)).commShiftIso n).app P.obj ≪≫
        (shiftFunctor _ n).mapIso eP⟩⟩⟩

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsTriangulatedClosed₃ :=
  .mk' (by
    intro T hT h₁ h₂
    obtain ⟨P, ⟨eP⟩⟩ := (perfectDerivedObjects_iff_exists_representative X _).mp h₁
    obtain ⟨L, ⟨eL⟩⟩ := (perfectDerivedObjects_iff_exists_representative X _).mp h₂
    obtain ⟨M, g, s, hsIso, heFac⟩ := DerivedCategory.left_fac (eP.hom ≫ T.mor₁ ≫ eL.inv)
    let : IsIso ((DerivedCategory.Q (C := X.Modules)).map s) := hsIso
    have hs : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules s).1 hsIso
    let : QuasiIso s := hs
    have he : (eP.hom ≫ T.mor₁ ≫ eL.inv) ≫ (DerivedCategory.Q (C := X.Modules)).map s =
        (DerivedCategory.Q (C := X.Modules)).map g := by
      rw [heFac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hM : locallyPerfect X M := (locallyPerfect_iff_of_quasiIso s).mp L.property
    let eM : (DerivedCategory.Q (C := X.Modules)).obj M ≅ T.obj₂ :=
      (asIso ((DerivedCategory.Q (C := X.Modules)).map s)).symm ≪≫ eL
    have hc : (DerivedCategory.Q (C := X.Modules)).map g ≫ eM.hom = eP.hom ≫ T.mor₁ := by
      rw [← he]
      simp [eM]
    let e := Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ T
      (DerivedCategory.mappingCone_triangle_distinguished g) hT eP eM hc)
    exact (perfectDerivedObjects_iff_exists_representative X _).mpr
      ⟨⟨CochainComplex.mappingCone g, locallyPerfect_mappingCone P.property hM g⟩, ⟨e⟩⟩)

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsTriangulatedClosed₂ :=
  .of_isTriangulatedClosed₃

instance (X : Scheme.{u}) : (perfectDerivedObjects X).IsTriangulated where

/-- The actual full triangulated subcategory of intrinsic perfect objects. -/
abbrev PerfectDerived (X : Scheme.{u}) := (perfectDerivedObjects X).FullSubcategory

/-- The original perfect-complex localization, corestricted to its intrinsic perfect target. -/
def perfectToDerived (X : Scheme.{u}) : Perfect X ⥤ PerfectDerived X :=
  (perfectDerivedObjects X).lift ((locallyPerfect X).ι ⋙ DerivedCategory.Q (C := X.Modules))
    (fun P => (perfectDerivedObjects_toDerived_iff X P.obj).mpr P.property)

lemma perfectToDerived_isIso_map_iff {X : Scheme.{u}} {K L : Perfect X} (f : K ⟶ L) :
    IsIso ((perfectToDerived X).map f) ↔ QuasiIso f.hom := by
  rw [← isIso_iff_of_reflects_iso ((perfectToDerived X).map f) (perfectDerivedObjects X).ι]
  exact DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules f.hom

lemma perfectDerivedObjects_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K : DerivedCategory X.Modules} (hK : perfectDerivedObjects X K) :
    perfectDerivedObjects U ((derivedRestrict j).obj K) := by
  obtain ⟨P, ⟨eP⟩⟩ := (perfectDerivedObjects_iff_exists_representative X K).mp hK
  apply (perfectDerivedObjects_iff_exists_representative U _).mpr
  exact ⟨⟨(Complex.restrict j).obj P.obj, locallyPerfect_restrict j P.property⟩,
    ⟨((derivedRestrictFactors j).app P.obj).symm ≪≫ (derivedRestrict j).mapIso eP⟩⟩

/-- Open restriction on actual perfect derived objects, retaining the original derived functor. -/
def perfectDerivedRestrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PerfectDerived X ⥤ PerfectDerived U :=
  (perfectDerivedObjects U).lift ((perfectDerivedObjects X).ι ⋙ derivedRestrict j)
    (fun K => perfectDerivedObjects_restrict j K.property)

@[simp]
lemma perfectDerivedRestrict_map {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : PerfectDerived X} (f : K ⟶ L) :
    ((perfectDerivedRestrict j).map f).hom = (derivedRestrict j).map f.hom := rfl

/-- The original perfect restriction and original derived restriction commute through the specified
  localization factorization. -/
def perfectDerivedRestrictFactors {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    perfectToDerived X ⋙ perfectDerivedRestrict j ≅ perfectRestrict j ⋙ perfectToDerived U :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _ ((derivedRestrictFactors j).app K.obj))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (derivedRestrictFactors j).hom.naturality f.hom)

end AlgebraicGeometry.Scheme.Modules
