/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Stalk
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent

/-!
# Original structure H1 on an actual local-spectrum pullback

The original R1 stalk identifies with H1 of the supplied local scheme,
with its original structural stalk-ring action. The actual Cartesian square,
native stalk/pullback sections, original flat base-change map, canonical
pullback-unit comparison and original affine cohomology comparison are retained.

Only the global map's quasi-compactness and quasi-separatedness are inputs.
The local replacement itself is supplied separately; this module constructs
no replacement scheme and asserts no universal local rationality theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y T : Scheme.{u}}
  (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (x : X)
  (a : T ⟶ Y) (p : T ⟶ Spec (X.presheaf.stalk x))
  (square : IsPullback a p h (X.fromSpecStalk x))

/-- The original stalk of R1 identifies with H1 on the caller's actual
local scheme, using the actual pullback square and original local-ring action.
The symmetry gives the requested H1-to-stalk equivalence. -/
def originalStructureH1StalkLinearEquiv :
    let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    let OT : T.Modules := SheafOfModules.unit T.ringCatSheaf
    let α := p.appTop.hom.comp (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom
    letI := moduleCohomologyModuleOfHom T α OT 1
    (moduleStalk X x).obj (((Scheme.Modules.pushforward h).rightDerived 1).obj OY) ≃ₗ[
        X.presheaf.stalk x]
      Sheaf.H.{u + 1} (moduleAddSheaf T OT) 1 := by
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let OT : T.Modules := SheafOfModules.unit T.ringCatSheaf
  let : OY.IsQuasicoherent := Scheme.Modules.isQuasicoherent_unit Y
  let hOT : OT.IsQuasicoherent := Scheme.Modules.isQuasicoherent_unit T
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  let hpqc : QuasiCompact p := MorphismProperty.of_isPullback square inferInstance
  let hpqs : QuasiSeparated p := MorphismProperty.of_isPullback square inferInstance
  let α := p.appTop.hom.comp (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom
  let := moduleCohomologyModuleOfHom T α OT 1
  let unitIso : (Scheme.Modules.pullback a).obj OY ≅ OT := pullbackUnitIso a
  let e₁ : _ ≃ₗ[X.presheaf.stalk x] _ :=
    (stalkFromSpecStalkSectionsIso X x
      (((Scheme.Modules.pushforward h).rightDerived 1).obj OY)).toLinearEquiv
  let e₂ : _ ≃ₗ[X.presheaf.stalk x] _ :=
    (moduleSpecΓFunctor.mapIso (higherDirectImageFlatBaseChangeIso
      a p h (X.fromSpecStalk x) square OY 1)).toLinearEquiv
  let e₃ : _ ≃ₗ[X.presheaf.stalk x] _ :=
    (moduleSpecΓFunctor.mapIso
      (((Scheme.Modules.pushforward p).rightDerived 1).mapIso unitIso)).toLinearEquiv
  let e₄ := @moduleHigherDirectImageAffineSectionsLinearEquiv
    (X.presheaf.stalk x) inferInstance T p hpqc hpqs OT hOT (injectiveResolution OT) 1
  exact e₁.trans (e₂.trans (e₃.trans e₄))

include x a p square in
/-- The original global R1 vanishing result kills the actual local H1
through the supplied pullback diagram. No desired local vanishing is an input. -/
theorem original_localStructureH1_subsingleton_of_R1_isZero
    (hzero : IsZero (((Scheme.Modules.pushforward h).rightDerived 1).obj
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf))) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf T (show T.Modules from SheafOfModules.unit T.ringCatSheaf)) 1) := by
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let OT : T.Modules := SheafOfModules.unit T.ringCatSheaf
  let R1 := ((Scheme.Modules.pushforward h).rightDerived 1).obj OY
  let α := p.appTop.hom.comp (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom
  let := moduleCohomologyModuleOfHom T α OT 1
  have hs : IsZero ((moduleStalk X x).obj R1) :=
    (moduleStalk X x).map_isZero hzero
  let : Subsingleton ((moduleStalk X x).obj R1) := ModuleCat.subsingleton_of_isZero hs
  exact (originalStructureH1StalkLinearEquiv h x a p square).symm.injective.subsingleton

end AlgebraicGeometry.Scheme.Cohomology

