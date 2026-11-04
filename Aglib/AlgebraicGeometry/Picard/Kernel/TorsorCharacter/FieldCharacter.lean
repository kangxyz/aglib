/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.BaseChange
public import Aglib.AlgebraicGeometry.Picard.FamilyBaseChange.Group
public import Aglib.AlgebraicGeometry.Picard.Kernel.Characters

/-! Comparison of original kernel characters from their multipliers. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.OverField Scheme.Group Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A B : Grp (FScheme k)} [IsProper A.X.hom] [GeometricallyIntegral A.X.hom]
  (q : A ⟶ B) (T : FScheme K)
  (M : LineBundle (pullback B.X.hom ((Over.map (Spec.algebraMap k K)).obj T).hom))
  (a : (Scheme.Modules.pullback
    (familyMapOfHom q.hom.hom ((Over.map (Spec.algebraMap k K)).obj T))).obj M.val ≅
      SheafOfModules.unit
        (pullback A.X.hom ((Over.map (Spec.algebraMap k K)).obj T).hom).ringCatSheaf)

local notation "b" => Spec.algebraMap k K
local notation "F" => Over.pullback b
local notation "Anew" => Functor.obj (Functor.mapGrp F) A
local notation "Bnew" => Functor.obj (Functor.mapGrp F) B
local notation "qK" => CategoryTheory.Functor.map (Functor.mapGrp F) q
local notation "qOver" => Mon.Hom.hom (InducedCategory.Hom.hom qK)
local notation "T₀" => Functor.obj (Over.map b) T
local notation "G" => Kernel.group q
local notation "j" => Kernel.baseChangeIso b q

local instance proper_field_source : IsProper (Anew).X.hom :=
  inferInstanceAs (IsProper (pullback.snd A.X.hom b))

local instance integral_field_source : GeometricallyIntegral (Anew).X.hom :=
  inferInstanceAs (GeometricallyIntegral (pullback.snd A.X.hom b))

/-- A scalar-extension equality of the actual multipliers identifies the
actual characters through the original kernel and composition comparisons. -/
theorem kernelTrivializationCharacter_fieldBaseChange_of_multiplier
    (N : LineBundle (pullback (Bnew).X.hom T.hom))
    (c : (Scheme.Modules.pullback (familyMapOfHom qOver T)).obj N.val ≅
      SheafOfModules.unit (pullback (Anew).X.hom T.hom).ringCatSheaf)
    (hμ : kernelMultiplier qK (Kernel.marking qK) T N c =
      Units.map
        (familyMapOfHom (j).inv.hom.hom T ≫
          (familyBaseChangeIso (G).X.hom b T).hom).appTop.hom.toMonoidHom
        (kernelMultiplier q (Kernel.marking q) T₀ M a)) :
    (Over.pullback T.hom).mapGrp.map (j).hom ≫
        kernelTrivializationCharacter qK (Kernel.marking qK) T N c =
      (Group.BaseChange.groupSchemeBaseChangeComp T.hom b).inv.app G ≫
        kernelTrivializationCharacter q (Kernel.marking q) T₀ M a := by
  let e := (Over.pullback T.hom).mapGrp.map (j).hom
  let d := (Group.BaseChange.groupSchemeBaseChangeComp T.hom b).inv.app G
  let h := familyMapOfHom (j).inv.hom.hom T ≫ (familyBaseChangeIso (G).X.hom b T).hom
  let μ₀ := kernelMultiplier q (Kernel.marking q) T₀ M a
  let μ₁ := kernelMultiplier qK (Kernel.marking qK) T N c
  let χ₀ := kernelTrivializationCharacter q (Kernel.marking q) T₀ M a
  let χ₁ := kernelTrivializationCharacter qK (Kernel.marking qK) T N c
  let U := ((Over.pullback T.hom).mapGrp.obj ((F).mapGrp.obj G)).X
  have hj : (j).hom.hom.hom ≫ (j).inv.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) (j).hom_inv_id
  have hh : e.hom.hom.left ≫ familyMapOfHom (j).inv.hom.hom T = 𝟙 _ := by
    change familyMapOfHom (j).hom.hom.hom T ≫ familyMapOfHom (j).inv.hom.hom T = 𝟙 _
    rw [← familyMapOfHom_comp, hj, familyMapOfHom_id]
  let r := familyMapOfHom (j).inv.hom.hom T
  let s : U.left ⟶ pullback (G).X.hom (T.hom ≫ b) := (familyBaseChangeIso (G).X.hom b T).hom
  have hAssoc : e.hom.hom.left ≫ h = (e.hom.hom.left ≫ r) ≫ s :=
    (Category.assoc e.hom.hom.left r s).symm
  have hCancel : (e.hom.hom.left ≫ r) ≫ s = 𝟙 U.left ≫ s :=
    congrArg (fun f => f ≫ s) hh
  have hComp : s = d.hom.hom.left :=
    (groupSchemeBaseChangeComp_inv_left_eq_familyBaseChangeIso_hom b G T).symm
  have hproj : e.hom.hom.left ≫ h = d.hom.hom.left :=
    hAssoc.trans (hCancel.trans ((Category.id_comp s).trans hComp))
  have h₁ : MultiplicativeGroup.sectionsUnitsEquiv T.left U
        (e.hom.hom ≫ χ₁.hom.hom) = Units.map e.hom.hom.left.appTop.hom.toMonoidHom μ₁ :=
    kernelTrivializationCharacterMap_units qK (Kernel.marking qK) T N c U e.hom.hom
  have h₀ : MultiplicativeGroup.sectionsUnitsEquiv T.left U
        (d.hom.hom ≫ χ₀.hom.hom) = Units.map d.hom.hom.left.appTop.hom.toMonoidHom μ₀ :=
    kernelTrivializationCharacterMap_units q (Kernel.marking q) T₀ M a U d.hom.hom
  have hU : Units.map e.hom.hom.left.appTop.hom.toMonoidHom μ₁ =
      Units.map d.hom.hom.left.appTop.hom.toMonoidHom μ₀ := calc
    _ = Units.map e.hom.hom.left.appTop.hom.toMonoidHom
        (Units.map h.appTop.hom.toMonoidHom μ₀) := congrArg _ hμ
    _ = _ := by
      apply Units.ext
      have hMaps : h.appTop ≫ e.hom.hom.left.appTop = d.hom.hom.left.appTop :=
        (Scheme.Hom.comp_appTop e.hom.hom.left h).symm.trans (congrArg (fun f => f.appTop) hproj)
      exact congrArg (fun f => f μ₀.val) hMaps
  apply Grp.hom_ext
  exact (MultiplicativeGroup.sectionsUnitsEquiv T.left U).injective
    (h₁.trans (hU.trans h₀.symm))

/-- A named scalar extension of the original map has the same character
after transporting the original kernel and changing the frame of the same bundle. -/
theorem kernelTrivializationCharacter_fieldBaseChange_of_multiplier_eq
    (N : LineBundle (pullback (Bnew).X.hom T.hom))
    (c : (Scheme.Modules.pullback (familyMapOfHom qOver T)).obj N.val ≅
      SheafOfModules.unit (pullback (Anew).X.hom T.hom).ringCatSheaf)
    (hμ : kernelMultiplier qK (Kernel.marking qK) T N c =
      Units.map
        (familyMapOfHom (j).inv.hom.hom T ≫
          (familyBaseChangeIso (G).X.hom b T).hom).appTop.hom.toMonoidHom
        (kernelMultiplier q (Kernel.marking q) T₀ M a))
    (q' : Anew ⟶ Bnew) (h : qK = q')
    (c' : (Scheme.Modules.pullback (familyMapOfHom q'.hom.hom T)).obj N.val ≅
      SheafOfModules.unit (pullback (Anew).X.hom T.hom).ringCatSheaf)
    (u : ((F).mapGrp.obj G) ⟶ Kernel.group q')
    (hu : u = (j).hom ≫ (eqToIso (congrArg (fun f => Kernel.group f) h)).hom) :
    (Over.pullback T.hom).mapGrp.map u ≫
        kernelTrivializationCharacter q' (Kernel.marking q') T N c' =
      (Group.BaseChange.groupSchemeBaseChangeComp T.hom b).inv.app G ≫
        kernelTrivializationCharacter q (Kernel.marking q) T₀ M a := by
  subst q'
  have hu' : u = (j).hom := hu.trans (Category.comp_id (j).hom)
  subst u
  have hc := kernelMultiplier_eq_of_iso qK (Kernel.marking qK) T N c' N (Iso.refl _) c
  exact kernelTrivializationCharacter_fieldBaseChange_of_multiplier q T M a N c' (hc.trans hμ)

end AlgebraicGeometry.Scheme.RelativePicard
