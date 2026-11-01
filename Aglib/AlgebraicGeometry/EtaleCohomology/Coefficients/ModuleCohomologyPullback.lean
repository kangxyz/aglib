/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Exactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitInverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Slice
public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingComposition

/-!
# Original module-unit cohomology and scheme pullback

The integer-to-unit map factors through the original constant scalar sheaf
and its original underlying-unit isomorphism. This normalization supplies the
source square for the actual module inverse image and abelian cohomology
pullback, without changing either cohomology realization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u wMX wMU wAX wAU

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

section IntegerNormalization

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The canonical integer-to-scalar coefficient morphism, with the original
lifted integer source of the module cohomology comparison. -/
def moduleUnitIntegerScalarHom :
    AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ AddCommGrpCat.of Λ :=
  AddCommGrpCat.ofHom ((Int.castAddHom Λ).comp AddEquiv.ulift.toAddMonoidHom)

/-- The original underlying-unit isomorphism is adjoint to its original
constant presheaf map, before any section evaluation. -/
theorem moduleUnitUnderlyingIso_homEquiv :
    (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _
        (moduleUnitUnderlyingIso X Λ).hom = moduleUnitConstantMap X Λ := by
  let F := (SheafOfModules.toSheaf (constantRing X Λ)).obj (moduleUnit X Λ)
  change (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ F
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (moduleUnitConstantMap X Λ) ≫
        (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).counit.app F) = _
  simpa only [Adjunction.homEquiv_counit] using
    ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
      ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of Λ)) F).apply_symm_apply
        (moduleUnitConstantMap X Λ)

/-- The selected integer-to-unit map factors through the actual constant
scalar map and the selected underlying-unit isomorphism, for every ring. -/
theorem liftedUnitIntegerMap_factorization :
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1}
        terminalIsTerminal (constantRing X Λ) =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (moduleUnitIntegerScalarHom Λ) ≫ (moduleUnitUnderlyingIso X Λ).hom := by
  have he : (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).homEquiv _ _ (moduleUnitUnderlyingIso X Λ).hom =
        (moduleUnitConstantMap X Λ).app (op (⊤_ X.Etale)) := by
    change (constantPresheafAdj AddCommGrpCat.{u + 1} terminalIsTerminal).homEquiv _ _
      ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _
        (moduleUnitUnderlyingIso X Λ).hom) = _
    rw [moduleUnitUnderlyingIso_homEquiv]
    rfl
  apply (Sheaf.ModuleCoefficients.integerHomTerminalEquiv terminalIsTerminal _).injective
  rw [Sheaf.ModuleCoefficients.liftedUnitIntegerMap_sections]
  change ULift.up (1 : (constantRing X Λ).obj.obj (op (⊤_ X.Etale))) =
    AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).homEquiv _ _
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
            (moduleUnitIntegerScalarHom Λ) ≫ (moduleUnitUnderlyingIso X Λ).hom))
  have hn := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).homEquiv_naturality_left (moduleUnitIntegerScalarHom Λ)
      (moduleUnitUnderlyingIso X Λ).hom
  rw [hn, he]
  change ULift.up (1 : (constantRing X Λ).obj.obj (op (⊤_ X.Etale))) =
    ULift.up (((constantRingUnit X Λ).app (op (⊤_ X.Etale))).hom ((1 : ℤ) : Λ))
  rw [Int.cast_one, map_one]

end IntegerNormalization

section SchemePullback

variable {U X : Scheme.{u}} (f : U ⟶ X) (n : ℕ)

/-- The inverse of the selected module-unit comparison retains its original
underlying constant-sheaf and inverse-image maps. -/
theorem moduleUnitInverseImageIso_inv_underlying :
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).map
        (moduleUnitInverseImageIso f n).inv ≫
      (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f).hom.app
        (moduleUnit X (ULift.{u + 1} (ZMod n))) =
    (moduleUnitUnderlyingIso U (ULift.{u + 1} (ZMod n))).inv ≫
      (inverseImageConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ≫
        (inverseImage f).map (moduleUnitUnderlyingIso X (ULift.{u + 1} (ZMod n))).hom := by
  let Λ := ULift.{u + 1} (ZMod n)
  let Q : ModuleSheaf U Λ ⥤ AbelianSheaf.{u, u + 1} U :=
    SheafOfModules.toSheaf (constantRing U Λ)
  let e := Q.mapIso (moduleUnitInverseImageIso f n)
  let eX := moduleUnitUnderlyingIso X Λ
  let eU := moduleUnitUnderlyingIso U Λ
  let c := (inverseImageConstantIso f).app (AddCommGrpCat.of Λ)
  let t := (moduleInverseImageUnderlyingIso Λ f).app (moduleUnit X Λ)
  have h : e.hom = t.hom ≫ (inverseImage f).map eX.inv ≫ c.hom ≫ eU.hom :=
    moduleUnitInverseImageIso_underlying f n
  change e.inv ≫ t.hom = eU.inv ≫ c.inv ≫ (inverseImage f).map eX.hom
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact (Category.comp_id t.hom).symm

/-- The original integer-to-unit source square commutes for every scheme
morphism and every level, including zero and one. -/
theorem liftedUnitIntegerMap_inverseImage :
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1} terminalIsTerminal
        (constantRing U (ULift.{u + 1} (ZMod n))) ≫
      (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).map
        (moduleUnitInverseImageIso f n).inv ≫
      (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f).hom.app
        (moduleUnit X (ULift.{u + 1} (ZMod n))) =
    (inverseImageConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
      (inverseImage f).map
        (Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1} terminalIsTerminal
          (constantRing X (ULift.{u + 1} (ZMod n)))) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let QX : ModuleSheaf X Λ ⥤ AbelianSheaf.{u, u + 1} X :=
    SheafOfModules.toSheaf (constantRing X Λ)
  let QU : ModuleSheaf U Λ ⥤ AbelianSheaf.{u, u + 1} U :=
    SheafOfModules.toSheaf (constantRing U Λ)
  let S := inverseImage f
  let CX := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let CU := constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}
  let β := moduleUnitIntegerScalarHom Λ
  let αX : CX.obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ QX.obj (moduleUnit X Λ) :=
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1}
      terminalIsTerminal (constantRing X Λ)
  let αU : CU.obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ QU.obj (moduleUnit U Λ) :=
    Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1}
      terminalIsTerminal (constantRing U Λ)
  let eX := moduleUnitUnderlyingIso X Λ
  let eU := moduleUnitUnderlyingIso U Λ
  let c := (inverseImageConstantIso f).app (AddCommGrpCat.of Λ)
  let z := (inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let t := (moduleInverseImageUnderlyingIso Λ f).app (moduleUnit X Λ)
  let e := moduleUnitInverseImageIso f n
  have hInv : QU.map e.inv ≫ t.hom = eU.inv ≫ c.inv ≫ S.map eX.hom :=
    moduleUnitInverseImageIso_inv_underlying f n
  have hX : αX = CX.map β ≫ eX.hom := liftedUnitIntegerMap_factorization X Λ
  have hU : αU = CU.map β ≫ eU.hom := liftedUnitIntegerMap_factorization U Λ
  have hβ : CU.map β ≫ c.inv = z.inv ≫ S.map (CX.map β) :=
    (inverseImageConstantIso f).inv.naturality β
  change αU ≫ QU.map e.inv ≫ t.hom = z.inv ≫ S.map αX
  calc
    αU ≫ QU.map e.inv ≫ t.hom = αU ≫ eU.inv ≫ c.inv ≫ S.map eX.hom := by
      simpa only [Category.assoc] using congrArg
        (fun g : QU.obj (moduleUnit U Λ) ⟶ S.obj (QX.obj (moduleUnit X Λ)) => αU ≫ g) hInv
    _ = CU.map β ≫ c.inv ≫ S.map eX.hom := by
      rw [hU]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = z.inv ≫ S.map (CX.map β ≫ eX.hom) := by
      rw [← Category.assoc, hβ, Category.assoc, ← Functor.map_comp]
    _ = z.inv ≫ S.map αX := by rw [← hX]

variable [HasExt.{wMX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wMU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

/-- The original module-unit cohomology pullback: exact inverse image on Ext,
precomposed with the inverse of the selected native unit comparison. -/
def moduleUnitExtPullback (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Ext.{wMX} (moduleUnit X (ULift.{u + 1} (ZMod n))) M q →+
      Ext.{wMU} (moduleUnit U (ULift.{u + 1} (ZMod n)))
        ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj M) q :=
  (moduleInverseImage f (ULift.{u + 1} (ZMod n))).extPrecompMap
    (moduleUnitInverseImageIso f n).inv M q

/-- The pullback map retains the literal exact-functor Ext map and original
unit source transport. -/
theorem moduleUnitExtPullback_apply (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ)
    (e : Ext.{wMX} (moduleUnit X (ULift.{u + 1} (ZMod n))) M q) :
    moduleUnitExtPullback f n M q e =
      (Ext.mk₀ (moduleUnitInverseImageIso f n).inv).comp
        (e.mapExactFunctor (moduleInverseImage f (ULift.{u + 1} (ZMod n)))) (zero_add q) :=
  rfl

variable [HasExt.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]

/-- The whole module-unit Ext/cohomology pullback square, for arbitrary
scheme maps and all levels. The four Ext universes remain independent. -/
theorem moduleUnitExtCohomologyPullback_square
    (M : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    (Sheaf.H.map
        ((moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f).hom.app M) q).comp
      ((etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMU, wAU} U
          (constantRing U (ULift.{u + 1} (ZMod n)))
          ((moduleInverseImage f (ULift.{u + 1} (ZMod n))).obj M) q).toAddMonoidHom.comp
        (moduleUnitExtPullback.{u, wMX, wMU} f n M q)) =
    (cohomologyPullback.{u, wAX, wAU} f
        ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj M) q).comp
      (etaleModuleExtCohomologyAddEquivLargeScalars.{u, wMX, wAX} X
        (constantRing X (ULift.{u + 1} (ZMod n))) M q).toAddMonoidHom := by
  ext e
  exact Sheaf.ModuleCoefficients.extPrecompMap_square
    (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n))))
    (moduleInverseImage f (ULift.{u + 1} (ZMod n))) (inverseImage f)
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n))))
    (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) f).hom
    (moduleUnitInverseImageIso f n).inv
    ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv
    (Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1} terminalIsTerminal
      (constantRing X (ULift.{u + 1} (ZMod n))))
    (Sheaf.ModuleCoefficients.liftedUnitIntegerMap.{u + 1, u, u + 1, u + 1} terminalIsTerminal
      (constantRing U (ULift.{u + 1} (ZMod n))))
    (liftedUnitIntegerMap_inverseImage f n) q e

end SchemePullback

end AlgebraicGeometry.Scheme.EtaleCohomology
