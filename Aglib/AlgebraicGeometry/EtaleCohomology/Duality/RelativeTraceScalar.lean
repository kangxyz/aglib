/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FieldTraceValue
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RelativeTraceNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldDirectImageValue

/-! Scalar values of the original relative product trace. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

@[expose] public noncomputable section
namespace CategoryTheory.Functor

/-- An original injective restriction detects a scalar endomorphism after a
specified identification of its restricted object. -/
theorem eq_nsmul_id_of_conjugated_map_eq
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (G : C ⥤ D) [G.Additive] {I : C} {J : D} (e : G.obj I ≅ J)
    (hG : Function.Injective (fun g : I ⟶ I => G.map g))
    (a : I ⟶ I) (m : ℕ) (h : e.inv ≫ G.map a ≫ e.hom = m • 𝟙 J) :
    a = m • 𝟙 I := by
  apply hG
  apply (cancel_epi e.inv).mp
  apply (cancel_mono e.hom).mp
  have h₀ : e.inv ≫ G.map (m • 𝟙 I) ≫ e.hom = m • 𝟙 J := by
    rw [G.map_nsmul, G.map_id, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, e.inv_hom_id]
  simpa only [Category.assoc] using h.trans h₀.symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve Scheme.OverField.Curve.PointDivisor
open GroupCohomology.Kummer.CoefficientBaseChange

universe u wB wY wZ wEZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  (o : Base k ⟶ Y.left) (ho : o ≫ Y.hom = 𝟙 (Base k))

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)
set_option hygiene false in
local notation "Z" => pullback Y.hom Y.hom
set_option hygiene false in
local notation "π" => pullback.snd Y.hom Y.hom
set_option hygiene false in
local notation "q" => pullback.fst Y.hom Y.hom

variable [HasDerivedCategory.{wB} (ModuleSheaf (Base k) Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [HasExt.{wEZ} (ModuleSheaf Z Λ)]

local instance : HasExt.{u + 2} (ModuleSheaf Y.left Λ) :=
  SheafOfModules.hasExt (constantRing Y.left Λ)
local instance : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.left) := hasExtStandard Y.left

set_option hygiene false in
local notation "I" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
  (moduleUnit Y.left Λ)
set_option hygiene false in
local notation "I₀" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf (Base k) Λ) 0).obj
  (moduleUnit (Base k) Λ)
set_option hygiene false in
local notation "M" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj
  (moduleRootsOfUnity Z n)
set_option hygiene false in
local notation "M₀" => (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
  (moduleRootsOfUnity Y.left n)

/-- A relative trace with the original section comparison evaluates the scalar
of the original restricted degree-two class. -/
abbrev properCurveProductOrdinaryTraceNsmul
    (a : ((moduleDerivedDirectImage Λ π).obj M)⟦(2 : ℤ)⟧ ⟶ I)
    (x : Ext.{wEZ} (moduleUnit Z Λ) (moduleRootsOfUnity Z n) 2)
    (h :
      let p := Y.hom
      let i := diagonalSectionFibreMap p o ho
      let hi := levelInvertible q n (modulePoint_globalLevelInvertible n hunit)
      let y := moduleRootsUnitExtPullback i n hn hi 2 x
      let R := moduleDerivedDirectImage Λ p
      let e := constantModuleDerivedUnitPullbackIso π n
      let e₀ := constantModuleDerivedUnitPullbackIso p n
      let eo := constantModuleDerivedUnitPullbackIso o n
      let hK := DerivedCategory.Plus.isLE_of_original_homology (R.obj M₀) 2
        (properCurveRootsDirectImage_isZero_homology hY n hn hunit)
      OriginalClassTraceRestrictionValue (moduleDerivedAdjunction Λ π)
        (moduleDerivedAdjunction Λ p) e e₀ eo hK
          (properCurveTopDirectImageTraceIso hY n hn hunit).hom x.homPlus y.homPlus a) :=
  let p := Y.hom
  let i := diagonalSectionFibreMap p o ho
  let hi := levelInvertible q n (modulePoint_globalLevelInvertible n hunit)
  let y := moduleRootsUnitExtPullback i n hn hi 2 x
  let s := Curves.traceAddEquiv hY n hn hunit (modulePoint_globalLevelInvertible n hunit)
    (moduleRootsUnitExtCohomologyAddEquiv Y.left n 2 y)
  letI : NeZero n := ⟨ne_of_gt hn⟩
  letI : IsProper p := hY.proper
  letI : IsNoetherian Y.left := curveProperties_isNoetherian hY
  letI : ConnectedSpace Y.left := curveProperties_connectedSpace hY
  let F := DerivedCategory.Plus.singleFunctor (ModuleSheaf (Base k) Λ) 0
  let G := moduleDerivedInverseImage Λ o
  let u := constantModuleDerivedUnitPullbackIso o n
  let hScalarSection := moduleFieldUnitSectionsEquiv_nsmul_id k n s
  let E := moduleFieldUnitSectionsEquiv k Λ (moduleUnit (Base k) Λ)
  let hE := (congrArg E.symm hScalarSection).symm.trans (E.symm_apply_apply _)
  let hF : F.map (s.val • 𝟙 (moduleUnit (Base k) Λ)) = s.val • 𝟙 I₀ := by
    rw [F.map_nsmul, F.map_id]
  let hField := (properCurveFieldOrdinaryTrace_value hY n hn hunit y).trans
    ((congrArg F.map hE).trans hF)
  let hG := moduleDerivedInverseImage_map_injective_singleUnit_end o Λ _root_.isAddTorsion_of_finite
  Functor.eq_nsmul_id_of_conjugated_map_eq G u hG _ s.val (h.trans hField)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
