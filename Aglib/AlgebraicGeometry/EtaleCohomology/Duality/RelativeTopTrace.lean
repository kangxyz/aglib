/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ProperTopTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperBaseChange.ZMod
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedPullback

/-! Existence and normalization of the relative degree-two trace by proper exchange. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u wS wY wX wZ

namespace CategoryTheory

/-- Transport across the original invertible component and coefficient isomorphism is unique. -/
theorem existsUnique_comp_map_of_isIso {C D : Type*} [Category* C] [Category* D]
    (H : C ⥤ D) {K L M : C} {b : K ⟶ L} (hb : IsIso b)
    (c : L ≅ M) {U : D} (t : H.obj K ⟶ U) :
    ∃! a : H.obj M ⟶ U, (H.map b ≫ H.map c.hom) ≫ a = t := by
  let := hb
  let f := H.map b ≫ H.map c.hom
  let : IsIso f := inferInstance
  refine ⟨inv f ≫ t, ?_, fun a ha => ?_⟩
  · change f ≫ inv f ≫ t = t
    exact IsIso.hom_inv_id_assoc f t
  · change f ≫ a = t at ha
    apply (cancel_epi f).mp
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using ha

end CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  {X Z : Scheme.{u}} (g : X ⟶ Base k)
  (p : Z ⟶ X) (q : Z ⟶ Y.left) (sq : IsPullback q p Y.hom g)
  [HasDerivedCategory.{wS} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z (ULift.{u + 1} (ZMod n)))]

/-- The relative top trace is obtained from the original field trace by the original
proper exchange and the exact homology comparison. -/
abbrev properCurveRelativeTopDirectImageTraceExistsUnique :=
  let Λ := ULift.{u + 1} (ZMod n)
  let G := moduleInverseImage g Λ
  let K := (moduleDerivedDirectImage Λ Y.hom).obj
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
      (moduleRootsOfUnity Y.left n))
  let e := (G.rightDerivedFunctorPlusHomologyIso 2).app K
  let t := e.hom ≫ G.map (properCurveTopDirectImageTraceIso hY n hn hunit).hom ≫
    (moduleUnitInverseImageIso g n).hom
  let K' := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
    (moduleRootsOfUnity Y.left n)
  letI : IsProper Y.hom := hY.proper
  let hb := Proper.properModuleDerivedBaseChange_isIso_zmod n hn Y.hom p g q
    sq K'
  let a := moduleRootsDerivedSinglePullbackIso q n hn (modulePoint_globalLevelInvertible n hunit)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) 2
  existsUnique_comp_map_of_isIso H hb ((moduleDerivedDirectImage Λ p).mapIso a) t

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
