/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ProperTopTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.RelativeTopTrace

/-! The original proper curve roots direct image has top degree two. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

open Scheme.OverField Scheme.OverField.Curve

universe u wS wY wX wZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : FScheme k} (hY : Curve.Properties Y)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasDerivedCategory.{wS} (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wY} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]

include hY hn hunit in
/-- Higher homology of the actual proper-curve roots direct image is zero above two. -/
theorem properCurveRootsDirectImage_isZero_homology (q : ℤ) (hq : 2 < q) :
    let Λ := ULift.{u + 1} (ZMod n)
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Base k) Λ) q).obj
      ((moduleDerivedDirectImage Λ Y.hom).obj
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
          (moduleRootsOfUnity Y.left n)))) := by
  lift q to ℕ using (by omega : 0 ≤ q)
  let m := q
  let Λ := ULift.{u + 1} (ZMod n)
  let Γ := moduleGlobalSections (Base k) Λ
  let H := DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Base k) Λ) (m : ℤ)
  let M := moduleRootsOfUnity Y.left n
  let K := (moduleDerivedDirectImage Λ Y.hom).obj
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj M)
  let : HasExt.{u + 2} (ModuleSheaf Y.left Λ) := SheafOfModules.hasExt (constantRing Y.left Λ)
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y.left) := hasExtStandard Y.left
  let : LocallyOfFiniteType Y.hom := curveProperties_locallyOfFiniteType hY
  let : IsProper Y.hom := hY.proper
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let e := (moduleFieldDirectImageHomologyAddEquiv k Y.hom n M m).symm.trans
    (moduleRootsUnitExtCohomologyAddEquiv Y.left n m)
  let h := Curves.roots_subsingleton_H_of_curve k Y.left Y.hom
    hY.topologicalKrullDim_eq_one.le n hn hunit (modulePoint_globalLevelInvertible n hunit) m
    (by exact_mod_cast hq)
  have hs : Subsingleton (Γ.obj (H.obj K)) := ⟨fun a b => e.injective (h.elim _ _)⟩
  let : Γ.Faithful := by
    change (moduleGlobalSections (Base k) Λ).Faithful
    rw [← moduleFieldSectionsEquivalence_inverse k Λ]
    infer_instance
  apply (IsZero.iff_id_eq_zero (H.obj K)).mpr
  apply Γ.map_injective
  exact (ModuleCat.isZero_iff_subsingleton.mpr hs).eq_of_src _ _

private theorem isZero_of_exchange {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms D] [HasZeroMorphisms E]
    (H : C ⥤ D) (F : E ⥤ D) [F.PreservesZeroMorphisms]
    {K L M : C} {A : E} {b : K ⟶ L} (hb : IsIso b)
    (e : L ≅ M) (t : H.obj K ≅ F.obj A) (hz : IsZero A) : IsZero (H.obj M) := by
  let := hb
  exact (F.map_isZero hz).of_iso ((H.mapIso e).symm ≪≫ (H.mapIso (asIso b)).symm ≪≫ t)

variable {X Z : Scheme.{u}} (g : X ⟶ Base k)
  (p : Z ⟶ X) (q : Z ⟶ Y.left) (sq : IsPullback q p Y.hom g)
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z (ULift.{u + 1} (ZMod n)))]

include hY hn hunit g q sq in
omit [HasDerivedCategory (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))] in
/-- The original proper exchange transports the roots vanishing to every actual base change. -/
theorem properCurveRelativeRootsDirectImage_isZero_homology (r : ℤ) (hr : 2 < r) :
    let Λ := ULift.{u + 1} (ZMod n)
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) r).obj
      ((moduleDerivedDirectImage Λ p).obj
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj
          (moduleRootsOfUnity Z n)))) := by
  let Λ := ULift.{u + 1} (ZMod n)
  let := HasDerivedCategory.standard (ModuleSheaf (Base k) Λ)
  let := HasDerivedCategory.standard (ModuleSheaf Y.left Λ)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) r
  let G := moduleInverseImage g Λ
  let K := (DerivedCategory.Plus.singleFunctor (ModuleSheaf Y.left Λ) 0).obj
    (moduleRootsOfUnity Y.left n)
  let I := (moduleDerivedDirectImage Λ Y.hom).obj K
  let a := moduleRootsDerivedSinglePullbackIso q n hn (modulePoint_globalLevelInvertible n hunit)
  let : IsProper Y.hom := hY.proper
  have hb := Proper.properModuleDerivedBaseChange_isIso_zmod n hn Y.hom p g q sq K
  have hz := properCurveRootsDirectImage_isZero_homology hY n hn hunit r hr
  exact isZero_of_exchange H G hb ((moduleDerivedDirectImage Λ p).mapIso a)
    ((G.rightDerivedFunctorPlusHomologyIso r).app I) hz

include hY hn hunit g q sq in
omit [HasDerivedCategory (ModuleSheaf (Base k) (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))] in
/-- The original relative roots direct image admits its top homology projection in degree two. -/
theorem properCurveRelativeRootsDirectImage_isLE :
    let Λ := ULift.{u + 1} (ZMod n)
    ((moduleDerivedDirectImage Λ p).obj
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf Z Λ) 0).obj
        (moduleRootsOfUnity Z n))).IsLE 2 := by
  dsimp only
  apply (DerivedCategory.Plus.isLE_ι_obj_iff _ 2).mp
  apply (DerivedCategory.isLE_iff _ _).mpr
  exact properCurveRelativeRootsDirectImage_isZero_homology hY n hn hunit g p q sq

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
