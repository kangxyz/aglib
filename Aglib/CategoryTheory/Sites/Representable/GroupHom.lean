/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Representable.ImageHom
public import Aglib.CategoryTheory.Monoidal.Cartesian.RepresentedGroupReflection

/-! # Whole Hom equivalences for the original represented commutative groups

The underlying inverse is the actual restricted Yoneda inverse at the original
source test. Its component formula and the additive sheaf map derive both group
map laws through the existing reflection producer. The final group Hom equivalence
and both inverse proofs use these same maps. Actual test membership, terminal and
product comparisons are structural inputs, not the desired full-faithfulness.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory.CommutativeGroupSections

universe w uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [CartesianMonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) (J : GrothendieckTopology C)
  (H K : Grp D) [IsCommMonObj H.X] [IsCommMonObj K.X]

/-- Restrict the existing additive group-section functor to the actual tests. -/
def testPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{max vD w} := F.op ⋙ functor.{w} H

/-- Supply the original geometric sheafhood proof to that same presheaf. -/
def testSheaf (hH : Presheaf.IsSheaf J (testPresheaf.{w} F H)) :
    Sheaf J AddCommGrpCat.{max vD w} := ⟨testPresheaf.{w} F H, hH⟩

/-- Actual group postcomposition, with the original additive section values. -/
def testMap (q : H ⟶ K) : testPresheaf.{w} F H ⟶ testPresheaf.{w} F K :=
  Functor.whiskerLeft F.op (map.{w} q)

/-- The canonical existing additive/underlying Yoneda comparison, whiskered once. -/
def testForgetIso : testPresheaf.{w} F H ⋙ CategoryTheory.forget AddCommGrpCat.{max vD w} ≅
    LiftedRestrictedYoneda.presheaf.{w} F H.X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F.op (forgetIso.{w} H)

/-- Forget the given additive map through those same canonical value comparisons. -/
def testUnderlyingMap (q : testPresheaf.{w} F H ⟶ testPresheaf.{w} F K) :
    LiftedRestrictedYoneda.presheaf.{w} F H.X ⟶
      LiftedRestrictedYoneda.presheaf.{w} F K.X :=
  (testForgetIso.{w} F H).inv ≫
    Functor.whiskerRight q (CategoryTheory.forget AddCommGrpCat.{max vD w}) ≫
      (testForgetIso.{w} F K).hom

variable (U : C) (e : F.obj U ≅ H.X)

/-- The whole raw inverse comes from the proved actual-test Yoneda constructor. -/
def testPreimage (q : testPresheaf.{w} F H ⟶ testPresheaf.{w} F K) : H.X ⟶ K.X :=
  LiftedRestrictedYoneda.preimageOfTest.{w} F U e (testUnderlyingMap.{w} F H K q)

/-- The recovered raw map has exactly the original additive component value. -/
theorem testPreimage_app [F.Full] (q : testPresheaf.{w} F H ⟶ testPresheaf.{w} F K)
    (V : C) (f : F.obj V ⟶ H.X) :
    (ULift.up (Additive.ofMul (f ≫ testPreimage.{w} F H K U e q)) :
      Sections.{w} K (F.obj V)) = q.app (op V) (ULift.up (Additive.ofMul f)) := by
  have hv := LiftedRestrictedYoneda.preimageOfTest_app.{w} F U e
    (testUnderlyingMap.{w} F H K q) (op V) f
  exact congrArg (fun x => (ULift.up (Additive.ofMul x.down) :
    Sections.{w} K (F.obj V))) hv

variable (U₀ U₂ : C) (κ₀ : F.obj U₀ ≅ 𝟙_ D) (κ₂ : F.obj U₂ ≅ H.X ⊗ H.X)

/-- Reflect both group laws on the same Yoneda preimage from actual terminal/product tests. -/
def testGroupPreimage [F.Full] (q : testPresheaf.{w} F H ⟶ testPresheaf.{w} F K) : H ⟶ K := by
  let r := testPreimage.{w} F H K U e q
  letI : IsMonHom r := isMonHom_of_original_test_sections.{w, w}
    (T := F) (H := H) (K := K) (U₀ := U₀) (U₂ := U₂)
    (κ₀ := κ₀) (κ₂ := κ₂) (Q := fun V => (q.app (op V)).hom) (r := r)
    (hr := testPreimage_app.{w} F H K U e q)
  exact Grp.homMk r

/-- The constructed group map reproduces the whole original additive natural map. -/
theorem testMap_testGroupPreimage [F.Full]
    (q : testPresheaf.{w} F H ⟶ testPresheaf.{w} F K) :
    testMap.{w} F H K (testGroupPreimage.{w} F H K U e U₀ U₂ κ₀ κ₂ q) = q := by
  ext V a
  exact testPreimage_app.{w} F H K U e q V.unop a.down.toMul

/-- The inverse on an original group map is that very group map. -/
theorem testGroupPreimage_testMap [F.Full] (q : H ⟶ K) :
    testGroupPreimage.{w} F H K U e U₀ U₂ κ₀ κ₂ (testMap.{w} F H K q) = q := by
  apply Grp.hom_ext
  change LiftedRestrictedYoneda.preimageOfTest.{w} F U e
    (testUnderlyingMap.{w} F H K (testMap.{w} F H K q)) = q.hom.hom
  have hq : testUnderlyingMap.{w} F H K (testMap.{w} F H K q) =
      LiftedRestrictedYoneda.map.{w} F q.hom.hom := by
    ext V a
    rfl
  rw [hq, LiftedRestrictedYoneda.preimageOfTest_map]

/-- Full faithfulness on these represented groups is a complete proved Hom equivalence. -/
def testHomEquiv [F.Full] : (H ⟶ K) ≃ (testPresheaf.{w} F H ⟶ testPresheaf.{w} F K) where
  toFun := testMap.{w} F H K
  invFun := testGroupPreimage.{w} F H K U e U₀ U₂ κ₀ κ₂
  left_inv := testGroupPreimage_testMap.{w} F H K U e U₀ U₂ κ₀ κ₂
  right_inv := testMap_testGroupPreimage.{w} F H K U e U₀ U₂ κ₀ κ₂

/-- The same actual sheafhood proofs give the whole sheaf Hom equivalence. -/
def testSheafHomEquiv [F.Full]
    (hH : Presheaf.IsSheaf J (testPresheaf.{w} F H))
    (hK : Presheaf.IsSheaf J (testPresheaf.{w} F K)) :
    (H ⟶ K) ≃ (testSheaf.{w} F J H hH ⟶ testSheaf.{w} F J K hK) where
  toFun q := ⟨testMap.{w} F H K q⟩
  invFun q := testGroupPreimage.{w} F H K U e U₀ U₂ κ₀ κ₂ q.hom
  left_inv := testGroupPreimage_testMap.{w} F H K U e U₀ U₂ κ₀ κ₂
  right_inv q := by
    apply Sheaf.hom_ext
    exact testMap_testGroupPreimage.{w} F H K U e U₀ U₂ κ₀ κ₂ q.hom

end CategoryTheory.CommutativeGroupSections
