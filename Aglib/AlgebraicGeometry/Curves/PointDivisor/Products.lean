/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.PoleFunctions
public import Aglib.AlgebraicGeometry.Curves.Picard.GenericTrivialization

/-!
# Native products of the original point-pole sections

The native unit and associator maps compare actual tensor powers at every
pair of bounds, including zero. Their comparison with the normalized
point-divisor sheaves is an equality of actual sheaf maps. Original global
section multiplication is therefore literal multiplication in the same
function field with the original structural scalar action.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

variable {k : Type u} [Field k] (X : FScheme k) (hX : Properties X)
  [IsIntegral X.left] [IsNoetherian X.left]
  [∀ x : Scheme.ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

local instance : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩

private theorem tensor_map_section (Y : Scheme.{u})
    {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N')
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (tensorSheafMap Y a b).val.app (op U) (moduleTensorSection Y M N U m n) =
      moduleTensorSection Y M' N' U (a.val.app (op U) m) (b.val.app (op U) n) :=
  SheafOfModulesOfCommRing.tensor_map_tensorSection Y.sheaf a b (op U) m n

private theorem tensor_iso_section (Y : Scheme.{u})
    {M M' N N' : Y.Modules} (a : M ≅ M') (b : N ≅ N')
    (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (tensorSheafIso Y a b).hom.val.app (op U) (moduleTensorSection Y M N U m n) =
      moduleTensorSection Y M' N' U (a.hom.val.app (op U) m) (b.hom.val.app (op U) n) :=
  tensor_map_section Y a.hom b.hom U m n

private theorem divisor_cast_value {D E : Divisor X.left} (h : D = E)
    (U : X.left.Opens) [Nonempty U]
    (s : (DivisorClass.divisorSheaf X.left D).val.obj (op U)) :
    Scheme.Modules.RationalFunctions.rationalValue X.left U
        ((eqToIso (congrArg (DivisorClass.divisorSheaf X.left) h)).hom.val.app (op U) s).val =
      Scheme.Modules.RationalFunctions.rationalValue X.left U s.val := by
  cases h
  rfl

private theorem divisor_tensor_section (D E : Divisor X.left) (U : X.left.Opens)
    (s : (DivisorClass.divisorSheaf X.left D).val.obj (op U))
    (t : (DivisorClass.divisorSheaf X.left E).val.obj (op U)) :
    (DivisorClass.divisorTensorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E).hom.val.app (op U)
      (moduleTensorSection X.left _ _ U s t) =
        DivisorClass.divisorMultiplySections X.left D E U s t := by
  have h := congrArg (fun f ↦ f.val.app (op U) (moduleTensorSection X.left _ _ U s t))
    (DivisorClass.divisorTensorIso_hom X.left
      (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E)
  exact h.trans (Picard.GenericTrivialization.divisorMultiplication_tmul X.left D E (op U) s t)

private theorem firstTensorPowerIso_tensorSection (Y : Scheme.{u}) (L : LineBundle Y)
    (U : Y.Opens) (s : Γ(L.val, U))
    (t : Γ((tensorPowerLineBundle Y L 0).val, U)) :
    (firstTensorPowerIso Y L).hom.val.app (op U)
        (moduleTensorSection Y L.val (tensorPowerLineBundle Y L 0).val U s t) =
      (show Γ(Y, U) from (Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)).hom.val.app
          (op U) t) • s := by
  let c₀ := Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)
  change ((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app L.val).hom.val.app
    (op U) ((tensorSheafIso Y (Iso.refl L.val) c₀).hom.val.app (op U)
      (moduleTensorSection Y L.val (tensorPowerLineBundle Y L 0).val U s t)) = _
  have ht := tensor_iso_section Y (Iso.refl L.val) c₀ U s t
  exact (congrArg (fun z ↦
    ((SheafOfModulesOfCommRing.tensorRightUnitIso Y.sheaf).app L.val).hom.val.app
      (op U) z) ht).trans
    (tensorRightUnitIso_hom_section Y L.val U s (c₀.hom.val.app (op U) t))

private theorem divisor_tensor_iso_value {M N : X.left.Modules}
    (D E : Divisor X.left) (a : M ≅ DivisorClass.divisorSheaf X.left D)
    (b : N ≅ DivisorClass.divisorSheaf X.left E)
    (U : X.left.Opens) [Nonempty U] (s : Γ(M, U)) (t : Γ(N, U)) :
    Scheme.Modules.RationalFunctions.rationalValue X.left U
      ((DivisorClass.divisorTensorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E).hom.val.app
          (op U) ((tensorSheafIso X.left a b).hom.val.app (op U)
            (moduleTensorSection X.left M N U s t))).val =
      Scheme.Modules.RationalFunctions.rationalValue X.left U (a.hom.val.app (op U) s).val *
        Scheme.Modules.RationalFunctions.rationalValue X.left U (b.hom.val.app (op U) t).val := by
  let s' := a.hom.val.app (op U) s
  let t' := b.hom.val.app (op U) t
  have ht := tensor_iso_section X.left a b U s t
  have hm := divisor_tensor_section X hX D E U s' t'
  calc
    _ = Scheme.Modules.RationalFunctions.rationalValue X.left U
        ((DivisorClass.divisorTensorIso X.left
          (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E).hom.val.app
            (op U) (moduleTensorSection X.left _ _ U s' t')).val :=
      congrArg (fun z ↦ Scheme.Modules.RationalFunctions.rationalValue X.left U
        ((DivisorClass.divisorTensorIso X.left
          (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E).hom.val.app
            (op U) z).val) ht
    _ = Scheme.Modules.RationalFunctions.rationalValue X.left U
        (DivisorClass.divisorMultiplySections X.left D E U s' t').val :=
      congrArg (fun z ↦ Scheme.Modules.RationalFunctions.rationalValue X.left U z.val) hm
    _ = _ := DivisorClass.divisorMultiplySections_value X.left D E U s' t'

private theorem divisor_tensor_cast_iso_value {M N : X.left.Modules}
    (D E T : Divisor X.left) (h : D + E = T)
    (a : M ≅ DivisorClass.divisorSheaf X.left D)
    (b : N ≅ DivisorClass.divisorSheaf X.left E)
    (U : X.left.Opens) [Nonempty U] (s : Γ(M, U)) (t : Γ(N, U)) :
    Scheme.Modules.RationalFunctions.rationalValue X.left U
      (((tensorSheafIso X.left a b ≪≫ DivisorClass.divisorTensorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E ≪≫
        eqToIso (congrArg (DivisorClass.divisorSheaf X.left) h)).hom.val.app
          (op U) (moduleTensorSection X.left M N U s t))).val =
      Scheme.Modules.RationalFunctions.rationalValue X.left U (a.hom.val.app (op U) s).val *
        Scheme.Modules.RationalFunctions.rationalValue X.left U (b.hom.val.app (op U) t).val := by
  let z := (DivisorClass.divisorTensorIso X.left
    (curveProperties_dimension Scheme.smoothFieldDimension hX).le D E).hom.val.app (op U)
      ((tensorSheafIso X.left a b).hom.val.app (op U) (moduleTensorSection X.left M N U s t))
  change Scheme.Modules.RationalFunctions.rationalValue X.left U
    ((eqToIso (congrArg (DivisorClass.divisorSheaf X.left) h)).hom.val.app (op U) z).val = _
  exact (divisor_cast_value X h U z).trans (divisor_tensor_iso_value X hX D E a b U s t)

omit [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : Scheme.ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)] in
private theorem single_one_add_nat (x : Scheme.ClosedPoint X.left) (n : ℕ) :
    Finsupp.single x 1 + Finsupp.single x (n : ℤ) =
      Finsupp.single x ((n + 1 : ℕ) : ℤ) := by
  rw [← Finsupp.single_add]
  congr 1
  omega

private theorem tensorPowerPointDivisorIso_add_two (L : LineBundle X.left)
    (x : Scheme.ClosedPoint X.left)
    (e : L.val ≅ DivisorClass.divisorSheaf X.left (Finsupp.single x 1)) (n : ℕ) :
    tensorPowerPointDivisorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e (n + 2) =
      tensorSheafIso X.left e (tensorPowerPointDivisorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e (n + 1)) ≪≫
      DivisorClass.divisorTensorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le
        (Finsupp.single x 1) (Finsupp.single x ((n + 1 : ℕ) : ℤ)) ≪≫
      eqToIso (congrArg (DivisorClass.divisorSheaf X.left)
        (single_one_add_nat X x (n + 1))) := rfl

/-- Native unit and associator comparison of actual tensor powers. -/
def tensorPowerAddIso (Y : Scheme.{u}) (L : LineBundle Y) :
    (m n : ℕ) → tensorSheaf Y (tensorPowerLineBundle Y L m).val
        (tensorPowerLineBundle Y L n).val ≅ (tensorPowerLineBundle Y L (m + n)).val
  | 0, n => tensorSheafIso Y
      (Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)) (Iso.refl _) ≪≫
      tensorSheafLeftUnit Y (tensorPowerLineBundle Y L n).val ≪≫
      eqToIso (congrArg (fun r ↦ (tensorPowerLineBundle Y L r).val) (Nat.zero_add n).symm)
  | m + 1, n => tensorSheafAssociator Y L.val (tensorPowerLineBundle Y L m).val
        (tensorPowerLineBundle Y L n).val ≪≫
      tensorSheafIso Y (Iso.refl _) (tensorPowerAddIso Y L m n) ≪≫
      eqToIso (congrArg (fun r ↦ (tensorPowerLineBundle Y L r).val) (Nat.succ_add m n).symm)

private theorem tensorPowerAddIso_zero_section (Y : Scheme.{u}) (L : LineBundle Y)
    (n : ℕ) (U : Y.Opens) (s : Γ((tensorPowerLineBundle Y L 0).val, U))
    (t : Γ((tensorPowerLineBundle Y L n).val, U)) :
    (tensorPowerAddIso Y L 0 n).hom.val.app (op U)
        (moduleTensorSection Y _ _ U s t) =
      (eqToIso (congrArg (fun r ↦ (tensorPowerLineBundle Y L r).val)
        (Nat.zero_add n).symm)).hom.val.app (op U)
          ((show Γ(Y, U) from (Limits.coproductUniqueIso
            (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)).hom.val.app
              (op U) s) • t) := by
  let c₀ := Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit Y.ringCatSheaf)
  change (eqToIso (congrArg (fun r ↦ (tensorPowerLineBundle Y L r).val)
    (Nat.zero_add n).symm)).hom.val.app (op U)
      ((tensorSheafLeftUnit Y (tensorPowerLineBundle Y L n).val).hom.val.app (op U)
        ((tensorSheafIso Y c₀ (Iso.refl _)).hom.val.app (op U)
          (moduleTensorSection Y _ _ U s t))) = _
  refine congrArg (fun z ↦ (eqToIso (congrArg
    (fun r ↦ (tensorPowerLineBundle Y L r).val) (Nat.zero_add n).symm)).hom.val.app
      (op U) z) ?_
  have ht := tensor_iso_section Y c₀ (Iso.refl (tensorPowerLineBundle Y L n).val) U s t
  exact (congrArg (fun z ↦
    (tensorSheafLeftUnit Y (tensorPowerLineBundle Y L n).val).hom.val.app (op U) z) ht).trans
      (tensorLeftUnitIso_hom_section Y (tensorPowerLineBundle Y L n).val U
        (c₀.hom.val.app (op U) s) t)

private theorem tensorPowerAddIso_succ_section (Y : Scheme.{u}) (L : LineBundle Y)
    (m n : ℕ) (U : Y.Opens) (a : Γ(L.val, U))
    (b : Γ((tensorPowerLineBundle Y L m).val, U))
    (d : Γ((tensorPowerLineBundle Y L n).val, U)) :
    (tensorPowerAddIso Y L (m + 1) n).hom.val.app (op U)
        (moduleTensorSection Y _ _ U (moduleTensorSection Y _ _ U a b) d) =
      (eqToIso (congrArg (fun r ↦ (tensorPowerLineBundle Y L r).val)
        (Nat.succ_add m n).symm)).hom.val.app (op U)
          (moduleTensorSection Y _ _ U a
            ((tensorPowerAddIso Y L m n).hom.val.app (op U)
              (moduleTensorSection Y _ _ U b d))) := by
  change (eqToIso (congrArg (fun r ↦ (tensorPowerLineBundle Y L r).val)
    (Nat.succ_add m n).symm)).hom.val.app (op U)
      ((tensorSheafIso Y (Iso.refl _) (tensorPowerAddIso Y L m n)).hom.val.app (op U)
        ((tensorSheafAssociator Y L.val (tensorPowerLineBundle Y L m).val
          (tensorPowerLineBundle Y L n).val).hom.val.app (op U)
            (moduleTensorSection Y _ _ U (moduleTensorSection Y _ _ U a b) d))) = _
  refine congrArg (fun z ↦ (eqToIso (congrArg
    (fun r ↦ (tensorPowerLineBundle Y L r).val) (Nat.succ_add m n).symm)).hom.val.app
      (op U) z) ?_
  have ha := associator_hom_moduleTensorSection L.val (tensorPowerLineBundle Y L m).val
    (tensorPowerLineBundle Y L n).val U a b d
  have ht := tensor_iso_section Y (Iso.refl L.val) (tensorPowerAddIso Y L m n) U a
    (moduleTensorSection Y _ _ U b d)
  exact (congrArg (fun z ↦
    (tensorSheafIso Y (Iso.refl _) (tensorPowerAddIso Y L m n)).hom.val.app (op U) z) ha).trans ht

private def powerPointValue (L : LineBundle X.left) (x : Scheme.ClosedPoint X.left)
    (e : L.val ≅ DivisorClass.divisorSheaf X.left (Finsupp.single x 1))
    (n : ℕ) (U : X.left.Opens) [Nonempty U] :
    Γ((tensorPowerLineBundle X.left L n).val, U) →ₗ[Γ(X.left, U)] X.left.functionField where
  toFun s := Scheme.Modules.RationalFunctions.rationalValue X.left U
    ((tensorPowerPointDivisorIso X.left
      (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e n).hom.val.app
        (op U) s).val
  map_add' s t := by rw [map_add]; exact map_add _ _ _
  map_smul' a s := by
    rw [((tensorPowerPointDivisorIso X.left
      (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e n).hom.val.app
        (op U)).hom.map_smul a s]
    exact (Scheme.Modules.RationalFunctions.rationalValue X.left U).map_smul a _

private theorem powerPointValue_zero (L : LineBundle X.left) (x : Scheme.ClosedPoint X.left)
    (e : L.val ≅ DivisorClass.divisorSheaf X.left (Finsupp.single x 1))
    (U : X.left.Opens) [Nonempty U] (s : Γ((tensorPowerLineBundle X.left L 0).val, U)) :
    powerPointValue X hX L x e 0 U s = X.left.germToFunctionField U
      ((Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.left.ringCatSheaf)).hom.val.app
          (op U) s) := by
  exact (DivisorClass.sectionTrivialization_value X.left
    (curveProperties_dimension Scheme.smoothFieldDimension hX).le
    (Finsupp.single x 0) U 1 _ _).trans (one_mul _)

private theorem powerPointValue_eqToIso (L : LineBundle X.left) (x : Scheme.ClosedPoint X.left)
    (e : L.val ≅ DivisorClass.divisorSheaf X.left (Finsupp.single x 1))
    {m n : ℕ} (h : m = n) (U : X.left.Opens) [Nonempty U]
    (s : Γ((tensorPowerLineBundle X.left L m).val, U)) :
    powerPointValue X hX L x e n U
      ((eqToIso (congrArg (fun r ↦ (tensorPowerLineBundle X.left L r).val) h)).hom.val.app
        (op U) s) = powerPointValue X hX L x e m U s := by
  cases h
  rfl

private theorem powerPointValue_succ_tensorSection (L : LineBundle X.left)
    (x : Scheme.ClosedPoint X.left)
    (e : L.val ≅ DivisorClass.divisorSheaf X.left (Finsupp.single x 1))
    (n : ℕ) (U : X.left.Opens) [Nonempty U] (s : Γ(L.val, U))
    (t : Γ((tensorPowerLineBundle X.left L n).val, U)) :
    powerPointValue X hX L x e (n + 1) U (moduleTensorSection X.left _ _ U s t) =
      Scheme.Modules.RationalFunctions.rationalValue X.left U (e.hom.val.app (op U) s).val *
        powerPointValue X hX L x e n U t := by
  cases n with
  | zero =>
    let c₀ := Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.left.ringCatSheaf)
    change Scheme.Modules.RationalFunctions.rationalValue X.left U
      (e.hom.val.app (op U) ((firstTensorPowerIso X.left L).hom.val.app (op U)
        (moduleTensorSection X.left _ _ U s t))).val = _
    calc
      _ = Scheme.Modules.RationalFunctions.rationalValue X.left U
          (e.hom.val.app (op U) ((show Γ(X.left, U) from c₀.hom.val.app (op U) t) • s)).val :=
        congrArg (fun z ↦ Scheme.Modules.RationalFunctions.rationalValue X.left U
          (e.hom.val.app (op U) z).val)
            (firstTensorPowerIso_tensorSection X.left L U s t)
      _ = X.left.germToFunctionField U (c₀.hom.val.app (op U) t) *
          Scheme.Modules.RationalFunctions.rationalValue X.left U
            (e.hom.val.app (op U) s).val := by
        rw [(e.hom.val.app (op U)).hom.map_smul]
        exact (Scheme.Modules.RationalFunctions.rationalValue X.left U).map_smul _ _
      _ = _ := by
        rw [powerPointValue_zero X hX L x e U t]
        exact mul_comm _ _
  | succ n =>
    let Eₙ : (tensorPowerLineBundle X.left L (n + 1)).val ≅
        DivisorClass.divisorSheaf X.left (Finsupp.single x ((n + 1 : ℕ) : ℤ)) :=
      tensorPowerPointDivisorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e (n + 1)
    have h := congrArg (fun q ↦ Scheme.Modules.RationalFunctions.rationalValue X.left U
      (q.hom.val.app (op U) (moduleTensorSection X.left _ _ U s t)).val)
        (tensorPowerPointDivisorIso_add_two X hX L x e n)
    exact h.trans (divisor_tensor_cast_iso_value X hX (Finsupp.single x 1)
      (Finsupp.single x ((n + 1 : ℕ) : ℤ)) (Finsupp.single x ((n + 2 : ℕ) : ℤ))
      (single_one_add_nat X x (n + 1)) e Eₙ U s t)

omit [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : Scheme.ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)] in
private theorem single_cast_add (x : Scheme.ClosedPoint X.left) (m n : ℕ) :
    Finsupp.single x (m : ℤ) + Finsupp.single x (n : ℤ) =
      Finsupp.single x ((m + n : ℕ) : ℤ) := by
  rw [← Finsupp.single_add, Nat.cast_add]

private def powerPointTensorMap (L : LineBundle X.left) (x : Scheme.ClosedPoint X.left)
    (e : L.val ≅ DivisorClass.divisorSheaf X.left (Finsupp.single x 1)) (m n : ℕ) :
    tensorSheaf X.left (tensorPowerLineBundle X.left L m).val
        (tensorPowerLineBundle X.left L n).val ⟶
      DivisorClass.divisorSheaf X.left (Finsupp.single x ((m + n : ℕ) : ℤ)) :=
  tensorSheafMap X.left
      (tensorPowerPointDivisorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e m).hom
      (tensorPowerPointDivisorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e n).hom ≫
    (DivisorClass.divisorTensorIso X.left
      (curveProperties_dimension Scheme.smoothFieldDimension hX).le
      (Finsupp.single x (m : ℤ)) (Finsupp.single x (n : ℤ))).hom ≫
    (eqToIso (congrArg (DivisorClass.divisorSheaf X.left) (single_cast_add X x m n))).hom

private theorem powerPointTensorMap_value (L : LineBundle X.left) (x : Scheme.ClosedPoint X.left)
    (e : L.val ≅ DivisorClass.divisorSheaf X.left (Finsupp.single x 1))
    (m n : ℕ) (U : X.left.Opens) [Nonempty U]
    (s : Γ((tensorPowerLineBundle X.left L m).val, U))
    (t : Γ((tensorPowerLineBundle X.left L n).val, U)) :
    Scheme.Modules.RationalFunctions.rationalValue X.left U
      ((powerPointTensorMap X hX L x e m n).val.app (op U)
        (moduleTensorSection X.left _ _ U s t)).val =
      powerPointValue X hX L x e m U s * powerPointValue X hX L x e n U t := by
  let Eₘ := tensorPowerPointDivisorIso X.left
    (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e m
  let Eₙ := tensorPowerPointDivisorIso X.left
    (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e n
  let z := (DivisorClass.divisorTensorIso X.left
    (curveProperties_dimension Scheme.smoothFieldDimension hX).le
    (Finsupp.single x (m : ℤ)) (Finsupp.single x (n : ℤ))).hom.val.app (op U)
      ((tensorSheafIso X.left Eₘ Eₙ).hom.val.app (op U)
        (moduleTensorSection X.left _ _ U s t))
  change Scheme.Modules.RationalFunctions.rationalValue X.left U
    ((eqToIso (congrArg (DivisorClass.divisorSheaf X.left)
      (single_cast_add X x m n))).hom.val.app (op U) z).val = _
  exact (divisor_cast_value X (single_cast_add X x m n) U z).trans
    (divisor_tensor_iso_value X hX (Finsupp.single x (m : ℤ))
      (Finsupp.single x (n : ℤ)) Eₘ Eₙ U s t)

private theorem divisorSection_ext_values (D : Divisor X.left) (U : X.left.Opens)
    (s t : (DivisorClass.divisorSheaf X.left D).val.obj (op U))
    (h : ∀ hU : Nonempty U, let := hU
      Scheme.Modules.RationalFunctions.rationalValue X.left U s.val =
        Scheme.Modules.RationalFunctions.rationalValue X.left U t.val) : s = t := by
  by_cases hU : Nonempty U
  · let := hU
    apply Subtype.ext
    exact (Scheme.Modules.RationalFunctions.rationalValueEquiv X.left U).injective (h hU)
  · have hbot : U = ⊥ := by
      ext y
      constructor
      · intro hy
        exact (hU ⟨⟨y, hy⟩⟩).elim
      · simp
    subst U
    let := DivisorClass.divisorSheaf_empty_subsingleton X.left D
    exact Subsingleton.elim _ _

private theorem tensorPowerAddIso_comp_pointIso (L : LineBundle X.left)
    (x : Scheme.ClosedPoint X.left)
    (e : L.val ≅ DivisorClass.divisorSheaf X.left (Finsupp.single x 1)) (m n : ℕ) :
    (tensorPowerAddIso X.left L m n).hom ≫
      (tensorPowerPointDivisorIso X.left
        (curveProperties_dimension Scheme.smoothFieldDimension hX).le L x e (m + n)).hom =
      powerPointTensorMap X hX L x e m n := by
  induction m with
  | zero =>
    apply moduleTensor_hom_ext
    intro U s t
    apply divisorSection_ext_values X (Finsupp.single x ((0 + n : ℕ) : ℤ)) U
    intro hU
    let := hU
    let c₀ := Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.left.ringCatSheaf)
    let a : Γ(X.left, U) := c₀.hom.val.app (op U) s
    calc
      _ = powerPointValue X hX L x e (0 + n) U
          ((eqToIso (congrArg (fun r ↦ (tensorPowerLineBundle X.left L r).val)
            (Nat.zero_add n).symm)).hom.val.app (op U) (a • t)) :=
        congrArg (powerPointValue X hX L x e (0 + n) U)
          (tensorPowerAddIso_zero_section X.left L n U s t)
      _ = powerPointValue X hX L x e n U (a • t) :=
        powerPointValue_eqToIso X hX L x e (Nat.zero_add n).symm U (a • t)
      _ = a • powerPointValue X hX L x e n U t :=
        (powerPointValue X hX L x e n U).map_smul a t
      _ = powerPointValue X hX L x e 0 U s * powerPointValue X hX L x e n U t := by
        rw [powerPointValue_zero X hX L x e U s]
        rfl
      _ = _ := (powerPointTensorMap_value X hX L x e 0 n U s t).symm
  | succ m ih =>
    apply moduleTensor_nested_hom_ext_left L.val (tensorPowerLineBundle X.left L m).val
      (tensorPowerLineBundle X.left L n).val
    intro U a b d
    apply divisorSection_ext_values X (Finsupp.single x (((m + 1) + n : ℕ) : ℤ)) U
    intro hU
    let := hU
    have hinner := congrArg
      (fun f ↦ f.val.app (op U) (moduleTensorSection X.left _ _ U b d)) ih
    have hv := congrArg
      (fun z ↦ Scheme.Modules.RationalFunctions.rationalValue X.left U z.val) hinner
    change powerPointValue X hX L x e (m + n) U
      ((tensorPowerAddIso X.left L m n).hom.val.app (op U)
        (moduleTensorSection X.left _ _ U b d)) = _ at hv
    have hinnerValue : powerPointValue X hX L x e (m + n) U
        ((tensorPowerAddIso X.left L m n).hom.val.app (op U)
          (moduleTensorSection X.left _ _ U b d)) =
        powerPointValue X hX L x e m U b * powerPointValue X hX L x e n U d :=
      hv.trans (powerPointTensorMap_value X hX L x e m n U b d)
    calc
      _ = powerPointValue X hX L x e ((m + 1) + n) U
          ((eqToIso (congrArg (fun r ↦ (tensorPowerLineBundle X.left L r).val)
            (Nat.succ_add m n).symm)).hom.val.app (op U)
              (moduleTensorSection X.left _ _ U a
                ((tensorPowerAddIso X.left L m n).hom.val.app (op U)
                  (moduleTensorSection X.left _ _ U b d)))) :=
        congrArg (powerPointValue X hX L x e ((m + 1) + n) U)
          (tensorPowerAddIso_succ_section X.left L m n U a b d)
      _ = powerPointValue X hX L x e (m + n + 1) U
          (moduleTensorSection X.left _ _ U a
            ((tensorPowerAddIso X.left L m n).hom.val.app (op U)
              (moduleTensorSection X.left _ _ U b d))) :=
        powerPointValue_eqToIso X hX L x e (Nat.succ_add m n).symm U _
      _ = Scheme.Modules.RationalFunctions.rationalValue X.left U
          (e.hom.val.app (op U) a).val *
          powerPointValue X hX L x e (m + n) U
            ((tensorPowerAddIso X.left L m n).hom.val.app (op U)
              (moduleTensorSection X.left _ _ U b d)) :=
        powerPointValue_succ_tensorSection X hX L x e (m + n) U a _
      _ = Scheme.Modules.RationalFunctions.rationalValue X.left U
          (e.hom.val.app (op U) a).val *
          (powerPointValue X hX L x e m U b * powerPointValue X hX L x e n U d) :=
        congrArg (fun z ↦ Scheme.Modules.RationalFunctions.rationalValue X.left U
          (e.hom.val.app (op U) a).val * z) hinnerValue
      _ = (Scheme.Modules.RationalFunctions.rationalValue X.left U
          (e.hom.val.app (op U) a).val * powerPointValue X hX L x e m U b) *
          powerPointValue X hX L x e n U d := (mul_assoc _ _ _).symm
      _ = powerPointValue X hX L x e (m + 1) U (moduleTensorSection X.left _ _ U a b) *
          powerPointValue X hX L x e n U d :=
        congrArg (fun z ↦ z * powerPointValue X hX L x e n U d)
          (powerPointValue_succ_tensorSection X hX L x e m U a b).symm
      _ = _ := (powerPointTensorMap_value X hX L x e (m + 1) n U
        (moduleTensorSection X.left _ _ U a b) d).symm

/-- The native unit and associator product on the original pole powers. -/
def poleTensorAddIso (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (m n : ℕ) : tensorSheaf X.left (poleLineBundle X hX p hp m).val
        (poleLineBundle X hX p hp n).val ≅ (poleLineBundle X hX p hp (m + n)).val :=
  tensorPowerAddIso X.left (positiveLineBundle X hX p hp) m n

/-- Actual original tensor multiplication becomes field multiplication. -/
theorem sectionsToFunctionField_tensor
    (p : Spec (.of k) ⟶ X.left) (hp : p ≫ X.hom = 𝟙 _)
    (hg : coherentGenus k X = 1) (m n : ℕ)
    (s : sections X hX p hp m) (t : sections X hX p hp n) :
    sectionsToFunctionField X hX p hp hg (m + n)
      ((poleTensorAddIso X hX p hp m n).hom.val.app (op ⊤)
        (moduleTensorSection X.left _ _ ⊤ s t)) =
      sectionsToFunctionField X hX p hp hg m s *
        sectionsToFunctionField X hX p hp hg n t := by
  have h := congrArg
    (fun f ↦ f.val.app (op ⊤) (moduleTensorSection X.left _ _ ⊤ s t))
    (tensorPowerAddIso_comp_pointIso X hX (positiveLineBundle X hX p hp)
      (closedPoint X p hp) (positiveDivisorIso X hX p hp hg) m n)
  have hv := congrArg
    (fun z ↦ Scheme.Modules.RationalFunctions.rationalValue X.left ⊤ z.val) h
  change _ = powerPointValue X hX (positiveLineBundle X hX p hp)
    (closedPoint X p hp) (positiveDivisorIso X hX p hp hg) m ⊤ s *
    powerPointValue X hX (positiveLineBundle X hX p hp)
      (closedPoint X p hp) (positiveDivisorIso X hX p hp hg) n ⊤ t
  exact hv.trans (powerPointTensorMap_value X hX (positiveLineBundle X hX p hp)
    (closedPoint X p hp) (positiveDivisorIso X hX p hp hg) m n ⊤ s t)

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
