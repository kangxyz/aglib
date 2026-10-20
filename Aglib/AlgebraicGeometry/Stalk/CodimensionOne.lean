/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# Actual codimension-one local rings of integral stalk-normal schemes

Source: `R5Lab.Aglib.AlgebraicGeometry.Stalk.CodimensionOne`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `7c4d89b447ffdf90267c8be33bdfcd7bcf22098ca6ff491049bee51dd4a56888`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Actual scheme points whose actual local ring has dimension one. -/
abbrev CodimensionOnePoint (X : Scheme.{u}) :=
  { x : X // ringKrullDim (X.presheaf.stalk x) = 1 }

namespace CodimensionOnePoint
variable {X : Scheme.{u}} (x : CodimensionOnePoint X)

/-- The actual structure-sheaf stalk of a codimension-one point. -/
abbrev localRing : CommRingCat := X.presheaf.stalk x.1
/-- The actual scheme residue field, with no supplied identification. -/
abbrev residueField : CommRingCat := X.residueField x.1

/-- The dimension-one condition is carried by the actual point index. -/
theorem dimension_localRing : ringKrullDim x.localRing = 1 := x.2

/-- A dimension-one stalk is not a field. -/
theorem localRing_not_isField : ¬ IsField x.localRing := by
  intro h
  have hzero := ringKrullDim_eq_zero_of_isField h
  rw [x.dimension_localRing] at hzero
  exact one_ne_zero hzero

/-- The canonical residue homomorphism of the actual stalk. -/
def residue : x.localRing →+* x.residueField := (X.residue x.1).hom

/-- Reduction on units of the actual stalk. -/
def residueUnits : x.localRingˣ →* x.residueFieldˣ :=
  Units.map x.residue.toMonoidHom

/-- The global-section germ at the actual codimension-one point. -/
def globalToLocalRing : Γ(X, ⊤) →+* x.localRing :=
  (X.presheaf.germ ⊤ x.1 (by trivial)).hom

/-- Global units map to units of the actual local ring. -/
def globalUnitsToLocalRing : Γ(X, ⊤)ˣ →* x.localRingˣ :=
  Units.map x.globalToLocalRing.toMonoidHom

section Integral
variable [IsIntegral X]

/-- The canonical stalk-specialization algebra map into the generic stalk. -/
def toFunctionField : x.localRing →+* X.functionField :=
  algebraMap x.localRing X.functionField

/-- The local-to-generic map is the actual presheaf stalk-specialization map. -/
theorem toFunctionField_eq_stalkSpecializes :
    x.toFunctionField =
      (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom := rfl

/-- The actual stalk injects into the actual function field. -/
theorem toFunctionField_injective : Function.Injective x.toFunctionField :=
  IsFractionRing.injective x.localRing X.functionField

/-- The generic stalk is a fraction field of the actual local ring. -/
theorem localRing_isFractionRing : IsFractionRing x.localRing X.functionField :=
  inferInstance

/-- Actual local-ring units embedded into function-field units. -/
def fieldUnits : x.localRingˣ →* X.functionFieldˣ :=
  Units.map x.toFunctionField.toMonoidHom

end Integral

section NormalNoetherian
variable [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)]

/-- Normality and local Noetherianity make the actual dimension-one stalk a DVR. -/
instance localRing_isDiscreteValuationRing : IsDiscreteValuationRing x.localRing := by
  let : Ring.KrullDimLE 1 x.localRing := Ring.krullDimLE_iff.mpr x.dimension_localRing.le
  have hprime : ∀ P : Ideal x.localRing, P ≠ ⊥ → P.IsPrime →
      P = IsLocalRing.maximalIdeal x.localRing := by
    intro P hP hprime
    exact IsLocalRing.eq_maximalIdeal (hprime.isMaximal_of_ne_bot hP)
  have hmax : IsLocalRing.maximalIdeal x.localRing ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp x.localRing_not_isField
  have hnormal : IsIntegrallyClosed x.localRing ∧
      ∃! P : Ideal x.localRing, P ≠ ⊥ ∧ P.IsPrime :=
    ⟨inferInstance, ⟨IsLocalRing.maximalIdeal x.localRing, ⟨hmax, inferInstance⟩,
      fun P hP => hprime P hP.1 hP.2⟩⟩
  exact ((IsDiscreteValuationRing.TFAE x.localRing x.localRing_not_isField).out 4 1).mp
    hnormal

end NormalNoetherian
end CodimensionOnePoint

variable (X : Scheme.{u}) [IsIntegral X]

/-- The global-section germ at the actual generic point. -/
def globalToFunctionField : Γ(X, ⊤) →+* X.functionField :=
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  (X.germToFunctionField ⊤).hom

/-- Global units mapped by their genuine germ at the generic point. -/
def globalUnitsToFunctionField : Γ(X, ⊤)ˣ →* X.functionFieldˣ :=
  Units.map (globalToFunctionField X).toMonoidHom

/-- The global germ through any indexed stalk is the global germ at the generic point. -/
@[simp] theorem toFunctionField_globalToLocalRing (x : CodimensionOnePoint X)
    (s : Γ(X, ⊤)) :
    x.toFunctionField (x.globalToLocalRing s) = globalToFunctionField X s := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact X.algebraMap_germ_eq_germToFunctionField (U := ⊤) (by trivial) s

/-- Ring-homomorphism form of the genuine global-to-local-to-generic compatibility. -/
theorem toFunctionField_comp_globalToLocalRing (x : CodimensionOnePoint X) :
    x.toFunctionField.comp x.globalToLocalRing = globalToFunctionField X := by
  ext s
  exact toFunctionField_globalToLocalRing X x s

/-- The same compatibility on genuine global units. -/
@[simp] theorem fieldUnits_globalUnitsToLocalRing (x : CodimensionOnePoint X)
    (s : Γ(X, ⊤)ˣ) :
    x.fieldUnits (x.globalUnitsToLocalRing s) = globalUnitsToFunctionField X s := by
  apply Units.ext
  exact toFunctionField_globalToLocalRing X x (s : Γ(X, ⊤))

/-- The generic point of an integral scheme is not in the dimension-one index. -/
theorem genericPoint_not_codimensionOne :
    ringKrullDim (X.presheaf.stalk (genericPoint X)) ≠ 1 := by
  change ringKrullDim X.functionField ≠ 1
  simp

end AlgebraicGeometry.Scheme
