/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperGeometricLocal
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.LocalHenselization
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitLifting
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ResidueStageComparison
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ResidueBaseChangeProperties

/-!
# Henselian base change of a proper arithmetic model

A proper model over a finite-type algebra over a characteristic-zero DVR
has the finite-etale closed-fibre lifting property after any henselian local
base change. Each prescribed cover descends through its actual residue-field
limit to one selected geometric local henselization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u v

open Algebra.FiniteTypeSubalgebraLimit LocalRing.AtLocalTarget

variable (D : Type v) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [CharZero D]
  (B R : Type u) [CommRing B] [CommRing R] [Algebra D B] [Algebra.FiniteType D B]
  [Algebra B R] [HenselianLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [IsProper f]

include D

/-- Every prescribed original closed-fibre cover lifts after henselian local
base change of a proper finite-type arithmetic model. No approximation or
cover-descent premise remains in this statement. -/
theorem properGeometricBaseChange_essSurj :
    (baseChange (pullback.fst (pullback.snd f (Spec.algebraMap B R))
      (LocalRing.residueSpecMap R))).EssSurj := by
  apply LimitDescent.baseChange_essSurj_of_stage_lifts
    (FiniteTypeResidueLimit.schemeDiagram B R (IsLocalRing.maximalIdeal R) f)
    (FiniteTypeResidueLimit.schemeCone B R (IsLocalRing.maximalIdeal R) f)
    (FiniteTypeResidueLimit.schemeConeIsLimit B R (IsLocalRing.maximalIdeal R) f)
    (pullback.fst (pullback.snd f (Spec.algebraMap B R)) (LocalRing.residueSpecMap R))
    (FiniteTypeResidueLimit.localClosedFiberIso B R f)
  intro s C
  let S := stage B R s.unop
  let a : S →+* R := (stage B R s.unop).val.toRingHom
  let b : B →+* S := algebraMap B S
  let : Algebra D S := (b.comp (algebraMap D B)).toAlgebra
  let : IsScalarTower D B S := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FiniteType D S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType D B) (inferInstance : Algebra.FiniteType B S)
  let q := Localization.AtLocalTarget.prime a
  let g := pullback.snd f (henselizationSpecMap a b)
  let : IsProper g := inferInstanceAs (IsProper (pullback.snd f (henselizationSpecMap a b)))
  let : (baseChange (pullback.fst g
      (LocalRing.residueSpecMap (Henselization.AtLocalTarget.Ring a)))).EssSurj :=
    properGeometricLocal_baseChange_essSurj_of_charZeroDVR D S q g
  let e : primeFiber a b f ≅
      (FiniteTypeResidueLimit.schemeDiagram B R (IsLocalRing.maximalIdeal R) f).obj s :=
    pullbackSymmetry f (Spec.algebraMap B q.ResidueField)
  obtain ⟨W, ⟨hW⟩⟩ := exists_cover_of_selected_henselization a b f
    ((baseChange e.hom).obj C)
  refine ⟨W, ⟨hW ≪≫ (baseChangeComp e.hom (targetPrimeFiberMap a b f)).symm.app C ≪≫ ?_⟩⟩
  exact (eqToIso (congrArg baseChange
    (FiniteTypeResidueLimit.targetPrimeFiberMap_eq_projection B R f s.unop))).app C

end AlgebraicGeometry.Scheme.FiniteEtale
