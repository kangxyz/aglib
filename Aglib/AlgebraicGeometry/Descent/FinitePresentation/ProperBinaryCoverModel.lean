/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cover.AffineBinary.Limit
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ModelBaseFactor
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ProperSubalgebraModel
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeBaseChangeLimit

/-!
# Proper finite coefficient models carrying an actual affine binary cover

An original proper finitely presented scheme descends by native proper-model
descent. Its two affine opens and affine intersection descend after one later
finite coefficient stage. The original cartesian structural comparison is
retained; no projective-line morphism is part of the model data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit

open Algebra.FiniteTypeSubalgebraLimit Scheme.FinitePresentationDescent

universe u v

/-- A proper fp scheme with an affine binary cover has an actual proper
finite-type coefficient model with such a cover and its original cartesian square. -/
theorem exists_properModel_with_affineBinaryCover
    (D : Type v) [CommRing D] [IsNoetherianRing D]
    (R : Type u) [CommRing R] [Algebra D R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [LocallyOfFinitePresentation f]
    (A : Scheme.AffineBinaryCover X) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra D C) (_ : Algebra.FiniteType D C)
      (_ : Algebra C R) (M : Model (Spec.algebraMap C R) f),
      IsProper M.f ∧ Nonempty (Scheme.AffineBinaryCover M.X) := by
  obtain ⟨s, M₀, hM₀⟩ := exists_properModel_over_finiteTypeSubalgebra D R f
  let B := stage D R s
  let M : Model (Spec.algebraMap B R) f := M₀
  let : IsProper M.f := hM₀
  obtain ⟨t, E, _, _⟩ := Scheme.AffineBinaryCover.exists_model_of_isLimit
    (schemeDiagram B R M.f) (schemeCone B R M.f) (schemeConeIsLimit B R M.f)
    (A.pullback M.rawIso.inv)
  let C := stage B R t.unop
  let : Algebra D C := ((algebraMap B C).comp (algebraMap D B)).toAlgebra
  let : IsScalarTower D B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FiniteType D C := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType D B) (inferInstance : Algebra.FiniteType B C)
  let a := Spec.algebraMap C R
  let b := Spec.algebraMap B C
  let N := M.factorBase a b (baseStructure_fac B R t)
  let E' : Scheme.AffineBinaryCover N.X := E.pullback (pullbackSymmetry M.f b).hom
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, N, ?_, ⟨E'⟩⟩
  change IsProper (Limits.pullback.snd M.f b)
  infer_instance

end AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit
