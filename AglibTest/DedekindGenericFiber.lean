/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.DedekindGenericFiberIntegral
public import Aglib.AlgebraicGeometry.Stalk.GenericFiber.DVROpen

/-!
# Actual Dedekind-base generic-fibre maps and scalars

The client first uses projection dominance with no fibre-integrality instance.
It then obtains that instance from the separate producer and exercises the
canonical field map, literal structural arrow and constants equation. All fields,
schemes and original structural maps remain arbitrary in their stated universe.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Scheme.LocalRing.GenericFiber (baseMap scheme projection)
open Scheme.FunctionField.DedekindGenericFiber

universe u

section GenericLift

variable (A F : Type u) [CommRing A] [IsDedekindDomain A] [Field F]
  [Algebra A F] [IsFractionRing A F] {Y : Scheme.{u}} [IsIntegral Y]
  (p : Y ⟶ Spec (.of A)) [IsDominant p]

example : IsDominant (projection A F p) := inferInstance

example : genericLift A F p ≫ projection A F p =
    Y.fromSpecStalk (genericPoint Y) :=
  genericLift_projection A F p

example : genericLift A F p ≫ pullback.snd p (baseMap A F) =
    Spec.map (CommRingCat.ofHom (Scheme.DedekindBase.constantToFunctionField F p)) :=
  genericLift_structure A F p

example : IsIntegral (scheme A F p) := integral_genericFiber A F p

local instance : IsIntegral (scheme A F p) := integral_genericFiber A F p

example : (functionFieldRingEquiv A F p).toRingHom =
    Scheme.functionFieldMap (projection A F p) := by
  ext a
  exact functionFieldRingEquiv_apply A F p a

example : Spec.map (CommRingCat.ofHom (structuralConstants A F p)) =
    (scheme A F p).fromSpecStalk (genericPoint (scheme A F p)) ≫
      pullback.snd p (baseMap A F) := by
  change Spec.map (Spec.preimage _) = _
  exact Spec.map_preimage _

example : (functionFieldRingEquiv A F p).toRingHom.comp
    (Scheme.DedekindBase.constantToFunctionField F p) = structuralConstants A F p :=
  functionFieldRingEquiv_constants A F p

example (a : F) :
    (functionFieldRingEquiv A F p).symm (structuralConstants A F p a) =
      Scheme.DedekindBase.constantToFunctionField F p a :=
  functionFieldRingEquiv_symm_constants_apply A F p a

example : (scheme A F p).fromSpecStalk (genericPoint (scheme A F p)) ≫ projection A F p =
    Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap (projection A F p))) ≫
      Y.fromSpecStalk (genericPoint Y) :=
  projection_generic_triangle A F p

end GenericLift

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] [IsDominant f] [IrreducibleSpace Y] : IrreducibleSpace X :=
  irreducible_of_dominant_preimmersion f

example (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] : IsOpenImmersion (baseMap R F) :=
  Scheme.LocalRing.GenericFiber.baseMap_isOpenImmersion
