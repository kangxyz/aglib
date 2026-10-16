/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Function fields under field base change

The embedding is the actual dominant base-change projection map on function
fields. The base-changed scheme is assumed integral exactly as in the source.

Source: `R5Lab/AlgebraicGeometry/Curves/Divisors/BaseChange.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`791a42eb94c20c97ad8e14585a6e4fd04a84004d44f28763e8b10299ea94a18c`. Selected original ranges: [[81,
106]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable {k l : Type u} [Field k] [Field l]

instance fieldExtensionSpecMap_surjective (a : k →+* l) :
    Surjective (Spec.map (CommRingCat.ofHom a)) where
  surj _x := ⟨IsLocalRing.closedPoint l, Subsingleton.elim _ _⟩

variable (p : Y ⟶ Spec (.of k)) (a : k →+* l)
variable [IsIntegral (pullback p (Spec.map (CommRingCat.ofHom a)))]

/-- Function-field extension from the actual base-change projection. -/
def functionFieldBaseChange : Y.functionField →+*
    (pullback p (Spec.map (CommRingCat.ofHom a))).functionField :=
  functionFieldMap (pullback.fst p (Spec.map (CommRingCat.ofHom a)))

/-- The algebra structure induced by the canonical function-field base-change map. -/
@[instance_reducible] def functionFieldBaseChangeAlgebra : Algebra Y.functionField
    (pullback p (Spec.map (CommRingCat.ofHom a))).functionField :=
  (functionFieldBaseChange p a).toAlgebra

theorem functionFieldBaseChange_constants :
    (functionFieldBaseChange p a).comp (functionFieldConstants Y p) =
    (functionFieldConstants _ (pullback.snd p (Spec.map (CommRingCat.ofHom a)))).comp a :=
  functionFieldMap_constants _ p _ a pullback.condition

theorem functionFieldBaseChange_genericPoint :
    ((pullback p (Spec.map (CommRingCat.ofHom a))).fromSpecStalk (genericPoint
      (pullback p (Spec.map (CommRingCat.ofHom a)) : Scheme.{u}))) ≫
      pullback.fst p (Spec.map (CommRingCat.ofHom a)) =
    Spec.map (CommRingCat.ofHom (functionFieldBaseChange p a)) ≫ (Y.fromSpecStalk (genericPoint
      Y)) :=
  fromSpecStalk_genericPoint_naturality _

end AlgebraicGeometry.Scheme
