/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Aglib.AlgebraicGeometry.Morphisms.Etale.NormalCurveInertia

/-!
# Clients of normal-curve inertia and literal local normalization

The clients use actual normalization maps, the literal stalk integral closure,
and every inertia element and geometric point. The target has arbitrary
characteristic and arbitrary residue fields; the original cover may be empty or split.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.LocalComparison

universe u

section StalkComparison

variable (X : Scheme.{u}) [IsIntegral X]
  (C : Scheme.FiniteEtale (Spec X.functionField))
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (y : U)

example :
    IsPullback (localToNormalization X C U hU y)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk y)
        (integralClosure (X.presheaf.stalk y)
          (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U))))))
      (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
      (X.fromSpecStalk y) :=
  localNormalization_isPullback X C U hU y

example :
    (localFiberIso X C U hU y).hom ≫
      pullback.snd (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
        (X.fromSpecStalk y) =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk y)
        (integralClosure (X.presheaf.stalk y)
          (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U))))) :=
  (localNormalization_isPullback X C U hU y).isoPullback_hom_snd

end StalkComparison

example (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1)
    (C : Scheme.FiniteEtale (Spec X.functionField))
    (Q : ∀ x : CodimensionOnePoint X,
      Ideal (integralClosure x.localRing (AlgebraicClosure X.functionField)))
    [∀ x, (Q x).IsPrime] [∀ x, (Q x).LiesOver (IsLocalRing.maximalIdeal x.localRing)]
    (hfixed : ∀ (x : CodimensionOnePoint X)
      (γ : (Q x).inertia (AlgebraicClosure X.functionField ≃ₐ[X.functionField] AlgebraicClosure
          X.functionField))
      (t : Fiber (geometricPoint X.functionField) C),
      pointEnd X.functionField γ.val ≫ t = t) :
    Etale (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization :=
  normalCurveCoverPurity.etale X hdim C Q hfixed
