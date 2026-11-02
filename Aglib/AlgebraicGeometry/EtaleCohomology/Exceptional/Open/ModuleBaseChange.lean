/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.EtaleBaseChange
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ValuedComparison

/-!
# Arbitrary base change of genuine constant-ring module extension by zero

The right-adjoint exchange is transported from the actual chart-pullback
isomorphism through the proved module equivalences. Its adjunction mate gives
the native lower-shriek comparison and retains the original composite unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

section Exchange

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]
  (Λ : Type (u + 1)) [Ring Λ]

/-- Native pullback after the actual inverse coefficient equivalence. -/
def moduleInverseImageValuedIso {A B : Scheme.{u}} (a : A ⟶ B) :
    moduleInverseImage a Λ ⋙ (moduleSheafEquivalence A Λ).inverse ≅
      (moduleSheafEquivalence B Λ).inverse ⋙ moduleValuedInverseImage a Λ :=
  ValuedComparison.inverseValuedIso (moduleSheafEquivalence B Λ)
    (moduleSheafEquivalence A Λ) (moduleInverseImageTransportIso a Λ)

/-- The left exchange composite after the actual inverse coefficient equivalence. -/
def moduleEtaleBaseChangeLeftIso :
    (moduleDirectImage f Λ ⋙ moduleInverseImage g Λ) ⋙
        (moduleSheafEquivalence T Λ).inverse ≅
      (moduleSheafEquivalence X Λ).inverse ⋙
        moduleValuedDirectImage f Λ ⋙ moduleValuedInverseImage g Λ :=
  scalarMateSourceIso (moduleDirectImageComparison f Λ) (moduleInverseImageValuedIso Λ g)

/-- The right exchange composite after the actual inverse coefficient equivalence. -/
def moduleEtaleBaseChangeRightIso :
    (moduleInverseImage (pullback.snd g f) Λ ⋙ moduleDirectImage (pullback.fst g f) Λ) ⋙
        (moduleSheafEquivalence T Λ).inverse ≅
      (moduleSheafEquivalence X Λ).inverse ⋙
        moduleValuedInverseImage (pullback.snd g f) Λ ⋙
          moduleValuedDirectImage (pullback.fst g f) Λ :=
  scalarMateTargetIso (moduleDirectImageComparison (pullback.fst g f) Λ)
    (moduleInverseImageValuedIso Λ (pullback.snd g f))

/-- The actual native right-adjoint exchange, before removing the faithful module equivalence. -/
def moduleEtaleBaseChangeValuedIso :
    (moduleDirectImage f Λ ⋙ moduleInverseImage g Λ) ⋙
        (moduleSheafEquivalence T Λ).inverse ≅
      (moduleInverseImage (pullback.snd g f) Λ ⋙ moduleDirectImage (pullback.fst g f) Λ) ⋙
        (moduleSheafEquivalence T Λ).inverse :=
  ValuedComparison.exchangeComparisonIso (moduleSheafEquivalence T Λ).inverse
    (moduleEtaleBaseChangeLeftIso f g Λ) (moduleEtaleBaseChangeRightIso f g Λ)
    (moduleValuedEtaleBaseChangeIso f g Λ)

/-- Native module inverse image commutes with direct image along an actual étale base change. -/
def moduleEtaleBaseChangeIso :
    moduleDirectImage f Λ ⋙ moduleInverseImage g Λ ≅
      moduleInverseImage (pullback.snd g f) Λ ⋙ moduleDirectImage (pullback.fst g f) Λ :=
  ValuedComparison.exchangeIso (moduleSheafEquivalence T Λ).inverse
    (moduleEtaleBaseChangeLeftIso f g Λ) (moduleEtaleBaseChangeRightIso f g Λ)
    (moduleValuedEtaleBaseChangeIso f g Λ)

end Exchange

variable {U X Y : Scheme.{u}} (j : U ⟶ X) [Etale j] (f : Y ⟶ X)
  (Λ : Type (u + 1)) [Ring Λ]

/-- Arbitrary base change of the genuine native module lower-shriek functor. -/
def moduleLowerShriekBaseChangeIso :
    moduleLowerShriek j Λ ⋙ moduleInverseImage f Λ ≅
      moduleInverseImage (pullback.fst j f) Λ ⋙ moduleLowerShriek (pullback.snd j f) Λ :=
  (((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ)).ofNatIsoRight
    (moduleEtaleBaseChangeIso f j Λ)).leftAdjointUniq
      ((moduleInverseImageAdjunction (pullback.fst j f) Λ).comp
        (moduleLowerShriekAdjunction (pullback.snd j f) Λ))

/-- Native lower-shriek base change satisfies the original hom-equivalence equation. -/
@[reassoc]
theorem moduleLowerShriekBaseChangeIso_homEquiv (M : ModuleSheaf U Λ) :
    ((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ)).homEquiv _ _
        ((moduleLowerShriekBaseChangeIso j f Λ).hom.app M) ≫
      (moduleEtaleBaseChangeIso f j Λ).hom.app
        ((moduleLowerShriek (pullback.snd j f) Λ).obj
          ((moduleInverseImage (pullback.fst j f) Λ).obj M)) =
    ((moduleInverseImageAdjunction (pullback.fst j f) Λ).comp
      (moduleLowerShriekAdjunction (pullback.snd j f) Λ)).unit.app M := by
  simpa only [Adjunction.homEquiv_ofNatIsoRight_apply, moduleLowerShriekBaseChangeIso,
    Functor.comp_obj] using
    Adjunction.homEquiv_leftAdjointUniq_hom_app
      (((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ)).ofNatIsoRight
        (moduleEtaleBaseChangeIso f j Λ))
      ((moduleInverseImageAdjunction (pullback.fst j f) Λ).comp
        (moduleLowerShriekAdjunction (pullback.snd j f) Λ)) M

/-- Equivalently, the base-change comparison is normalized by the actual composite unit. -/
@[reassoc]
theorem moduleLowerShriekBaseChangeIso_unit (M : ModuleSheaf U Λ) :
    ((moduleLowerShriekAdjunction j Λ).comp (moduleInverseImageAdjunction f Λ)).unit.app M ≫
      (moduleInverseImage j Λ).map ((moduleDirectImage f Λ).map
        ((moduleLowerShriekBaseChangeIso j f Λ).hom.app M)) ≫
      (moduleEtaleBaseChangeIso f j Λ).hom.app
        ((moduleLowerShriek (pullback.snd j f) Λ).obj
          ((moduleInverseImage (pullback.fst j f) Λ).obj M)) =
    ((moduleInverseImageAdjunction (pullback.fst j f) Λ).comp
      (moduleLowerShriekAdjunction (pullback.snd j f) Λ)).unit.app M := by
  simpa only [Adjunction.homEquiv_unit, Functor.comp_map, Category.assoc] using
    moduleLowerShriekBaseChangeIso_homEquiv j f Λ M

end AlgebraicGeometry.Scheme.EtaleCohomology
