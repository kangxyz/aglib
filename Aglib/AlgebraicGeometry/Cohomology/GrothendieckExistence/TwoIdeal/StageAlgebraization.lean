/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.ReconstructionStages
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCandidateIso
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedDefects

/-! # Actual algebraization of original stages from a concrete bounded triple

Bounded-candidate uniqueness is applied to two genuine triples over the same
original map. The second is the original formal coefficient itself, with
identity completion comparison. No faithfulness of K-completion is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (K : X.IdealSheafData)
  (h : ClosedThickeningCompletionEssSurj f I K)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) {G H : X.CoherentSheaf}
local notation "J" => idealThickeningIdealSheaf f I
local notation "C" => completionFunctor X K
variable (φ : F ⟶ (completionFunctor X (idealThickeningIdealSheaf f I)).obj H) (t : ℕ)
  (hφ : AdicSystem.DefectsKilled K t φ) (a : G ⟶ H)
  (β : (completionFunctor X K).obj G ≅ twoIdealCoefficientSystem I f K h F)
  (hβ : β.hom ≫ twoIdealCoefficientMap I f K h F φ = (completionFunctor X K).map a)
  (s : ℕ) (hk : killedByIdealSheaf (K ^ s) (kernel a.hom))
  (hc : killedByIdealSheaf (K ^ s) (cokernel a.hom))

/-- Each original stage is recovered with both its original target and
specified K-completion comparison, by actual bounded-candidate uniqueness. -/
def twoIdealStageAlgebraizationComparison (n : ℕ) :
    {e : idealSheafCoherentQuotient X (J ^ n) G ≅ originalStageCoherent I f F n //
      e.hom ≫ originalStageCoherentMap I f F φ n =
        idealSheafCoherentQuotientHom X (J ^ n) a ∧ ∀ m : ℕ,
      e.hom.hom ≫ (idealSheafQuotientUnit X (K ^ m)).app
          (originalStageCoherent I f F n).obj ≫
        (Iso.refl ((C).obj (originalStageCoherent I f F n))).hom.hom.app (op m) =
      (idealSheafQuotientUnit X (K ^ m)).app
          (idealSheafCoherentQuotient X (J ^ n) G).obj ≫
        (twoIdealReconstructionStageIso I f K h F β n).hom.hom.app (op m)} :=
  boundedCandidateIsoComparison
    ((C).map (originalStageCoherentMap I f F φ n))
    (idealSheafCoherentQuotientHom X (J ^ n) a)
    (twoIdealReconstructionStageIso I f K h F β n)
    (twoIdealReconstructionStageIso_map I f K h F φ a β hβ n)
    (s * 2) (twoIdealReconstructionStageMap_bounds I f K a s n hk hc).1
    (twoIdealReconstructionStageMap_bounds I f K a s n hk hc).2
    (originalStageCoherentMap I f F φ n) (Iso.refl _) (by simp)
    t (hφ n).1 (hφ n).2

/-- The actual original I-stage algebraization, not merely an equivalence
between its K-completions. -/
def twoIdealStageAlgebraizationIso (n : ℕ) :
    idealSheafCoherentQuotient X (J ^ n) G ≅ originalStageCoherent I f F n :=
  (twoIdealStageAlgebraizationComparison I f K h F φ t hφ a β hβ s hk hc n).val

/-- The recovered coefficient isomorphism preserves the original map to H/I^n. -/
theorem twoIdealStageAlgebraizationIso_map (n : ℕ) :
    (twoIdealStageAlgebraizationIso I f K h F φ t hφ a β hβ s hk hc n).hom ≫
        originalStageCoherentMap I f F φ n =
      idealSheafCoherentQuotientHom X (J ^ n) a :=
  (twoIdealStageAlgebraizationComparison I f K h F φ t hφ a β hβ s hk hc n).property.1

/-- The recovered isomorphism retains the specified completed comparison.
Only cancellation of the original epimorphic quotient unit is used. -/
theorem twoIdealStageAlgebraizationIso_completion (n : ℕ) :
    (C).map (twoIdealStageAlgebraizationIso I f K h F φ t hφ a β hβ s hk hc n).hom =
      (twoIdealReconstructionStageIso I f K h F β n).hom := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  apply (cancel_epi ((idealSheafQuotientUnit X (K ^ m.unop)).app
    (idealSheafCoherentQuotient X (J ^ n) G).obj)).mp
  change (idealSheafQuotientUnit X (K ^ m.unop)).app _ ≫
      (idealSheafQuotientFunctor X (K ^ m.unop)).map
        (twoIdealStageAlgebraizationIso I f K h F φ t hφ a β hβ s hk hc n).hom.hom = _
  rw [← (idealSheafQuotientUnit X (K ^ m.unop)).naturality]
  have hs :=
    (twoIdealStageAlgebraizationComparison I f K h F φ t hφ a β hβ s hk hc n).property.2
      m.unop
  change (twoIdealStageAlgebraizationIso I f K h F φ t hφ a β hβ s hk hc n).hom.hom ≫
      (idealSheafQuotientUnit X (K ^ m.unop)).app
        (originalStageCoherent I f F n).obj ≫
      𝟙 ((idealSheafQuotientFunctor X (K ^ m.unop)).obj
        (originalStageCoherent I f F n).obj) = _ at hs
  simpa only [Category.comp_id, Functor.id_map] using hs

end AlgebraicGeometry.Scheme.Cohomology
