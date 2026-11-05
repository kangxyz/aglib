/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleInverseImageFaithful
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CohomologyPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SurjectivePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Size
public import Aglib.CategoryTheory.Sites.SheafCohomology.Retract
public import Aglib.CategoryTheory.Adjunction.InjectiveTests
public import Aglib.Logic.Function.TransportThree
public import Aglib.CategoryTheory.Sites.SheafCohomology.NaturalIsoFunction

/-! # Genuine injective coefficient replacement and original finite class transport

For every surjective coefficient-base map, construct an actual injective
constant-ring module upstairs and a retraction downstairs. For a finite map,
canonical finite exchange and the actual finite cohomology equivalence give
an injective function on the original pulled-back classes. The original
additive arrows are used literally, without reconstructing an additive
dictionary for their composite at the geometric return boundary. Neither the forgotten
coefficient nor its arbitrary inverse image is declared injective. No class
zero, local effacement or support-induction conclusion is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u eY eY'

attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- The arbitrary-ring native module version uses the common faithful
adjunction construction, without converting through a second ZMod model. -/
theorem exists_moduleInjective_directImage_retract
    {T' T : Scheme.{u}} (f : T' ⟶ T) [Surjective f]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf T Λ) [Injective I] :
    ∃ J : ModuleSheaf T' Λ, Injective J ∧
      Nonempty (Retract I ((moduleDirectImage f Λ).obj J)) := by
  let : (moduleInverseImage f Λ).Faithful :=
    moduleInverseImage_faithful_of_surjective_map f Λ
  let : EnoughInjectives (ModuleSheaf T' Λ) :=
    SheafOfModules.enoughInjectivesLarge.{u + 1, u, 0} (constantRing T' Λ)
  exact CategoryTheory.Adjunction.exists_injective_rightAdjoint_retract
    (moduleInverseImage f Λ) (moduleDirectImage f Λ)
    (moduleInverseImageAdjunction f Λ) I

namespace Finite

variable {T' T Y' Y : Scheme.{u}}
  [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{eY'} (AbelianSheaf.{u, u + 1} Y')]
  (f : T' ⟶ T) [IsFinite f] (f' : Y' ⟶ Y)
  (b : Y ⟶ T) (b' : Y' ⟶ T') (h : IsPullback b' f' f b)

/-- The literal original coefficient arrow on cohomology, named once. -/
def finiteRetractCoefficientFunction
    {I : AbelianSheaf.{u, u + 1} T} (J : AbelianSheaf.{u, u + 1} T')
    (r : Retract I ((directImage f).obj J)) (q : ℕ) :
    Sheaf.H.{eY} ((inverseImage b).obj I) q →
      Sheaf.H.{eY} ((inverseImage b).obj ((directImage f).obj J)) q :=
  Sheaf.H.map ((inverseImage b).map r.i) q

omit [IsFinite f] in
/-- Original coefficient retraction detects the same classes. -/
theorem finiteRetractCoefficientFunction_injective
    {I : AbelianSheaf.{u, u + 1} T} (J : AbelianSheaf.{u, u + 1} T')
    (r : Retract I ((directImage f).obj J)) (q : ℕ) :
    Function.Injective (finiteRetractCoefficientFunction f b J r q) :=
  Sheaf.H.map_injective_of_retract (r.map (inverseImage b)) q

/-- The actual canonical finite mate on the same original cohomology groups. -/
def finiteRetractMateFunction (J : AbelianSheaf.{u, u + 1} T') (q : ℕ) :
    Sheaf.H.{eY} ((inverseImage b).obj ((directImage f).obj J)) q →
      Sheaf.H.{eY} ((directImage f').obj ((inverseImage b').obj J)) q := by
  letI : IsIso (baseChangeMap f f' b b' h.w.symm) :=
    finiteBaseChange_isIso f f' b b' h
  exact Sheaf.H.naturalIsoFunction (asIso (baseChangeMap f f' b b' h.w.symm)) J q

omit [HasExt.{eY'} (AbelianSheaf.{u, u + 1} Y')] in
/-- Canonical finite exchange, not an assumed comparison, gives injectivity. -/
theorem finiteRetractMateFunction_injective
    (J : AbelianSheaf.{u, u + 1} T') (q : ℕ) :
    Function.Injective (finiteRetractMateFunction f f' b b' h J q) := by
  let : IsIso (baseChangeMap f f' b b' h.w.symm) :=
    finiteBaseChange_isIso f f' b b' h
  exact Sheaf.H.naturalIsoFunction_injective
    (asIso (baseChangeMap f f' b b' h.w.symm)) J q

/-- The actual finite-cohomology comparison, with the finite instance
constructed from this exact original Cartesian square. -/
def finiteRetractComparisonFunction (J : AbelianSheaf.{u, u + 1} T') (q : ℕ) :
    Sheaf.H.{eY} ((directImage f').obj ((inverseImage b').obj J)) q →
      Sheaf.H.{eY'} ((inverseImage b').obj J) q := by
  letI : IsFinite f' :=
    MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  exact fun c => finiteCohomologyDirectImageAddEquiv.{u, eY', eY} f'
    ((inverseImage b').obj J) q c

/-- The named original finite comparison is injective. -/
theorem finiteRetractComparisonFunction_injective
    (J : AbelianSheaf.{u, u + 1} T') (q : ℕ) :
    Function.Injective (finiteRetractComparisonFunction f f' b b' h J q) := by
  let : IsFinite f' :=
    MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  exact (finiteCohomologyDirectImageAddEquiv.{u, eY', eY} f' ((inverseImage b').obj J) q).injective

/-- Preserve the successful ordinary-function construction. The three
unchanged original arrows have fixed names, so subsequent theorem boundaries
do not repeat their concrete group dictionaries or finite-instance terms. -/
def finiteRetractClassMap
    {I : AbelianSheaf.{u, u + 1} T} (J : AbelianSheaf.{u, u + 1} T')
    (r : Retract I ((directImage f).obj J)) (q : ℕ) :
    Sheaf.H.{eY} ((inverseImage b).obj I) q →
      Sheaf.H.{eY'} ((inverseImage b').obj J) q :=
  Function.transportThree
    (finiteRetractCoefficientFunction f b J r q)
    (finiteRetractMateFunction f f' b b' h J q)
    (finiteRetractComparisonFunction f f' b b' h J q)

/-- Evaluation through exactly the three named original functions. -/
theorem finiteRetractClassMap_apply
    {I : AbelianSheaf.{u, u + 1} T} (J : AbelianSheaf.{u, u + 1} T')
    (r : Retract I ((directImage f).obj J)) (q : ℕ)
    (c : Sheaf.H.{eY} ((inverseImage b).obj I) q) :
    finiteRetractClassMap f f' b b' h J r q c =
      finiteRetractComparisonFunction f f' b b' h J q
        (finiteRetractMateFunction f f' b b' h J q
          (finiteRetractCoefficientFunction f b J r q c)) :=
  Function.transportThree_apply
    (finiteRetractCoefficientFunction f b J r q)
    (finiteRetractMateFunction f f' b b' h J q)
    (finiteRetractComparisonFunction f f' b b' h J q) c

/-- Original class detection through the same three original functions. -/
theorem finiteRetractClassMap_injective
    {I : AbelianSheaf.{u, u + 1} T} (J : AbelianSheaf.{u, u + 1} T')
    (r : Retract I ((directImage f).obj J)) (q : ℕ) :
    Function.Injective (finiteRetractClassMap f f' b b' h J r q) :=
  Function.transportThree_injective
    (finiteRetractCoefficientFunction f b J r q)
    (finiteRetractMateFunction f f' b b' h J q)
    (finiteRetractComparisonFunction f f' b b' h J q)
    (finiteRetractCoefficientFunction_injective f b J r q)
    (finiteRetractMateFunction_injective f f' b b' h J q)
    (finiteRetractComparisonFunction_injective f f' b b' h J q)

/-- Construct the actual upstairs injective and original downstairs retraction
before transporting any class. This applies to the native constant-ring
module category used by open/closed support detection. -/
theorem exists_moduleInjective_finite_class_transport
    [Surjective f] (Λ : Type (u + 1)) [Ring Λ]
    (I : ModuleSheaf T Λ) [Injective I] :
    ∃ J : ModuleSheaf T' Λ, Injective J ∧
      ∃ r : Retract ((SheafOfModules.toSheaf (constantRing T Λ)).obj I)
          ((directImage f).obj ((SheafOfModules.toSheaf (constantRing T' Λ)).obj J)),
        ∀ q : ℕ, Function.Injective
          (finiteRetractClassMap f f' b b' h
            ((SheafOfModules.toSheaf (constantRing T' Λ)).obj J) r q) := by
  obtain ⟨J, hJ, ⟨r⟩⟩ := exists_moduleInjective_directImage_retract f Λ I
  let rA := (r.map (SheafOfModules.toSheaf (constantRing T Λ))).trans
    (Retract.ofIso ((moduleDirectImageUnderlyingIso f Λ).app J))
  exact ⟨J, hJ, rA, fun q => finiteRetractClassMap_injective f f' b b' h
    ((SheafOfModules.toSheaf (constantRing T' Λ)).obj J) rA q⟩

end Finite
end AlgebraicGeometry.Scheme.EtaleCohomology
