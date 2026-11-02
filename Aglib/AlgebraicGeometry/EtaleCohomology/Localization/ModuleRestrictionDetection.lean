/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleShortExact

/-! # Original module restrictions jointly detect arrows

Complementary open and closed inverse images detect the original module
arrow by the actual geometric stalk comparisons. No support decomposition
or replacement coefficient category is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge

private theorem module_stalk_map_eq_of_inverseImage_eq
    {S X : Scheme.{u}} (f : S ⟶ X) (Λ : Type (u + 1)) [Ring Λ]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ S)
    (η : Spec (.of Ω) ⟶ X) (hζ : ζ ≫ f = η)
    {M N : ModuleSheaf X Λ} (a b : M ⟶ N)
    (h : (moduleInverseImage f Λ).map a = (moduleInverseImage f Λ).map b) :
    (pointSmallEtale η).sheafFiber.map
        ((SheafOfModules.toSheaf (constantRing X Λ)).map a) =
      (pointSmallEtale η).sheafFiber.map
        ((SheafOfModules.toSheaf (constantRing X Λ)).map b) := by
  subst η
  let Q := SheafOfModules.toSheaf (constantRing X Λ)
  let Q' := SheafOfModules.toSheaf (constantRing S Λ)
  let P := (pointSmallEtale ζ).sheafFiber (A := AddCommGrpCat.{u + 1})
  let e := Functor.isoWhiskerRight (moduleInverseImageUnderlyingIso Λ f) P
  have h₁ : ((moduleInverseImage f Λ ⋙ Q') ⋙ P).map a =
      ((moduleInverseImage f Λ ⋙ Q') ⋙ P).map b :=
    congrArg (fun k => P.map (Q'.map k)) h
  have h₂ : ((Q ⋙ inverseImage f) ⋙ P).map a =
      ((Q ⋙ inverseImage f) ⋙ P).map b := by
    rw [← NatIso.naturality_1 e, ← NatIso.naturality_1 e, h₁]
  let e' := Functor.isoWhiskerLeft Q (StalkInverseImage.nativeStalkIso f ζ)
  change (Q ⋙ (pointSmallEtale (ζ ≫ f)).sheafFiber).map a =
    (Q ⋙ (pointSmallEtale (ζ ≫ f)).sheafFiber).map b
  rw [← NatIso.naturality_1 e'.symm, ← NatIso.naturality_1 e'.symm]
  exact congrArg (fun k => (e'.app M).hom ≫ k ≫ (e'.app N).inv) h₂

/-- Complementary original open and closed module inverse images jointly
faithfully detect every arrow, without finiteness or Noetherian hypotheses. -/
theorem module_map_eq_of_open_closed_restrictions
    {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (Λ : Type (u + 1)) [Ring Λ] {M N : ModuleSheaf X Λ} (a b : M ⟶ N)
    (hj : (moduleInverseImage j Λ).map a = (moduleInverseImage j Λ).map b)
    (hi : (moduleInverseImage i Λ).map a = (moduleInverseImage i Λ).map b) : a = b := by
  have (x : FibrewiseClosed.Index (𝟙 X)) : PreservesFiniteLimits
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})) :=
    preservesFiniteLimits_of_natIso
      (StalkUniverse.sheafFiberIso (FibrewiseClosed.geometricPoint x.val))
  apply (SheafOfModules.toSheaf (constantRing X Λ)).map_injective
  apply (StalkUniverse.originalStalks_jointlyReflectIsomorphisms
    (𝟙 X)).jointlyFaithful.map_injective
  intro x
  let η := FibrewiseClosed.geometricPoint x.val
  by_cases hx : η default ∈ Set.range i
  · obtain ⟨ζ, hζ⟩ := exists_closedImmersion_pointLift i η hx
    exact module_stalk_map_eq_of_inverseImage_eq i Λ ζ η hζ a b hi
  · have hxj : η default ∈ Set.range j := by rw [hcomp]; exact hx
    obtain ⟨ζ, hζ⟩ := exists_openImmersion_pointLift j η hxj
    exact module_stalk_map_eq_of_inverseImage_eq j Λ ζ η hζ a b hj

end AlgebraicGeometry.Scheme.EtaleCohomology
