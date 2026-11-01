/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtalePresentation

/-! Native coefficient presentations, without curve or duality hypotheses. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u v

attribute [local instance] hasSheafifyLarge hasSheafifyModules ModuleCat.Sheaf.hasSheafify
  Abelian.hasFiniteBiproducts

example (n : ℕ) (hn : 0 < n)
    (M : ModuleCat.{v} (ULift.{v} (ZMod n))) [Finite M] :
    ∃ (m : ℕ) (i : M ⟶ ModuleCat.of (ULift.{v} (ZMod n))
      (Fin m → ULift.{v} (ZMod n))), Mono i :=
  ModuleCat.exists_mono_finPi_uLiftZMod n hn M

example {U : Scheme.{u}} [ConnectedSpace U] (n : ℕ) (hn : 0 < n)
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    ∃ Y : Scheme.FiniteEtale U,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      ∃ (m : ℕ) (a : F ⟶ (moduleDirectImage Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n)))), Mono a :=
  exists_galois_unit_biproduct_directImage_mono n hn F hF

/-- The existing epimorphism is reused unchanged at the coefficient level. -/
example {U : Scheme.{u}} [ConnectedSpace U] (n : ℕ) (hn : 0 < n)
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).inverse.obj F)) :
    ∃ Y : Scheme.FiniteEtale U,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      ∃ (m : ℕ) (a : (moduleLowerShriek Y.obj.hom (ULift.{u + 1} (ZMod n))).obj
        (⨁ fun _ : Fin m => moduleUnit Y.obj.left (ULift.{u + 1} (ZMod n))) ⟶ F), Epi a :=
  exists_galois_unit_biproduct_lowerShriek_epi n hn F hF

/-- info: 'ModuleCat.exists_mono_finPi_uLiftZMod' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.exists_mono_finPi_uLiftZMod

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_unit_biproduct_directImage_mono' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_unit_biproduct_directImage_mono

/-- Finite direct image and cokernels are computed in the same native
coefficient category, without field, curve, Ext or trace inputs. -/
example {U V : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    (f : V ⟶ U) [IsFinite f] [Etale f] (P : ModuleSheaf V Λ)
    (hP : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence V Λ).inverse.obj P)) :
    Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U Λ).inverse.obj ((moduleDirectImage f Λ).obj P)) :=
  moduleDirectImage_isFiniteTypeLocallyConstant Λ f P hP
