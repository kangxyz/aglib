/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.SourceAction
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ChangeUniverse
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite

/-!
# Finite generation of the actual higher-coinduction modules

Over a Noetherian commutative ring, a finite restricted source algebra and a
finite coefficient give finite higher-coinduction modules over the source
algebra. Native finite Ext is transported to the selected size through the
original universe comparison. The unchanged identity on Ext is semilinear
by the proved source-action formula; no new scalar action is installed.

The same installed derived-homology comparison then proves finite generation
of its actual homology. No locality, surjectivity, flatness, projectivity,
concentration or canonical trivialization is assumed. This supplies the
finite-generation condition for the normal-quotient canonical module; it does
not prove homothety, dualizing uniqueness or a reverse Gorenstein criterion.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w a b

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
  (q : R →+* S) (N : ModuleCat.{u} R)
  [Module.Finite R ((restrictScalars q).obj (ModuleCat.of S S))]
  [Module.Finite R N]

/-- The original Ext carrier, with its actual coinduced source action, is
finite over the source algebra, independently of the selected Ext size. -/
theorem coinducedExtSourceModule_finite [HasExt.{w} (ModuleCat.{u} R)] (n : ℕ) :
    letI := coinducedExtSourceModule q N n
    Module.Finite S (Ext.{w} ((restrictScalars q).obj (ModuleCat.of S S)) N n) := by
  let := coinducedExtSourceModule q N n
  let T := (restrictScalars q).obj (ModuleCat.of S S)
  let E := Ext.{w} T N n
  let : Module.Finite R (Ext.{u} T N n) := inferInstance
  let : Module.Finite R E := Module.Finite.equiv
    (Ext.chgUnivLinearEquiv.{u, u + 1, u, u, w} R T N n : Ext.{u} T N n ≃ₗ[R] E)
  let f : E →ₛₗ[q] E :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => (coinducedExtSourceModule_map_smul q N n r x).symm }
  exact Module.Finite.of_surjective f Function.surjective_id

variable [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]

/-- The same homology of installed derived coinduction is a finite target-ring
module. Both selected derived-category sizes remain independent. -/
theorem derivedCoextendScalarsPlusHomology_finite (n : ℕ) :
    Module.Finite S
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
        ((coextendScalars q).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N))) := by
  let := coinducedExtSourceModule.{u, u} q N n
  let : Module.Finite S (Ext.{u} ((restrictScalars q).obj (ModuleCat.of S S)) N n) :=
    coinducedExtSourceModule_finite q N n
  exact Module.Finite.equiv
    (derivedCoextendScalarsPlusHomologyExtSourceLinearEquiv q N n
      (injectiveResolution N)).symm

end ModuleCat
