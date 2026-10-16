/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Composition of the original derived scalar-coinduction functors

Native coinduction preserves injectives, so the installed bounded-below
right-derived functors compose through the same ordinary coinduction
comparison. The unit equation retains the original mapped cochain arrow
and both actual installed units. Ring, ambient module and derived size
universes are explicit, and the supplied derived categories are arbitrary.
No commutativity, flatness, regularity or finiteness is assumed.

Regular-embedding purity can use this transitivity after its separate
cohomology/Ext and quotient-line normalization. This construction itself
asserts neither concentration nor geometric purity.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u v w z a b c
namespace ModuleCat
variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]
  [HasDerivedCategory.{a} (ModuleCat.{max u v w z} R)]
  [HasDerivedCategory.{b} (ModuleCat.{max u v w z} S)]
  [HasDerivedCategory.{c} (ModuleCat.{max u v w z} T)]
  (σ : R →+* S) (τ : S →+* T)

/-- The actual bounded-below derived coinduction for a composite is its derived composite. -/
def derivedCoextendScalarsPlusCompIso :
    (coextendScalars (τ.comp σ) :
      ModuleCat.{max u v w z} R ⥤ ModuleCat.{max u v w z} T).rightDerivedFunctorPlus ≅
      (coextendScalars σ : ModuleCat.{max u v w z} R ⥤
        ModuleCat.{max u v w z} S).rightDerivedFunctorPlus ⋙
          (coextendScalars τ).rightDerivedFunctorPlus := by
  let F : ModuleCat.{max u v w z} R ⥤ ModuleCat.{max u v w z} S := coextendScalars σ
  let G : ModuleCat.{max u v w z} S ⥤ ModuleCat.{max u v w z} T := coextendScalars τ
  let : F.PreservesInjectiveObjects :=
    coextendScalars_preservesInjectiveObjects.{u, v, max u v w z} σ
  exact (coextendScalars (τ.comp σ)).rightDerivedFunctorPlusIso
      (coextendScalarsComp.{u, v, w, max u z} σ τ) ≪≫
    F.rightDerivedFunctorPlusCompIsoOfPreservesInjectives G

/-- The derived composition retains the ordinary comparison and both installed units. -/
@[reassoc]
theorem derivedCoextendScalarsPlusCompIso_unit
    (K : CochainComplex.Plus (ModuleCat.{max u v w z} R)) :
    (coextendScalars (τ.comp σ)).rightDerivedFunctorPlusUnit.app K ≫
        (derivedCoextendScalarsPlusCompIso σ τ).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (coextendScalarsComp.{u, v, w, max u z} σ τ)).hom.app K) ≫
        (Functor.rightDerivedFunctorPlusCompUnit (coextendScalars σ)
          (coextendScalars τ)).app K := by
  let F : ModuleCat.{max u v w z} R ⥤ ModuleCat.{max u v w z} S := coextendScalars σ
  let G : ModuleCat.{max u v w z} S ⥤ ModuleCat.{max u v w z} T := coextendScalars τ
  let : F.PreservesInjectiveObjects :=
    coextendScalars_preservesInjectiveObjects.{u, v, max u v w z} σ
  have h₁ := (coextendScalars (τ.comp σ)).rightDerivedFunctorPlusIso_hom_app
    (coextendScalarsComp.{u, v, w, max u z} σ τ) K
  have h₂ := F.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app G K
  change _ ≫ ((coextendScalars (τ.comp σ)).rightDerivedFunctorPlusIso
    (coextendScalarsComp.{u, v, w, max u z} σ τ)).hom.app _ ≫
      (F.rightDerivedFunctorPlusCompIsoOfPreservesInjectives G).hom.app _ = _
  rw [← Category.assoc, h₁, Category.assoc, h₂]
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]

end ModuleCat
