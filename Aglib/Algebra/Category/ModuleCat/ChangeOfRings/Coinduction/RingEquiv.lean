/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Derived
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-!
# Native derived coinduction along ring isomorphisms

Original scalar coinduction along a ring isomorphism is the original scalar
restriction along its inverse. The comparison uses uniqueness of the same
right adjoints and retains their original unit and counit equations.

The installed D+ functor carries every actual single coefficient to the
single of that inverse restriction. The comparison is natural in the
coefficient and uses the original derived-functor isomorphism and native
exact-single comparison. For the ring coefficient it retains the native
restricted-ring isomorphism in every integer degree. This is the transport
needed when iterating regular quotients; it imposes no regularity or
finiteness hypothesis.

The ordinary and single-functor comparisons allow independent ring, ambient
module, and derived-category universes. The ring-coefficient endpoint uses
a common ring/module universe, as in the principal purity consumer. No new
global instance or alternate derived functor is introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v z a b
namespace ModuleCat
section General
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (e : R ≃+* S)

/-- Original coinduction along a ring isomorphism is inverse scalar restriction. -/
def coextendScalarsRingEquivIso :
    (coextendScalars e.toRingHom :
      ModuleCat.{max u v z} R ⥤ ModuleCat.{max u v z} S) ≅
      restrictScalars e.symm.toRingHom :=
  (restrictCoextendScalarsAdj.{max u v z, u, v} e.toRingHom).rightAdjointUniq
    (restrictScalarsEquivalenceOfRingEquiv e).toAdjunction

/-- The functor comparison retains the original coinduction counit. -/
@[reassoc]
theorem coextendScalarsRingEquivIso_counit (M : ModuleCat.{max u v z} R) :
    (restrictScalars e.toRingHom).map ((coextendScalarsRingEquivIso e).hom.app M) ≫
        (restrictScalarsEquivalenceOfRingEquiv e).toAdjunction.counit.app M =
      (restrictCoextendScalarsAdj.{max u v z, u, v} e.toRingHom).counit.app M := by
  exact Adjunction.rightAdjointUniq_hom_app_counit
    (restrictCoextendScalarsAdj.{max u v z, u, v} e.toRingHom)
    (restrictScalarsEquivalenceOfRingEquiv e).toAdjunction M

/-- The functor comparison retains the original coinduction unit. -/
@[reassoc]
theorem coextendScalarsRingEquivIso_unit (M : ModuleCat.{max u v z} S) :
    (restrictCoextendScalarsAdj.{max u v z, u, v} e.toRingHom).unit.app M ≫
        (coextendScalarsRingEquivIso e).hom.app ((restrictScalars e.toRingHom).obj M) =
      (restrictScalarsEquivalenceOfRingEquiv e).toAdjunction.unit.app M := by
  exact Adjunction.unit_rightAdjointUniq_hom_app
    (restrictCoextendScalarsAdj.{max u v z, u, v} e.toRingHom)
    (restrictScalarsEquivalenceOfRingEquiv e).toAdjunction M

variable [HasDerivedCategory.{a} (ModuleCat.{max u v z} R)]
  [HasDerivedCategory.{b} (ModuleCat.{max u v z} S)]

/-- Every actual derived single is the single of original inverse scalar restriction. -/
def derivedCoextendScalarsPlusRingEquivSingleIso (i : ℤ) :
    DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v z} R) i ⋙
        (coextendScalars e.toRingHom).rightDerivedFunctorPlus ≅
      restrictScalars e.symm.toRingHom ⋙
        DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v z} S) i := by
  let G : ModuleCat.{max u v z} R ⥤ ModuleCat.{max u v z} S :=
    restrictScalars e.symm.toRingHom
  let E : ModuleCat.{max u v z} R ≌ ModuleCat.{max u v z} S :=
    (restrictScalarsEquivalenceOfRingEquiv e).symm
  letI : G.IsLeftAdjoint := E.toAdjunction.isLeftAdjoint
  letI : G.IsRightAdjoint := E.symm.toAdjunction.isRightAdjoint
  letI : G.PreservesHomology := inferInstance
  exact Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ i)
      ((coextendScalars e.toRingHom).rightDerivedFunctorPlusIso
        (coextendScalarsRingEquivIso e)) ≪≫ G.rightDerivedFunctorPlusSingleIso i

end General
section Ring
variable {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)
  [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]

/-- Original derived coinduction sends the actual regular ring single to the target ring single. -/
def derivedCoextendScalarsPlusRingEquivRingIso (i : ℤ) :
    (coextendScalars e.toRingHom).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) i).obj (ModuleCat.of R R)) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} S) i).obj (ModuleCat.of S S) :=
  (derivedCoextendScalarsPlusRingEquivSingleIso.{u,u,u,a,b} e i).app (ModuleCat.of R R) ≪≫
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} S) i).mapIso
      (restrictScalarsIsoOfEquiv e.symm)
end Ring

end ModuleCat
