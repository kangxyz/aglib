/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Ext.Localization
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Flat
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Linear
public import Aglib.Algebra.Category.ModuleCat.Localization.ScalarExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Original top Ext under localization of the base ring

The original native exact-functor map on top Ext is a localization map
when the specified algebra is a localization of the base ring. The proof
uses the original scalar-adjunction unit, fixed-base coefficient localization
and Mathlib's exact-adjunction Ext equivalence. Both native exactness
conditions follow from localization flatness in the public statement.

The coefficient requires no regularity, flatness, finiteness or Noetherian
hypothesis. Rings and module carriers share the same universe, as required
by the native scalar adjunction here; the two supported Ext sizes remain
independent. The target source is the actual scalar extension of R/I.
Its comparison with A/(IA), normalization in the original Koszul complex
over A, determinant changes and geometric purity remain separate consumers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w z

namespace ChainComplex.Koszul

section Generic
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt.{w} C] [HasExt.{z} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private theorem extEquiv_mapExactFunctor_unit (adj : F ⊣ G) {X Y : C} {n : ℕ}
    (x : Ext.{w} X Y n) :
    adj.extEquiv (x.mapExactFunctor F) =
      x.comp (Ext.mk₀ (adj.unit.app Y)) (add_zero n) := by
  rw [Adjunction.extEquiv_apply, ← Ext.comp_mapExactFunctor]
  simpa only [Ext.id_mapExactFunctor] using
    (Ext.mapExactFunctor_comp_mk₀_natTransApp x adj.unit).symm
end Generic

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

private instance scalarRestriction_linear :
    (ModuleCat.restrictScalars (algebraMap R A)).Linear R :=
  inferInstanceAs
    ((ModuleCat.restrictScalars (Algebra.ofId R A).toRingHom).Linear R)

variable [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} A)]

/-- The original exact scalar-extension map localizes top Ext of a weakly
regular quotient at the specified submonoid. -/
theorem topExtScalarExtension_isLocalizedModule (T : Submonoid R) [IsLocalization T A] (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (N : ModuleCat.{u} R) :
    let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat (algebraMap R A)
        (show (algebraMap R A).Flat from by
          exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    let : PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap R A)) :=
      ModuleCat.extendScalars_preservesFiniteColimits_of_flat (algebraMap R A)
        (show (algebraMap R A).Flat from by
          exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T))
    IsLocalizedModule T
      ((ModuleCat.extendScalars (algebraMap R A)).mapExtLinearMap R
        (ModuleCat.of R (R ⧸ Ideal.ofList s)) N s.length) := by
  have hflat : (algebraMap R A).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A T)
  let : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hflat
  let : PreservesFiniteColimits (ModuleCat.extendScalars (algebraMap R A)) :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ hflat
  let F := ModuleCat.extendScalars (algebraMap R A)
  let adj := ModuleCat.extendRestrictScalarsAdj.{u} (algebraMap R A)
  let b := F.mapExtLinearMap R (ModuleCat.of R (R ⧸ Ideal.ofList s)) N s.length
  let η := adj.unit.app N
  let : IsLocalizedModule T η.hom :=
    ModuleCat.extendRestrictScalarsAdj_unit_isLocalizedModule T (algebraMap R A)
      (by
        rw [toAlgebra_algebraMap]
        infer_instance) N
  let e := adj.extLinearEquiv R
    (X := ModuleCat.of R (R ⧸ Ideal.ofList s)) (Y := F.obj N) (n := s.length)
  let q := (Ext.mk₀ η).postcompOfLinear R (ModuleCat.of R (R ⧸ Ideal.ofList s))
    (add_zero s.length)
  let : IsLocalizedModule T q :=
    ChainComplex.Koszul.topExtPostcomp_isLocalizedModule T η s hs
  have he : b = e.symm.toLinearMap.comp q := by
    apply LinearMap.ext
    intro x
    apply e.injective
    change adj.extEquiv (x.mapExactFunctor F) = e (e.symm (q x))
    rw [LinearEquiv.apply_symm_apply]
    exact extEquiv_mapExactFunctor_unit adj x
  change IsLocalizedModule T b
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T q e.symm

end ChainComplex.Koszul
