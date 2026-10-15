/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Essentially etale maps on actual scheme stalks

The algebra on the source stalk is induced by the actual scheme stalk map.
Its finite type property is essential finite type; no finite-presentation
or `Algebra.Etale` structure is imposed on the localized map.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- The three algebraic properties of the actual stalk map are available
without replacing essential finite type by finite presentation. -/
theorem stalkMap_essentiallyEtaleProperties (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] [FormallyUnramified f] (x : X) :
    (f.stalkMap x).hom.EssFiniteType ∧ (f.stalkMap x).hom.Flat ∧
      (f.stalkMap x).hom.FormallyUnramified :=
  ⟨LocallyOfFiniteType.stalkMap f x, Flat.stalkMap f x,
    FormallyUnramified.stalkMap f x⟩

/-- The maximal ideal of the actual source stalk lies over that of the target
stalk, for the algebra defined by the actual stalk map. -/
theorem stalkMap_maximalIdeal_liesOver (f : X ⟶ Y) (x : X) :
    let := (f.stalkMap x).hom.toAlgebra
    (maximalIdeal (X.presheaf.stalk x)).LiesOver
      (maximalIdeal (Y.presheaf.stalk (f x))) := by
  let := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  infer_instance

/-- Essential finite type of the actual stalk map transports Noetherianity
from the target stalk; no global Noetherian hypothesis is required. -/
theorem isNoetherianRing_stalk_of_locallyOfFiniteType (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X)
    [IsNoetherianRing (Y.presheaf.stalk (f x))] :
    IsNoetherianRing (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  exact Algebra.EssFiniteType.isNoetherianRing (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- An essentially etale map preserves the dimensions of the actual
Noetherian scheme stalks. -/
theorem ringKrullDim_stalk_eq_of_flat_formallyUnramified (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] [FormallyUnramified f] (x : X)
    [IsNoetherianRing (Y.presheaf.stalk (f x))] :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  let := (f.stalkMap x).hom.toAlgebra
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  let : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  let : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    FormallyUnramified.stalkMap f x
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  let : IsNoetherianRing (X.presheaf.stalk x) :=
    isNoetherianRing_stalk_of_locallyOfFiniteType f x
  exact Algebra.FormallyUnramified.ringKrullDim_eq_of_flat _ _

/-- Regularity ascends from a target stalk to the actual source stalk of an
essentially etale morphism. -/
theorem isRegularLocalRing_stalk_of_flat_formallyUnramified (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] [FormallyUnramified f] (x : X)
    [IsRegularLocalRing (Y.presheaf.stalk (f x))] :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  let : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  let : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    FormallyUnramified.stalkMap f x
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  let : IsNoetherianRing (X.presheaf.stalk x) :=
    isNoetherianRing_stalk_of_locallyOfFiniteType f x
  exact Algebra.FormallyUnramified.isRegularLocalRing_of_flat
    (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- The dimension bridge applied to the actual stalk map of an etale morphism. -/
theorem ringKrullDim_stalk_eq_of_etale (f : X ⟶ Y) [Etale f]
    (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))] :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) :=
  ringKrullDim_stalk_eq_of_flat_formallyUnramified f x

/-- The regularity bridge applied to an actual etale stalk map. -/
theorem isRegularLocalRing_stalk_of_etale (f : X ⟶ Y) [Etale f]
    (x : X)
    [IsRegularLocalRing (Y.presheaf.stalk (f x))] :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_flat_formallyUnramified f x

end AlgebraicGeometry.Scheme
