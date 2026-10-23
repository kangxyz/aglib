/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.ZariskiEtale
public import Aglib.CategoryTheory.Functor.FlatKanExtension
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.RaisedInjectives
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Category.Grp.AB

/-! # The actual Zariski--étale adjunction at the larger value universe

Restriction is the native continuous-site pushforward on original sheaves.
Its inverse image is exact, proved by the original flat Kan extension at
independent category sizes. Consequently restriction preserves injectives;
it is not claimed to preserve arbitrary epimorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u})

/-- Sheafification on opens at the actual étale coefficient universe. -/
instance zariskiSheafifyRaised :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} :=
  Sheaf.LargeCohomology.hasSheafifyRaised.{u, u, u + 1} _

/-- The literal restriction of small étale abelian sheaves to open subschemes. -/
abbrev zariskiRestriction :=
  (opensToEtale X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X) (smallEtaleTopology X)

/-- The native left adjoint of the original restriction functor. -/
abbrev zariskiInverseImage :=
  (opensToEtale X).sheafPullback AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X) (smallEtaleTopology X)

/-- The original continuous-site adjunction. -/
def zariskiEtaleAdjunction : zariskiInverseImage X ⊣ zariskiRestriction X :=
  (opensToEtale X).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X) (smallEtaleTopology X)

instance zariskiRestriction_additive : (zariskiRestriction X).Additive where
  map_add := rfl

instance zariskiInverseImage_additive : (zariskiInverseImage X).Additive :=
  (zariskiEtaleAdjunction X).left_adjoint_additive

/-- Exact inverse image uses the actual filtered costructured-arrow colimits,
not a same-universe small-category specialization. -/
instance zariskiInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (zariskiInverseImage X) := by
  let G := opensToEtale X
  let : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  let : ∀ T : X.Etaleᵒᵖ, IsFiltered (CostructuredArrow G.op T) := fun T =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence G (unop T))
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  let : PreservesFiniteLimits
      (G.op.lan : (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    Functor.lan_preservesFiniteLimits_of_flat_of_shapes AddCommGrpCat.{u + 1} G
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits G AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X) (smallEtaleTopology X)

instance zariskiInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (zariskiInverseImage X) := by
  let := (zariskiEtaleAdjunction X).isLeftAdjoint
  infer_instance

instance zariskiRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (zariskiRestriction X) := by
  let := (zariskiEtaleAdjunction X).isRightAdjoint
  infer_instance

/-- Restriction preserves injectives because its actual left adjoint is exact. -/
instance zariskiRestriction_preservesInjectiveObjects :
    (zariskiRestriction X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (zariskiEtaleAdjunction X)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
