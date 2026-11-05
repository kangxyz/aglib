/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FilteredPresentation
public import Aglib.CategoryTheory.Filtered.AdjointStageHom

/-! # Original native module Hom cocones

The actual fixed-cocone Hom universal property extends from the original
free affine-etale generators to their native finite-colimit closure. Source
closure uses native finite-limit interchange, not finite presentation of the
underlying abelian sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation

universe u

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

/-- Generator section continuity extends to the actual native stage objects. -/
def canonicalHomCoconeIsColimit (R : Type (u + 1)) [Ring R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (X : Scheme.{u})
    {D : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (c : Cocone D)
    (hgen : ∀ U : X.AffineEtale,
      IsColimit ((coyoneda.obj (op (ModuleCat.Sheaf.freeRepresentable.{u + 1, u + 1, u, 0}
        X.smallEtaleTopology R ((Scheme.AffineEtale.Spec X).obj U)))).mapCocone c))
    (A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hA : finiteColimitStages R X A) :
    IsColimit ((coyoneda.obj (op A)).mapCocone c) :=
  AdjointStageHom.homCoconeIsColimitOfFiniteColimitClosure
    (generators R X) c (by
      intro B hB
      exact Classical.choice (by
        rcases hB with ⟨U⟩
        exact ⟨hgen U⟩)) A hA

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation
