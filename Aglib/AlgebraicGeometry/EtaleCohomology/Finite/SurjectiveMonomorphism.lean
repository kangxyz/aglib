/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.MonomorphismCounit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SurjectivePullback

/-! # Original abelian sheaves across a surjective finite monomorphism

The original counit is invertible by the actual finite singleton-fibre stalk
calculation. The original triangle identity makes the inverse image of the
unit invertible. Faithfulness of inverse image along the original surjection
reflects its monomorphism and epimorphism properties; the original abelian
category is balanced. Thus the original unit and counit define an equivalence,
with no replacement site or coefficient model. Surjective closed immersions,
including nilpotent thickenings, are a special case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

/-- The original unit of a surjective finite monomorphism is invertible for
all original abelian coefficients on its target. -/
theorem surjectiveFiniteMono_unit_app_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Mono f] [Surjective f]
    (F : AbelianSheaf.{u, u + 1} S) :
    IsIso ((inverseImageAdjunction f).unit.app F) := by
  have : (inverseImage f).Faithful := Proper.Reduction.inverseImage_faithful_of_surjective f
  let η := (inverseImageAdjunction f).unit.app F
  let ε := (inverseImageAdjunction f).counit.app ((inverseImage f).obj F)
  have : IsIso ε := finiteMono_counit_app_isIso f ((inverseImage f).obj F)
  have hm : IsIso ((inverseImage f).map η) :=
    isIso_of_comp_hom_eq_id ε ((inverseImageAdjunction f).left_triangle_components F)
  have : Mono η := (inverseImage f).mono_of_mono_map (inferInstance : Mono ((inverseImage f).map η))
  have : Epi η := (inverseImage f).epi_of_epi_map (inferInstance : Epi ((inverseImage f).map η))
  exact isIso_of_mono_of_epi η

/-- The equivalence uses exactly the original inverse image, direct image,
unit and counit of the given surjective finite monomorphism. -/
def abelianSheafEquivalenceOfSurjectiveFiniteMono
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Mono f] [Surjective f] :
    AbelianSheaf.{u, u + 1} S ≌ AbelianSheaf.{u, u + 1} X := by
  have (F : AbelianSheaf.{u, u + 1} S) :
      IsIso ((inverseImageAdjunction f).unit.app F) := surjectiveFiniteMono_unit_app_isIso f F
  have (F : AbelianSheaf.{u, u + 1} X) :
      IsIso ((inverseImageAdjunction f).counit.app F) := finiteMono_counit_app_isIso f F
  exact (inverseImageAdjunction f).toEquivalence

/-- In particular, any surjective closed immersion gives the original
abelian-sheaf equivalence; no nilpotence bound or Noetherian hypothesis is needed. -/
def abelianSheafEquivalenceOfSurjectiveClosedImmersion
    {X S : Scheme.{u}} (f : X ⟶ S) [IsClosedImmersion f] [Surjective f] :
    AbelianSheaf.{u, u + 1} S ≌ AbelianSheaf.{u, u + 1} X :=
  abelianSheafEquivalenceOfSurjectiveFiniteMono f

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
