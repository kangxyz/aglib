/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Single.Quotient

/-!
# The scalar quotient functor

Quotienting a module by the image of a fixed scalar is an additive functor.
It preserves scalar-multiplication morphisms. Applied degreewise, it is the
literal quotient complex used by the one-element tensor augmentation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] (a : R)

/-- Quotient a linear morphism by multiplication by the same scalar in source and target. -/
def scalarQuotientMap {M N : ModuleCat R} (f : M ⟶ N) :
    ModuleCat.of R (SingleQuotient M a) ⟶ ModuleCat.of R (SingleQuotient N a) :=
  ModuleCat.ofHom ((LinearMap.range (LinearMap.lsmul R M a)).mapQ
    (LinearMap.range (LinearMap.lsmul R N a)) f.hom (by
      rintro x ⟨y, rfl⟩
      exact ⟨f y, (map_smul f.hom a y).symm⟩))

/-- The actual quotient-module functor by a fixed scalar. -/
def scalarQuotientFunctor : ModuleCat R ⥤ ModuleCat R where
  obj M := ModuleCat.of R (SingleQuotient M a)
  map := scalarQuotientMap a
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

instance scalarQuotientFunctor_additive : (scalarQuotientFunctor a).Additive where
  map_add {_ _ f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

@[simp]
theorem scalarQuotientFunctor_map_mk {M N : ModuleCat R} (f : M ⟶ N) (x : M) :
    (scalarQuotientFunctor a).map f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := rfl

/-- The functor preserves each scalar-multiplication endomorphism. -/
theorem scalarQuotientFunctor_map_lsmul (M : ModuleCat R) (b : R) :
    (scalarQuotientFunctor a).map (ModuleCat.ofHom (LinearMap.lsmul R M b)) =
      ModuleCat.ofHom (LinearMap.lsmul R ((scalarQuotientFunctor a).obj M) b) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- Applying the quotient functor degreewise gives the literal quotient complex. -/
theorem scalarQuotientFunctor_mapComplex (K : ChainComplex (ModuleCat R) ℕ) :
    ((scalarQuotientFunctor a).mapHomologicalComplex (ComplexShape.down ℕ)).obj K =
      quotientComplex a K := rfl

end ChainComplex.Koszul
