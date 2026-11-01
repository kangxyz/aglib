/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CounitCoefficientColimit
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteTypeArrowLimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModImages

/-! # Genuine module coefficients at simultaneous finite-type stages

The module coefficient at a stage is the original direct image, and is
injective in the genuine ZMod sheaf category when the original module is.
Its underlying abelian coefficients are reconstructed by the original counit
colimit. No injectivity of the underlying abelian sheaf is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeArrowLimit
universe u
open Algebra.FiniteTypeArrowLimit EtaleCohomology.Continuity EtaleCohomology.Proper.Reduction
attribute [local instance] EtaleCohomology.hasSheafifyLarge

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (α : A →ₐ[R] B)

/-- The quiver underlying the opposite category of finite-type arrow indices. -/
local instance : Quiver (Index A B)ᵒᵖ :=
  (inferInstance : Category (Index A B)ᵒᵖ).toQuiver

/-- The actual original module direct image at a source finite-type stage. -/
abbrev sourceStageModule (n : ℕ) (M : ZModSheaf (Spec (.of A)) n) (s : Index A B) :=
  (zmodDirectImage ((sourceSpecCone α).π.app (op s)) n).obj M

/-- Exact module inverse image gives genuine module injectivity at each stage. -/
instance sourceStageModule_injective (n : ℕ) (M : ZModSheaf (Spec (.of A)) n)
    [Injective M] (s : Index A B) : Injective (sourceStageModule α n M s) := by
  exact (zmodDirectImage_preservesInjectiveObjects
    ((sourceSpecCone α).π.app (op s)) n).injective_obj
    (inferInstance : Injective M)

/-- The corresponding actual module at a target finite-type stage. -/
abbrev targetStageModule (n : ℕ) (M : ZModSheaf (Spec (.of B)) n) (s : Index A B) :=
  (zmodDirectImage ((targetSpecCone α).π.app (op s)) n).obj M

/-- Genuine module injectivity also holds at the other end of the same arrow. -/
instance targetStageModule_injective (n : ℕ) (M : ZModSheaf (Spec (.of B)) n)
    [Injective M] (s : Index A B) : Injective (targetStageModule α n M s) := by
  exact (zmodDirectImage_preservesInjectiveObjects
    ((targetSpecCone α).π.app (op s)) n).injective_obj
    (inferInstance : Injective M)

/-- Forgetting module scalars retains the original abelian stage coefficient. -/
def sourceStageModuleUnderlyingIso (n : ℕ) (M : ZModSheaf (Spec (.of A)) n)
    (s : Index A B) :
    (zmodUnderlying _ n).obj (sourceStageModule α n M s) ≅
      (EtaleCohomology.directImage ((sourceSpecCone α).π.app (op s))).obj
        ((zmodUnderlying _ n).obj M) :=
  (zmodDirectImageUnderlyingIso ((sourceSpecCone α).π.app (op s)) n).app M

/-- The original source-spectrum counit cocone reconstructs any module's
underlying abelian sheaf. Injectivity is not needed for reconstruction. -/
def sourceModuleCounitIsColimit (n : ℕ) (M : ZModSheaf (Spec (.of A)) n) :
    IsColimit (directImageCounitCocone (sourceSpecDiagram α).op (sourceSpecCone α).op
      ((zmodUnderlying _ n).obj M)) := by
  have (s : ((Index A B)ᵒᵖ)ᵒᵖ) : IsAffine (((sourceSpecDiagram α).op.obj s).unop) := by
    change IsAffine (Spec _)
    infer_instance
  have {s t : ((Index A B)ᵒᵖ)ᵒᵖ} (a : s ⟶ t) :
      IsAffineHom (((sourceSpecDiagram α).op.map a).unop) := by
    change IsAffineHom ((sourceSpecDiagram α).map a.unop)
    infer_instance
  exact isColimitDirectImageCounitCocone (sourceSpecDiagram α).op (sourceSpecCone α).op
    (sourceSpecConeIsLimit α).op ((zmodUnderlying _ n).obj M)

end AlgebraicGeometry.Scheme.FiniteTypeArrowLimit
