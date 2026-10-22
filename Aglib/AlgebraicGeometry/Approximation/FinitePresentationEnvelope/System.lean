/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual arithmetic approximation systems

The data of an inverse system of finite-type arithmetic schemes with affine
transition maps, together with its limiting cone at the original scheme.
This packet records actual objects and maps; its definition alone is not an
existence theorem for arbitrary schemes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope

/-- An arithmetic approximation system with the original scheme as literal limit. -/
structure System (X : Scheme.{u}) where
  /-- The small indexing category. -/
  Index : Type u
  /-- The category structure on the actual index. -/
  category : Category.{u} Index
  /-- The index is cofiltered and nonempty. -/
  cofiltered : @IsCofiltered Index category
  /-- The actual scheme diagram. -/
  diagram : @Functor Index category Scheme inferInstance
  /-- The original projections form a natural transformation. -/
  projection : (Functor.const Index).obj X ⟶ diagram
  /-- The cone at the original scheme is limiting. -/
  isLimit : IsLimit (Cone.mk X projection)
  /-- Transition maps are affine. -/
  affine : ∀ {i j} (f : i ⟶ j), IsAffineHom (diagram.map f)
  /-- Every stage is locally of finite type over the arithmetic base. -/
  finiteType : ∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (diagram.obj i))
  /-- Every stage is quasi-compact. -/
  compact : ∀ i, CompactSpace (diagram.obj i)

attribute [instance] System.category System.cofiltered System.affine
  System.finiteType System.compact

/-- The arithmetic base is locally Noetherian in the original scheme universe. -/
instance arithmeticBase_isLocallyNoetherian :
    IsLocallyNoetherian (Spec (CommRingCat.of (ULift.{u} ℤ))) := by
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  infer_instance

namespace System

variable {X : Scheme.{u}} (M : System X)

/-- The actual cone, with point definitionally equal to `X`. -/
def cone : Cone M.diagram := Cone.mk X M.projection

/-- Original projections of an arithmetic approximation are affine. -/
instance projection_isAffineHom (i : M.Index) : IsAffineHom (M.projection.app i) :=
  isAffineHom_π_app M.diagram M.cone M.isLimit i

/-- Finite-type arithmetic stages are locally Noetherian. -/
instance stage_isLocallyNoetherian (i : M.Index) : IsLocallyNoetherian (M.diagram.obj i) :=
  LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.from (M.diagram.obj i))

/-- The arithmetic stages are actually of finite presentation. -/
instance stage_locallyOfFinitePresentation (i : M.Index) :
    LocallyOfFinitePresentation (specULiftZIsTerminal.from (M.diagram.obj i)) := inferInstance

end System
end AlgebraicGeometry.Scheme.FinitePresentationEnvelope
