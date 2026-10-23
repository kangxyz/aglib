/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericUnitCoordinates
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinBaseChangeIndex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericSectionSupport

/-!
# Finite support for the original generic-unit kernel

An actual Gm section killed by the original small-etale generic direct-image
unit has trivial germs at every component-generic point. On a Noetherian
curve test its nontrivial stalk support is therefore finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {X : Scheme.{u}} [IsNoetherian X] (U : X.Etale) [QuasiCompact U.hom]

/-- The original kernel condition forces triviality at every actual generic stalk. -/
theorem genericUnit_kernel_generic_germs (a : (gm X).obj.obj (op U))
    (ha : (genericArtinUnit X).hom.app (op U) a = 0) (η : genericPoints U.left) :
    U.left.presheaf.germ ⊤ η.val trivial
      ((unitsSections X (op U) a).toMul : Γ(U.left, ⊤)) = 1 := by
  obtain ⟨p, rfl⟩ :=
    (genericArtinBaseChangeIndexEquiv (X := X) (U := U.left) U.hom).surjective η
  rw [genericArtinBaseChangeIndexEquiv_val]
  have h := genericDirectImageUnitCoordinates_unit U a p
  rw [ha] at h
  have hz : genericDirectImageUnitCoordinates U 0 p = 1 := by
    change genericBaseChangeUnitCoordinates U
      ((unitsSections (genericArtinLocus X)
        ((siteBaseChange (genericArtinMap X)).op.obj (op U))) 0).toMul p = 1
    rw [(unitsSections (genericArtinLocus X)
      ((siteBaseChange (genericArtinMap X)).op.obj (op U))).map_zero]
    exact congrFun (map_one (genericBaseChangeUnitCoordinates U)) p
  have hu := h.symm.trans hz
  exact congrArg (fun b : (U.left.presheaf.stalk
    ((pullback.fst U.hom (genericArtinMap X)) p))ˣ =>
      (b : U.left.presheaf.stalk ((pullback.fst U.hom (genericArtinMap X)) p))) hu

/-- The actual kernel unit has finite nontrivial stalk support on a curve test. -/
theorem finite_genericUnit_kernel_support (hdim : topologicalKrullDim U.left ≤ 1)
    (a : (gm X).obj.obj (op U)) (ha : (genericArtinUnit X).hom.app (op U) a = 0) :
    {x : U.left | U.left.presheaf.germ ⊤ x trivial
      ((unitsSections X (op U) a).toMul : Γ(U.left, ⊤)) ≠ 1}.Finite := by
  let : IsNoetherian U.left := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X := U.left) (Y := X) U.hom }
  exact finite_globalUnit_support_of_generic_germs_one U.left hdim
    (unitsSections X (op U) a).toMul (genericUnit_kernel_generic_germs U a ha)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
