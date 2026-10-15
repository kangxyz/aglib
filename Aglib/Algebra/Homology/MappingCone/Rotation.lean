/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.MappingCone.WeakMap
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Actual cone reassembly after two native triangle rotations

Double rotation of the original signed cone triangle identifies the cone
of its original projection, shifted by minus one, with the original middle
complex up to homotopy. The native homotopy-category triangle isomorphism
and native lift of an isomorphism give an actual homotopy equivalence.
An actual replacement of the first cone therefore reassembles to an actual
chain map to the original middle complex. No homology-only object comparison
or new derived object is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

namespace CochainComplex.mappingCone

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [hzero : HasZeroObject C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

include hzero

/-- The native homotopy-category cancellation isomorphism, with the
source the original cone projection's actual mapping cocone. -/
def rotateTwiceHomotopyIso :
    (HomotopyCategory.quotient C (.up ℤ)).obj (mappingCocone (triangle φ).mor₃) ≅
      (HomotopyCategory.quotient C (.up ℤ)).obj L := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let S := triangleh (triangle φ).mor₃
  let T := (triangleh φ).rotate.rotate
  let e := Pretriangulated.isoTriangleOfIso₁₂ S T
    (HomotopyCategory.mappingCone_triangleh_distinguished _)
    (Pretriangulated.rot_of_distTriang _
      (Pretriangulated.rot_of_distTriang _
        (HomotopyCategory.mappingCone_triangleh_distinguished φ)))
    (Iso.refl _) ((q.commShiftIso (1 : ℤ)).app K) (by simp [S, T, q])
  let e₃ : q.obj (mappingCone (triangle φ).mor₃) ≅ q.obj (L⟦(1 : ℤ)⟧) :=
    Triangle.π₃.mapIso e ≪≫ ((q.commShiftIso (1 : ℤ)).app L).symm
  exact (q.commShiftIso (-1 : ℤ)).app (mappingCone (triangle φ).mor₃) ≪≫
    (CategoryTheory.shiftFunctor (HomotopyCategory C (.up ℤ)) (-1 : ℤ)).mapIso e₃ ≪≫
    ((q.commShiftIso (-1 : ℤ)).app (L⟦(1 : ℤ)⟧)).symm ≪≫
    q.mapIso ((shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1 : ℤ)
      (by omega)).app L)

/-- An actual homotopy equivalence cancels the twice-rotated native cone.
Its source is the unchanged native mapping cocone of the original projection. -/
def rotateTwiceHomotopyEquiv : HomotopyEquiv (mappingCocone (triangle φ).mor₃) L :=
  HomotopyCategory.homotopyEquivOfIso (rotateTwiceHomotopyIso φ)

/-- The chosen actual cancellation map represents exactly the displayed
native homotopy-category cancellation isomorphism. -/
theorem quotient_rotateTwiceHomotopyEquiv_hom :
    (HomotopyCategory.quotient C (.up ℤ)).map (rotateTwiceHomotopyEquiv φ).hom =
      (rotateTwiceHomotopyIso φ).hom :=
  HomotopyCategory.quotient_map_out _

/-- Reassemble an actual map to the original cone into an actual map to
the original middle complex, using the literal native cone-square map. -/
def reassemblyMap {Q : CochainComplex C ℤ} (s : Q ⟶ mappingCone φ) :
    mappingCocone (s ≫ (triangle φ).mor₃) ⟶ L :=
  (map (s ≫ (triangle φ).mor₃) (triangle φ).mor₃ s (𝟙 _)
    (by simp))⟦(-1 : ℤ)⟧' ≫ (rotateTwiceHomotopyEquiv φ).hom

/-- The orientation and factors of reassembly retain the original map
into the cone, original cone projection, native cone map and actual cancellation. -/
theorem reassemblyMap_eq {Q : CochainComplex C ℤ} (s : Q ⟶ mappingCone φ) :
    reassemblyMap φ s =
      (map (s ≫ (triangle φ).mor₃) (triangle φ).mor₃ s (𝟙 _)
        (by simp))⟦(-1 : ℤ)⟧' ≫ (rotateTwiceHomotopyEquiv φ).hom := rfl

end Preadditive

section Terms

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K L Q : CochainComplex C ℤ} (φ : K ⟶ L) (s : Q ⟶ mappingCone φ)

/-- Native term transport for reassembly: the shifted cone has exactly the
original replacement term and original source term as its biproduct factors. -/
def reassemblyTermIso (i : ℤ) :
    (mappingCocone (s ≫ (triangle φ).mor₃)).X i ≅ Q.X i ⊞ K.X i :=
  (mappingCone (s ≫ (triangle φ).mor₃)).shiftFunctorObjXIso
      (-1 : ℤ) i (i - 1) (by omega) ≪≫
    homotopyCofiber.XIsoBiprod (s ≫ (triangle φ).mor₃) (i - 1) i (by
      change (i - 1) + 1 = i
      omega) ≪≫
    biprod.mapIso (Iso.refl _) (K.shiftFunctorObjXIso (1 : ℤ) (i - 1) i (by omega))

end Terms

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L Q : CochainComplex C ℤ} (φ : K ⟶ L) (s : Q ⟶ mappingCone φ)

/-- A genuine quasi-isomorphism to the original cone reassembles to a
genuine quasi-isomorphism to the original middle complex. -/
theorem reassemblyMap_quasiIso [QuasiIso s] : QuasiIso (reassemblyMap φ s) := by
  let t := map (s ≫ (triangle φ).mor₃) (triangle φ).mor₃ s (𝟙 _) (by simp)
  let : QuasiIso t := mappingCone_map_quasiIso _ _ s (𝟙 _) (by simp)
  change QuasiIso (t⟦(-1 : ℤ)⟧' ≫ (rotateTwiceHomotopyEquiv φ).hom)
  infer_instance

end Abelian

end CochainComplex.mappingCone
