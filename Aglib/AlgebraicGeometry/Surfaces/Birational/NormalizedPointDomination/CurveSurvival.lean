/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveStalk
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.ResidueTranscendence

/-!
# Original maps of surviving curves

Proper-image embeddings compose on their actual geometric values. A surviving
curve's generic point maps to the original generic point. Transcendence of
the selected residue is retained by the original stalk and residue maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- Actual proper images compose, retaining the literal composite projection. -/
theorem Hom.irreducibleClosedImage_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g]
    (C : IrreducibleCloseds X) :
    (f ≫ g).irreducibleClosedImage C = g.irreducibleClosedImage (f.irreducibleClosedImage C) := by
  apply SetLike.coe_injective
  change (fun x ↦ g (f x)) '' (C : Set X) = g '' (f '' (C : Set X))
  exact (Set.image_image g f (C : Set X)).symm

/-- The selected generic point is retained by the original projection when
its actual proper image is the selected old curve. -/
theorem Hom.genericPoint_image_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (C : IrreducibleCloseds X) (D : IrreducibleCloseds Y)
    (h : f.irreducibleClosedImage C = D) :
    f C.isIrreducible.genericPoint = D.isIrreducible.genericPoint := by
  have hc := f.isGenericPoint_irreducibleClosedImage C
  rw [h] at hc
  exact hc.eq (D.isIrreducible.isGenericPoint_genericPoint D.isClosed)

namespace NormalizedPointDomination

/-- Pulling back the retained stalk element along the actual common-model
projection preserves its residue transcendence over the old closed point.
The scalar action is the original composite residue-field map. -/
theorem transcendental_residue_stalkMap
    {X Y S : Scheme.{u}} (g : X ⟶ Y) (q : Y ⟶ S) (z : X)
    (u : Y.presheaf.stalk (g z))
    (hu : letI := (q.residueFieldMap (g z)).hom.toAlgebra
      Transcendental (S.residueField (q (g z))) (Y.residue (g z) u)) :
    letI : Algebra (S.residueField (q (g z))) (X.residueField z) :=
      ((g ≫ q).residueFieldMap z).hom.toAlgebra
    Transcendental (S.residueField (q (g z))) (X.residue z (g.stalkMap z u)) := by
  let K := S.residueField (q (g z))
  let L := Y.residueField (g z)
  let E := X.residueField z
  let : Algebra K L := (q.residueFieldMap (g z)).hom.toAlgebra
  let : Algebra K E := ((g ≫ q).residueFieldMap z).hom.toAlgebra
  have hr : X.residue z (g.stalkMap z u) =
      g.residueFieldMap z (Y.residue (g z) u) :=
    (congrArg (fun k : Y.presheaf.stalk (g z) ⟶ E ↦ k u)
      (residue_residueFieldMap g z)).symm
  rw [hr]
  apply hu.ringHom_of_comp_eq (RingHom.id K) (g.residueFieldMap z).hom
    Function.surjective_id (g.residueFieldMap z).hom.injective
  change ((g ≫ q).residueFieldMap z).hom.comp (RingHom.id K) =
    (g.residueFieldMap z).hom.comp (q.residueFieldMap (g z)).hom
  rw [RingHom.comp_id]
  exact congrArg CommRingCat.Hom.hom (residueFieldMap_comp g q z)

end NormalizedPointDomination
end AlgebraicGeometry.Scheme
