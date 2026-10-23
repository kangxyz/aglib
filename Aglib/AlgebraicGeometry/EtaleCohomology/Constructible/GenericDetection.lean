/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.GenericDetection.Represented
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.CoefficientRepresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteSetRepresentation

/-! # Generic detection of finite locally constant abelian sheaves

On every integral scheme, the original adjunction unit to the direct image of
the original generic inverse image is a monomorphism for every finite locally
constant abelian sheaf. The finite etale coefficient representation is produced
from finite local constancy, rather than supplied as an additional hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.GenericDetection

universe u

attribute [local instance] hasSheafifyLarge

private theorem mono_app_of_iso {C D : Type*} [Category* C] [Category* D]
    {G H : C ⥤ D} (α : G ⟶ H) {L M : C} (e : L ≅ M) [Mono (α.app L)] :
    Mono (α.app M) := by
  have h : α.app M = (G.mapIso e).inv ≫ α.app L ≫ (H.mapIso e).hom := by
    simp only [Functor.mapIso_inv, Functor.mapIso_hom]
    rw [← α.naturality e.hom, ← Category.assoc, ← G.map_comp, e.inv_hom_id,
      G.map_id, Category.id_comp]
  rw [h]
  infer_instance

/-- The literal generic adjunction unit detects every finite locally constant
abelian sheaf on an integral scheme, without normality or Noetherianity. -/
theorem mono_genericUnit (X : Scheme.{u}) [IsIntegral X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    Mono ((inverseImageAdjunction (X.fromSpecStalk (genericPoint X))).unit.app F) := by
  let r := CoefficientRepresentation.ofFiniteLocallyConstant F (stacks03RV X) hF
  have := r.finite
  have := r.etale
  have := r.commutative
  have : Mono ((inverseImageAdjunction (X.fromSpecStalk (genericPoint X))).unit.app
      (representedSheaf r.group)) := mono_representedGenericUnit X r.group
  exact mono_app_of_iso
    (inverseImageAdjunction (X.fromSpecStalk (genericPoint X))).unit r.iso

end AlgebraicGeometry.Scheme.EtaleCohomology.GenericDetection
