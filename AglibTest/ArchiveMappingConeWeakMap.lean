/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.MappingCone.WeakMap

/-! The weak-map proof retains the actual middle map and original target cone inclusion. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory
open CochainComplex
universe u v
namespace AglibTest.ArchiveMappingConeWeakMap
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L K' L' : CochainComplex A ℤ}

/-- The middle vertical map is the literal original signed cone map. -/
theorem original_middle_cone_map (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g) :
    (mappingConeTriangleShortComplexMap f g a b h).τ₂ =
      CochainComplex.mappingCone.map f g a b h := rfl

/-- Original target inclusions commute with that exact middle cone map. -/
theorem original_cone_target_square (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g) :
    b ≫ CochainComplex.mappingCone.inr g =
      CochainComplex.mappingCone.inr f ≫ CochainComplex.mappingCone.map f g a b h :=
  (mappingConeTriangleShortComplexMap f g a b h).comm₁₂

/-- The original map is weak under the two original endpoint quasi-isomorphisms. -/
theorem original_cone_weak_map (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g) [QuasiIso a] [QuasiIso b] :
    QuasiIso (CochainComplex.mappingCone.map f g a b h) :=
  mappingCone_map_quasiIso f g a b h

end AglibTest.ArchiveMappingConeWeakMap
