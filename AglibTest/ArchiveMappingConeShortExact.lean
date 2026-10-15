/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.MappingCone.ShortExact

/-! Actual coefficient cone maps and genuine inherited short exact sequences. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex
universe u v u' v'
namespace AglibTest.ArchiveMappingConeShortExact
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {D : Type u'} [Category.{v'} D]
variable {F G : D ⥤ CochainComplex A ℤ}

/-- The map is exactly the original cone map of the actual naturality square. -/
theorem original_cone_map (α : F ⟶ G) {K L : D} (g : K ⟶ L) :
    (mappingConeNatTransFunctor α).map g =
      CochainComplex.mappingCone.map _ _ (F.map g) (G.map g) (α.naturality g).symm := rfl

variable [Preadditive D] [F.Additive] [G.Additive]

/-- The original endpoint short exactness produces genuine cone short exactness. -/
theorem original_cone_short_exact (α : F ⟶ G) (S : ShortComplex D)
    (hF : (S.map F).ShortExact) (hG : (S.map G).ShortExact) :
    (S.map (mappingConeNatTransFunctor α)).ShortExact :=
  mappingConeNatTransFunctor_shortExact α S hF hG

end AglibTest.ArchiveMappingConeShortExact
