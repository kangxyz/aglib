/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.CategoryTheory.Abelian.Ext.OriginalComparison

/-! # Original sheaf cohomology under exact direct image

The comparison uses the native exact-adjunction Ext equivalence and the original
inverse-image constant-sheaf isomorphism. Its forward map is precisely original
cohomology pullback followed by the original adjunction counit. No arbitrary
base-change pullback is asserted invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian



namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]
  (f : X ⟶ S) [PreservesFiniteColimits (directImage f)]

/-- Original cohomology of an exact direct image agrees with cohomology on the source,
with independent Ext universes on the two schemes. -/
def cohomologyDirectImageAddEquiv (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Sheaf.H.{wS} ((directImage f).obj F) q ≃+ Sheaf.H.{wX} F q :=
  Adjunction.originalExtSourceComparison (inverseImageAdjunction f)
    ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q

/-- The actual comparison is original pullback followed by the original counit map. -/
theorem cohomologyDirectImageAddEquiv_apply
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (a : Sheaf.H.{wS} ((directImage f).obj F) q) :
    cohomologyDirectImageAddEquiv f F q a =
      Sheaf.H.map ((inverseImageAdjunction f).counit.app F) q
        (cohomologyPullback f ((directImage f).obj F) q a) :=
  Adjunction.originalExtSourceComparison_apply (inverseImageAdjunction f)
    ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q a

/-- The exact-image comparison sends the original unit map to the original pullback. -/
theorem cohomologyDirectImageAddEquiv_unit
    (F : AbelianSheaf.{u, u + 1} S) (q : ℕ) (x : Sheaf.H.{wS} F q) :
    cohomologyDirectImageAddEquiv f ((inverseImage f).obj F) q
        (Sheaf.H.map ((inverseImageAdjunction f).unit.app F) q x) =
      cohomologyPullback f F q x :=
  Adjunction.originalExtSourceComparison_unit (inverseImageAdjunction f)
    ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) F q x

/-- Coefficient naturality retains the original maps on both cohomology groups. -/
theorem cohomologyDirectImageAddEquiv_naturality
    {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{wS} ((directImage f).obj F) q) :
    cohomologyDirectImageAddEquiv f G q (Sheaf.H.map ((directImage f).map a) q x) =
      Sheaf.H.map a q (cohomologyDirectImageAddEquiv f F q x) :=
  Adjunction.originalExtSourceComparison_naturality (inverseImageAdjunction f)
    ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) a q x

end AlgebraicGeometry.Scheme.EtaleCohomology
