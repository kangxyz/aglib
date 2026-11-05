/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers

/-! # Actual class transport along an isomorphic triangle

The original pullback and the actual inverse-image composition comparison
transport a class between two isomorphic models over the same coefficient
scheme. Bijectivity is proved, not assumed, in every degree.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e
attribute [local instance] hasSheafifyLarge

/-- The coefficient comparison of an actual commuting isomorphic triangle. -/
def isoTriangleCoefficientIso {T Y Z : Scheme.{u}}
    (b : Y ⟶ T) (b₀ : Z ⟶ T) (E : Z ≅ Y) (h : E.hom ≫ b = b₀)
    (F : AbelianSheaf.{u, u + 1} T) :
    (inverseImage E.hom).obj ((inverseImage b).obj F) ≅ (inverseImage b₀).obj F :=
  (inverseImageComp b E.hom).symm.app F ≪≫
    eqToIso (congrArg (fun f : Z ⟶ T => (inverseImage f).obj F) h)

/-- The literal original pullback followed by its triangle comparison is bijective. -/
theorem isoTriangleTransfer_bijective {T Y Z : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]
    (b : Y ⟶ T) (b₀ : Z ⟶ T) (E : Z ≅ Y) (h : E.hom ≫ b = b₀)
    (F : AbelianSheaf.{u, u + 1} T) (q : ℕ) :
    Function.Bijective (cohomologyTransfer E.hom
      (isoTriangleCoefficientIso b b₀ E h F).hom q) := by
  exact (cohomologyMapIso_bijective (isoTriangleCoefficientIso b b₀ E h F) q).comp
    (cohomologyPullback_bijective_of_isEquivalence E.hom ((inverseImage b).obj F) q)

/-- Construct a representative on the second model returning to any original class. -/
theorem exists_isoTriangle_class {T Y Z : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]
    (b : Y ⟶ T) (b₀ : Z ⟶ T) (E : Z ≅ Y) (h : E.hom ≫ b = b₀)
    (F : AbelianSheaf.{u, u + 1} T) (q : ℕ)
    (a : Sheaf.H.{e} ((inverseImage b₀).obj F) q) :
    ∃ c : Sheaf.H.{e} ((inverseImage b).obj F) q,
      cohomologyTransfer E.hom (isoTriangleCoefficientIso b b₀ E h F).hom q c = a :=
  (isoTriangleTransfer_bijective b b₀ E h F q).surjective a

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
