/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ModificationCone

/-! # Independent source and boundary bounds for an actual modification

The original derived adjunction unit and its actual cone reduce torsion
cohomology on the target to cohomology on the source and on a displayed
closed boundary. The bounds are independent: a source bound `M`, a boundary
bound `N`, and a higher-image bound `a` give `max M (N + a + 1)`.

In particular, geometric codimension must enter through the boundary bound;
it is not lost by replacing it with the source bound. This is the homological
step used in the sharp dimension argument of Stacks, Tag 095U. The theorem
does not assert the existence of a codimension-two modification. It requires
neither properness, normality, a field, nor monicity of the sheaf unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u eX eY eZ

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Independent original cohomology bounds on a modification source and its
closed boundary give a bound on the original target coefficient. The cone is
constructed from the literal adjunction unit, not supplied as extra data.
All three original Ext universes remain independent. -/
theorem subsingleton_H_of_modification_bounds
    {Y X U Z : Scheme.{u}}
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    (b : Y ⟶ X) [QuasiCompact b] [QuasiSeparated b]
    (j : U ⟶ X) [IsOpenImmersion j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hcomp : Set.range j = (Set.range i)ᶜ) [IsIso (pullback.fst j b)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (a M N : ℕ)
    (hR : ∀ r : ℕ, a < r →
      IsZero ((higherDirectImage b r).obj ((inverseImage b).obj F)))
    (hY : ∀ r : ℕ, M < r →
      Subsingleton (Sheaf.H.{eY} ((inverseImage b).obj F) r))
    (hZ : ∀ G : AbelianSheaf.{u, u + 1} Z, IsTorsion Z G →
      ∀ r : ℕ, N < r → Subsingleton (Sheaf.H.{eZ} G r))
    (q : ℕ) (hqY : M < q) (hqZ : N + a + 1 < q) :
    Subsingleton (Sheaf.H.{eX} F q) := by
  obtain ⟨Q, v, w, hT, hQge, hQle, hQtorsion, hQsupport⟩ :=
    exists_derivedImageSingleUnit_cone b j i hcomp F hF a hR
  let T := Triangle.mk (derivedImageSingleUnit b F) v w
  let : Q.IsGE (-1) := hQge
  let : Q.IsLE (a : ℤ) := hQle
  let : ((derivedGlobalSections X).obj T.obj₂).IsLE (M : ℤ) := by
    let : ((derivedGlobalSections Y).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj
          ((inverseImage b).obj F))).IsLE (M : ℤ) :=
      isLE_derivedGlobalSections_single_of_H _ M hY
    let E : (derivedGlobalSections Y).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj ((inverseImage b).obj F)) ≅
          (derivedGlobalSections X).obj T.obj₂ :=
      ((derivedDirectImageGlobalSectionsIso b).app
        ((singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj ((inverseImage b).obj F))).symm
    exact TStructure.t.isLE_of_iso E (M : ℤ)
  let : ((derivedGlobalSections X).obj T.obj₃).IsLE ((N : ℤ) + a) := by
    apply isLE_derivedGlobalSections_of_closedSupport_homology_H i Q (-1) (a : ℤ) N
    · exact fun n _ _ => hQsupport n
    · intro n _ _ r hr
      exact hZ _ ((hQtorsion n).inverseImage i) r hr
  exact subsingleton_H_of_triangle_bounds T hT F (Iso.refl _)
    (M : ℤ) ((N : ℤ) + a) q (by omega) (by omega)

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
