/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Bounds
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ClosedSupportUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.CohomologyComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # Finite-window bounds from original coefficient cohomology

Original sheaf cohomology bounds on the actual homology sheaves of a bounded
native D+ object give an upper bound on its actual derived global sections.
The proof uses the existing finite Postnikov reduction, not a new spectral
sequence or a choice of terms satisfying the coefficient hypotheses.

For homology supported on a displayed closed subscheme, the literal closed
adjunction unit and finite direct-image cohomology reduce these inputs to the
restrictions to that subscheme. The last theorem applies the actual triangle
long exact sequence and returns original `Sheaf.H`. These are homological
suppliers for dimension induction; geometric support, torsion and dimension
bounds are neither asserted nor hidden in the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u eX eZ dX dA

attribute [local instance] hasSheafifyLarge

section ClosedSupport

variable {X Z : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]

/-- Original cohomology of a coefficient supported on a closed subscheme
vanishes whenever the cohomology of its actual closed restriction vanishes.
The support condition is on original geometric stalks, and the Ext universes
on the two schemes are independent. -/
theorem subsingleton_H_of_closedSupport (i : Z ⟶ X) [IsClosedImmersion i]
    (F : AbelianSheaf.{u, u + 1} X)
    (hsupport : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ X),
      (∀ z : Spec (.of Ω) ⟶ Z, z ≫ i ≠ s) →
        IsZero (coefficientFiber s F))
    (q : ℕ) (hH : Subsingleton (Sheaf.H.{eZ} ((inverseImage i).obj F) q)) :
    Subsingleton (Sheaf.H.{eX} F q) := by
  let : IsIso ((inverseImageAdjunction i).unit.app F) :=
    Curves.closedSupportUnit_isIso i F hsupport
  let e : F ≅ (directImage i).obj ((inverseImage i).obj F) :=
    asIso ((inverseImageAdjunction i).unit.app F)
  let : Subsingleton (Sheaf.H.{eZ} ((inverseImage i).obj F) q) := hH
  let : Subsingleton (Sheaf.H.{eX}
      ((directImage i).obj ((inverseImage i).obj F)) q) :=
    (Finite.finiteCohomologyDirectImageAddEquiv.{u, eZ, eX}
      i ((inverseImage i).obj F) q).injective.subsingleton
  exact (cohomologyMapIso_bijective e q).injective.subsingleton

end ClosedSupport

section DerivedSections

variable {X : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- A bound on the original Ext cohomology is an upper bound on actual
derived sections of the original degree-zero single. -/
theorem isLE_derivedGlobalSections_single_of_H
    (F : AbelianSheaf.{u, u + 1} X) (N : ℕ)
    (hH : ∀ q : ℕ, N < q → Subsingleton (Sheaf.H.{eX} F q)) :
    ((derivedGlobalSections X).obj
      ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)).IsLE (N : ℤ) := by
  rw [← isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro q hq
  change IsZero ((homologyFunctor AddCommGrpCat.{u + 1} q).obj
    ((derivedGlobalSections X).obj
      ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)))
  have hqnat : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
  let : Subsingleton (Sheaf.H.{eX} F q.toNat) := hH q.toNat (by omega)
  have hzero : IsZero ((homologyFunctor AddCommGrpCat.{u + 1} (q.toNat : ℤ)).obj
      ((derivedGlobalSections X).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr
      (cohomologyDerivedGlobalSectionsAddEquiv F q.toNat).surjective.subsingleton
  simpa only [hqnat] using hzero

/-- A common original cohomology bound on the finitely many actual homology
sheaves adds to the upper amplitude of the original D+ object. The lower
bound is used only for the finite Postnikov argument. -/
theorem isLE_derivedGlobalSections_of_homology_H
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X))
    (a b : ℤ) [K.IsGE a] [K.IsLE b] (N : ℕ)
    (hH : ∀ k : ℤ, a ≤ k → k ≤ b → ∀ q : ℕ, N < q →
      Subsingleton (Sheaf.H.{eX}
        ((homologyFunctor (AbelianSheaf.{u, u + 1} X) k).obj K) q)) :
    ((derivedGlobalSections X).obj K).IsLE ((N : ℤ) + b) := by
  apply isLE_obj_of_homology_single_zero_bounds
    (derivedGlobalSections X) TStructure.t K a b (N : ℤ)
  intro k hak hkb
  exact isLE_derivedGlobalSections_single_of_H _ N (hH k hak hkb)

/-- Closed support of the actual homology sheaves reduces a finite-window
derived-sections bound to original cohomology on the displayed closed scheme.
No condition on terms of an injective representative is used. -/
theorem isLE_derivedGlobalSections_of_closedSupport_homology_H
    {Z : Scheme.{u}} [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X))
    (a b : ℤ) [K.IsGE a] [K.IsLE b] (N : ℕ)
    (hsupport : ∀ k : ℤ, a ≤ k → k ≤ b →
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      (∀ z : Spec (.of Ω) ⟶ Z, z ≫ i ≠ s) →
        IsZero (coefficientFiber s
          ((homologyFunctor (AbelianSheaf.{u, u + 1} X) k).obj K)))
    (hH : ∀ k : ℤ, a ≤ k → k ≤ b → ∀ q : ℕ, N < q →
      Subsingleton (Sheaf.H.{eZ} ((inverseImage i).obj
        ((homologyFunctor (AbelianSheaf.{u, u + 1} X) k).obj K)) q)) :
    ((derivedGlobalSections X).obj K).IsLE ((N : ℤ) + b) := by
  apply isLE_derivedGlobalSections_of_homology_H K a b N
  intro k hak hkb q hq
  exact subsingleton_H_of_closedSupport i _ (hsupport k hak hkb) q (hH k hak hkb q hq)

/-- In an actual distinguished triangle whose first vertex is the original
single of a sheaf, upper bounds on derived sections of the other two vertices
give vanishing of original cohomology. The third vertex contributes one
additional degree, as in the actual triangle long exact sequence. -/
theorem subsingleton_H_of_triangle_bounds
    (T : Triangle (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)))
    (hT : T ∈ distTriang _)
    (F : AbelianSheaf.{u, u + 1} X)
    (eF : T.obj₁ ≅ (singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)
    (N₂ N₃ : ℤ)
    [((derivedGlobalSections X).obj T.obj₂).IsLE N₂]
    [((derivedGlobalSections X).obj T.obj₃).IsLE N₃]
    (q : ℕ) (h₂ : N₂ < (q : ℤ)) (h₃ : N₃ + 1 < (q : ℤ)) :
    Subsingleton (Sheaf.H.{eX} F q) := by
  let S := (derivedGlobalSections X).mapTriangle.obj T
  have hS : S ∈ distTriang _ := (derivedGlobalSections X).map_distinguished T hT
  let H := homologyFunctor AddCommGrpCat.{u + 1} 0
  have hzero₂ := isZero_homology_of_isLE
    ((derivedGlobalSections X).obj T.obj₂) N₂ (q : ℤ) h₂
  have hzero₃ := isZero_homology_of_isLE
    ((derivedGlobalSections X).obj T.obj₃) N₃ ((q : ℤ) - 1) (by omega)
  have hzero₁ : IsZero ((homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      ((derivedGlobalSections X).obj T.obj₁)) :=
    (H.homologySequence_exact₁ S hS ((q : ℤ) - 1) (q : ℤ) (by omega)).isZero_X₂_iff.mpr
      ⟨hzero₃.eq_of_src _ _, hzero₂.eq_of_tgt _ _⟩
  have hzero : IsZero ((homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      ((derivedGlobalSections X).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))) :=
    hzero₁.of_iso ((homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).mapIso
      ((derivedGlobalSections X).mapIso eF)).symm
  let : Subsingleton ((homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      ((derivedGlobalSections X).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hzero
  exact (cohomologyDerivedGlobalSectionsAddEquiv F q).injective.subsingleton

end DerivedSections

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
