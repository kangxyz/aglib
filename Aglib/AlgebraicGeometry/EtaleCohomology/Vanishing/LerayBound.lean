/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.BoundedHypercohomology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure

/-! # Original cohomology bounds from higher direct images

A finite bound on the original higher direct images and a cohomology bound
on their actual coefficients give the sum bound on original source
cohomology. The proof uses the native derived single/homology comparisons,
finite Postnikov bounds, and the actual derived direct-image/global-sections
composition isomorphism. It does not introduce a second spectral sequence or
assume any geometric, torsion or properness condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u eX eS dX dS dA

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]

/-- A bound on the original natural-degree higher direct images bounds the
actual D+ direct image of the original degree-zero single. -/
theorem isLE_derivedDirectImage_single_of_higher
    (f : X ⟶ S) (F : AbelianSheaf.{u, u + 1} X) (d : ℕ)
    (hR : ∀ q : ℕ, d < q → IsZero ((higherDirectImage f q).obj F)) :
    ((derivedDirectImage f).obj
      ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)).IsLE (d : ℤ) := by
  rw [← isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro q hq
  change IsZero ((homologyFunctor (AbelianSheaf.{u, u + 1} S) q).obj
    ((derivedDirectImage f).obj
      ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)))
  have hqn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
  have hz := (hR q.toNat (by omega)).of_iso
    ((higherDirectImageIso f q.toNat).app F).symm
  change IsZero ((homologyFunctor (AbelianSheaf.{u, u + 1} S) (q.toNat : ℤ)).obj
    ((derivedDirectImage f).obj
      ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))) at hz
  simpa only [hqn] using hz

section Sections

variable [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]

/-- Bounds on original higher direct images and their original cohomology
add in the actual derived global sections of the source single. -/
theorem isLE_derivedGlobalSections_single_of_leray
    (f : X ⟶ S) (F : AbelianSheaf.{u, u + 1} X) (d N : ℕ)
    (hR : ∀ q : ℕ, d < q → IsZero ((higherDirectImage f q).obj F))
    (hH : ∀ n : ℕ, n ≤ d → ∀ q : ℕ, N < q →
      Subsingleton (Sheaf.H.{eS} ((higherDirectImage f n).obj F) q)) :
    ((derivedGlobalSections X).obj
      ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)).IsLE ((N : ℤ) + d) := by
  let K := (derivedDirectImage f).obj
    ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)
  let : K.IsGE 0 := (directImage f).rightDerivedFunctorPlus_isGE _ 0
  let : K.IsLE (d : ℤ) := isLE_derivedDirectImage_single_of_higher f F d hR
  let : ((derivedGlobalSections S).obj K).IsLE ((N : ℤ) + d) := by
    apply isLE_derivedGlobalSections_of_homology_H K 0 (d : ℤ) N
    intro n hn hnd q hq
    have hnn : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    let : Subsingleton (Sheaf.H.{eS} ((higherDirectImage f n.toNat).obj F) q) :=
      hH n.toNat (by omega) q hq
    have hz : Subsingleton (Sheaf.H.{eS}
        ((homologyFunctor (AbelianSheaf.{u, u + 1} S) (n.toNat : ℤ)).obj K) q) :=
      (cohomologyMapIso_bijective
        ((higherDirectImageIso f n.toNat).app F) q).surjective.subsingleton
    simpa only [hnn] using hz
  let E : (derivedGlobalSections S).obj K ≅
      (derivedGlobalSections X).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F) :=
    (derivedDirectImageGlobalSectionsIso f).app
      ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)
  exact TStructure.t.isLE_of_iso E ((N : ℤ) + d)

/-- The sum of the displayed higher-image and coefficient cohomology bounds
annihilates original source cohomology. All Ext and derived-model universes
are independent, and no geometric condition is hidden in the premises. -/
theorem subsingleton_H_of_leray_bounds
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    (f : X ⟶ S) (F : AbelianSheaf.{u, u + 1} X) (d N : ℕ)
    (hR : ∀ n : ℕ, d < n → IsZero ((higherDirectImage f n).obj F))
    (hH : ∀ n : ℕ, n ≤ d → ∀ q : ℕ, N < q →
      Subsingleton (Sheaf.H.{eS} ((higherDirectImage f n).obj F) q))
    (q : ℕ) (hq : N + d < q) : Subsingleton (Sheaf.H.{eX} F q) := by
  let K := (derivedGlobalSections X).obj
    ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)
  let : K.IsLE ((N : ℤ) + d) :=
    isLE_derivedGlobalSections_single_of_leray f F d N hR hH
  have hz := isZero_homology_of_isLE K ((N : ℤ) + d) (q : ℤ) (by omega)
  let : Subsingleton ((homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj K) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hz
  exact (cohomologyDerivedGlobalSectionsAddEquiv F q).injective.subsingleton

end Sections

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
