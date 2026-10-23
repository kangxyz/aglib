/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.DirectImageDivisibility

/-!
# Divisibility transfer on original sheaf cohomology

The endpoints use the original coefficient maps on original Ext cohomology.
Source and target Ext universes, and all derived-category universes, are independent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w' dS dX dA

private theorem bijective_nsmul_iff {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (n : ℕ) :
    Function.Bijective (fun b : B => n • b) ↔
      Function.Bijective (fun a : A => n • a) := by
  constructor
  · intro h
    have he : (fun a : A => n • a) = e.symm ∘ (fun b : B => n • b) ∘ e := by
      funext a
      simp
    rw [he]
    exact e.symm.bijective.comp (h.comp e.bijective)
  · intro h
    have he : (fun b : B => n • b) = e ∘ (fun a : A => n • a) ∘ e.symm := by
      funext b
      simp
    rw [he]
    exact e.bijective.comp (h.comp e.symm.bijective)

/-- Scalar invertibility in native derived sections is equivalent to bijectivity
of the literal original coefficient endomorphism on original cohomology. -/
theorem isIso_nsmul_homology_derivedGlobalSections_iff
    {X : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]
    (L : AbelianSheaf.{u, u + 1} X) (q n : ℕ) :
    IsIso (n • 𝟙 ((homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      ((derivedGlobalSections X).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj L)))) ↔
      Function.Bijective (Sheaf.H.map (n • 𝟙 L) q) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have he : (Sheaf.H.map (n • 𝟙 L) q : Sheaf.H.{w} L q → Sheaf.H.{w} L q) =
      fun x => n • x := funext (cohomology_map_nsmul_id L q n)
  rw [he]
  exact bijective_nsmul_iff (cohomologyDerivedGlobalSectionsAddEquiv L q) n

/-- Original-H divisibility transfer through actual direct image, using only
positive higher-image divisibility and consecutive source cohomology degrees. -/
theorem cohomology_directImage_nsmul_bijective
    {S X : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dA} AddCommGrpCat.{u + 1}]
    (f : S ⟶ X) (L : AbelianSheaf.{u, u + 1} S) (n q : ℕ)
    (hh : ∀ k : ℕ, 1 ≤ k → IsIso (n • 𝟙 ((higherDirectImage f k).obj L)))
    (hq : Function.Bijective (Sheaf.H.map (n • 𝟙 L) q))
    (hq' : Function.Bijective (Sheaf.H.map (n • 𝟙 L) (q + 1))) :
    Function.Bijective (Sheaf.H.map (n • 𝟙 ((directImage f).obj L)) (q + 1)) := by
  let := (isIso_nsmul_homology_derivedGlobalSections_iff L q n).mpr hq
  let := (isIso_nsmul_homology_derivedGlobalSections_iff L (q + 1) n).mpr hq'
  apply (isIso_nsmul_homology_derivedGlobalSections_iff
    ((directImage f).obj L) (q + 1) n).mp
  exact isIso_nsmul_homology_derivedGlobalSections_directImage f L n hh
    (q : ℤ) ((q + 1 : ℕ) : ℤ) (by omega)

end AlgebraicGeometry.Scheme.EtaleCohomology
