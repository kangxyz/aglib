/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.FiniteSurjectiveDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.HigherImageConstructibleComposition
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.ClosedSubschemeReduction

/-! # Projective constructibility from the geometric curve-family theorem

The geometric input is constructibility for every proper morphism over a
Noetherian target whose actual field-valued fibres have dimension at most one,
for every constructible coefficient and every degree. It is not supplied here.

Induction on the actual number of projective-line factors constructs the
product case using the original finite-diagonal composition theorem. Pullback
of binary-form multiplication gives a finite surjection onto an arbitrary
closed projective subscheme. Finite direct image and the actual finite-cover
unit/cokernel degree induction descend the result. Proper modification descent
is not assumed or concluded, so arbitrary proper constructibility remains
separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

private theorem higherImage_finite_constructible
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsFinite f]
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((higherDirectImage f q).obj F) := by
  cases q with
  | zero =>
    exact (Constructible.isConstructible_iff_of_iso
      ((directImage f).rightDerivedZeroIsoSelf.app F)).mpr
        (Finite.isConstructible_directImage_of_isNoetherian f hF)
  | succ q =>
    exact ObjectProperty.prop_of_isZero (Constructible.IsConstructible (X := S))
      (Finite.isZero_higherDirectImage_obj_of_isFinite f F (q + 1) (Nat.succ_pos q))

variable
  (hcurve : ∀ {Y T : Scheme.{u}} [IsNoetherian T] (g : Y ⟶ T) [IsProper g],
    (∀ (K : Type u) [Field K] (η : Spec (.of K) ⟶ T),
      topologicalKrullDim (pullback g η : Scheme.{u}) ≤ 1) →
    ∀ (q : ℕ) (F : AbelianSheaf.{u, u + 1} Y), Constructible.IsConstructible F →
      Constructible.IsConstructible ((higherDirectImage g q).obj F))
  (R : Type u) [CommRing R] [IsNoetherianRing R]

private theorem product_noetherian (n : ℕ) : IsNoetherian (source R n) := by
  have : IsLocallyNoetherian (source R n) :=
    LocallyOfFiniteType.isLocallyNoetherian (structureMap R n)
  have : CompactSpace (source R n) :=
    QuasiCompact.compactSpace_of_compactSpace (structureMap R n)
  exact ⟨⟩

include hcurve

/-- The actual product-length induction uses proper curve projections and
only the finite cohomological diagonal for each original composite. -/
theorem higherDirectImage_binaryProduct_isConstructible_of_curves (n : ℕ) :
    ∀ (q : ℕ) (F : AbelianSheaf.{u, u + 1} (source R n)),
      Constructible.IsConstructible F →
      Constructible.IsConstructible ((higherDirectImage (structureMap R n) q).obj F) := by
  induction n with
  | zero =>
    intro q F hF
    exact higherImage_finite_constructible (𝟙 (Spec (.of R))) q F hF
  | succ n ih =>
    intro q F hF
    have : IsNoetherian (source R n) := product_noetherian R n
    have htail (j : ℕ) : Constructible.IsConstructible
        ((higherDirectImage (tailProjection R n) j).obj F) := by
      apply hcurve (tailProjection R n) ?_ j F hF
      intro K _ η
      have h := finite_tailProjection_geometricFiber_dimension_le_one R n
        (𝟙 (source R (n + 1))) K η
      rw [Category.id_comp] at h
      exact h
    rw [← tailProjection_over R n]
    apply higherDirectImage_isConstructible_of_composition_diagonal
      (structureMap R n) (tailProjection R n) F q
    intro j _
    exact ih (q - j) _ (htail j)

/-- A closed projective source has constructible original higher images once
the genuine proper relative-curve theorem has been supplied. The finite cover,
its original coefficient unit and its quotient are all constructed. -/
theorem higherDirectImage_closedProjective_isConstructible_of_curves
    {X : Scheme.{u}} (n : ℕ)
    (j : X ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))) [IsClosedImmersion j]
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible
      ((higherDirectImage (j ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1)))) q).obj F) := by
  let f := j ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1)))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  obtain ⟨Z, p, i, hp, hs, hi, hbase⟩ :=
    exists_finiteSurjective_closedProductCover R n j
  have : IsFinite p := hp
  have : Surjective p := hs
  have : IsClosedImmersion i := hi
  apply higherDirectImage_isConstructible_of_finiteSurjective f p ?_ q F hF
  intro k G hG
  have : IsNoetherian (source R n) := product_noetherian R n
  have hGi : Constructible.IsConstructible ((directImage i).obj G) :=
    Finite.isConstructible_directImage_of_isNoetherian i hG
  have hout := higherDirectImage_binaryProduct_isConstructible_of_curves hcurve R n
    k _ hGi
  have hcomp := (Constructible.isConstructible_iff_of_iso
    (Finite.higherDirectImageCompFiniteIso (structureMap R n) i k G)).mpr hout
  have he : i ≫ structureMap R n = p ≫ f := by
    simpa only [f, Category.assoc] using hbase
  simpa only [he] using hcomp

end AlgebraicGeometry.Scheme.EtaleCohomology
