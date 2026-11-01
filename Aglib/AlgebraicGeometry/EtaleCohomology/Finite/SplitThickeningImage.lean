/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtaleImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic.PullbackAffine
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.SurjectiveMonomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SplitThickening.SpecQuotient

/-! # Constructibility of the original direct image across a split thickening

The original unit for a surjective closed immersion and the original
composition isomorphism identify the given direct image with a finite étale
direct image of the actual inverse image. The concrete spectrum consumer
uses the same split quotient, nilpotent kernel, product and triangle.
No proper-base-change theorem or smooth-base-change assumption is used.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

/-- A genuine surjective closed immersion with finite étale composite gives
constructibility of the original direct image from an affine source. -/
theorem isConstructible_directImage_of_surjectiveClosedImmersion
    {X Y Z : Scheme.{u}} [IsAffine Y] (f : Y ⟶ X) (i : Z ⟶ Y)
    [IsClosedImmersion i] [Surjective i] [IsFinite (i ≫ f)] [Etale (i ≫ f)]
    {F : AbelianSheaf.{u, u + 1} Y} (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((directImage f).obj F) := by
  have : IsAffine Z := isAffine_of_isAffineHom i
  have hFi : Constructible.IsConstructible ((inverseImage i).obj F) :=
    Constructible.isConstructible_pullback_of_isAffine i hF
  have : IsIso ((inverseImageAdjunction i).unit.app F) :=
    surjectiveFiniteMono_unit_app_isIso i F
  let e := (directImage f).mapIso (asIso ((inverseImageAdjunction i).unit.app F)) ≪≫
    (directImageCompIso f i).app ((inverseImage i).obj F)
  exact (Constructible.isConstructible_iff_of_iso e).mpr
    (Constructible.isConstructible_finiteEtaleDirectImage (i ≫ f) hFi)

/-- The actual original split quotient supplies the preceding geometric
hypotheses and preserves finite-abelian constructibility under direct image. -/
theorem isConstructible_directImage_of_splitQuotient
    {R C A : Type u} [CommRing R] [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A] {J : Type u} [Finite J]
    (q : C ⊗[R] A →ₐ[C] (J → C)) (hq : Function.Surjective q)
    (n : ℕ) (hn : (RingHom.ker q.toRingHom) ^ n = ⊥)
    {F : AbelianSheaf.{u, u + 1} (Spec (.of (C ⊗[R] A)))}
    (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((directImage (Spec.algebraMap C (C ⊗[R] A))).obj F) := by
  let f := Spec.algebraMap C (C ⊗[R] A)
  let i := Spec.map (CommRingCat.ofHom q.toRingHom)
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ hq
  have : Surjective i :=
    Scheme.FiniteEtale.SplitThickening.specMap_surjective_of_ker_pow_eq_bot q.toRingHom hq n hn
  have ht : i ≫ f = Spec.algebraMap C (J → C) :=
    Scheme.FiniteEtale.SplitThickening.spec_splitQuotient_triangle q
  have : IsFinite (i ≫ f) := by
    rw [ht]
    exact Scheme.FiniteEtale.SplitThickening.splitProduct_isFinite C J
  have : Etale (i ≫ f) := by
    rw [ht]
    exact Scheme.FiniteEtale.SplitThickening.splitProduct_etale C J
  exact isConstructible_directImage_of_surjectiveClosedImmersion f i hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
