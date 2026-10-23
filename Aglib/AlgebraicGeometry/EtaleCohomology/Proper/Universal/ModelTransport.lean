/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Universal.Basic

/-! # Bounded exchange in independently supplied derived models

The actual higher direct-image objects do not depend on the choice of derived
category. For underlying genuine module injectives, positive source images
vanish. Exchange in the standard models therefore proves positive target
vanishing in the same actual sheaf category. Degree zero is controlled by the
original ordinary mate. These two tests transfer exchange to independently
supplied derived models, and genuine module injective reduction then supplies
every coefficient annihilated by the specified modulus.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

section TypedTransport

variable {C : Type*} [Category* C]

private theorem isIso_iff_of_normalization {A B D E : C}
    (s : A ≅ B) (t : D ≅ E) (a : B ⟶ E) (b : A ⟶ D)
    (h : s.hom ≫ a = b ≫ t.hom) : IsIso b ↔ IsIso a := by
  constructor
  · intro hb
    have := hb
    have hs : IsIso (s.hom ≫ a) := by rw [h]; infer_instance
    exact (isIso_comp_left_iff _ _).mp hs
  · intro ha
    have := ha
    have ht : IsIso (b ≫ t.hom) := by rw [← h]; infer_instance
    exact (isIso_comp_right_iff _ _).mp ht

private theorem injectiveTests_at_composite
    {M A B D : Type*} [Category* M] [Category* A] [Category* B] [Category* D]
    (single : A ⥤ B) (U : M ⥤ A) (Z : M ⥤ B) (e : Z = U ⋙ single)
    {L R : B ⥤ D} (β : L ⟶ R)
    (h : ∀ (I : M) [Injective I], IsIso (β.app (single.obj (U.obj I)))) :
    ∀ (I : M) [Injective I], IsIso (β.app (Z.obj I)) := by
  subst Z
  exact h

end TypedTransport

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

section ArbitraryModels

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- In each independently supplied model, degree-zero exchange is invertible
exactly when the actual ordinary exchange is invertible. -/
theorem higherBaseChangeMap_zero_isIso_iff (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((higherBaseChangeMap f f' g g' h 0).app F) ↔
      IsIso ((baseChangeMap f f' g g' h).app F) :=
  isIso_iff_of_normalization
    ((inverseImage g).mapIso ((directImage f).rightDerivedZeroIsoSelf.app F))
    ((directImage f').rightDerivedZeroIsoSelf.app ((inverseImage g').obj F))
    ((baseChangeMap f f' g g' h).app F) ((higherBaseChangeMap f f' g g' h 0).app F)
    (higherBaseChangeMap_zero f f' g g' h F)

end ArbitraryModels

section StandardModels

attribute [local instance] HasDerivedCategory.standard

variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (n : ℕ)

private theorem ordinaryExchange_of_boundedExchange
    (hf : boundedExchange n f f' g g' h)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
    IsIso ((baseChangeMap f f' g g' h).app F) :=
  (higherBaseChangeMap_zero_isIso_iff f f' g g' h F).mp (hf F hF 0)

private theorem targetImage_zmodInjective_isZero_of_boundedExchange
    (hf : boundedExchange n f f' g g' h)
    (I : Reduction.ZModSheaf X n) [Injective I] (q : ℕ) :
    IsZero ((higherDirectImage f' (q + 1)).obj
      ((inverseImage g').obj ((Reduction.zmodUnderlying X n).obj I))) := by
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X
  have hsource := (inverseImage g).map_isZero
    (Reduction.higherDirectImage_zmodInjective_isZero.{u, u + 2} f n I q)
  have hi := hf ((Reduction.zmodUnderlying X n).obj I)
    (Reduction.zmodUnderlying_nsmul_id X n I) (q + 1)
  have := hi
  exact hsource.of_iso
    (asIso ((higherBaseChangeMap f f' g g' h (q + 1)).app
      ((Reduction.zmodUnderlying X n).obj I))).symm

end StandardModels

section ArbitraryModels

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f) (n : ℕ)

private theorem higherExchange_zmodInjective_of_boundedExchange
    (hf : boundedExchange n f f' g g' h)
    (I : Reduction.ZModSheaf X n) [Injective I] (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' h q).app
      ((Reduction.zmodUnderlying X n).obj I)) := by
  cases q with
  | zero =>
      exact (higherBaseChangeMap_zero_isIso_iff f f' g g' h _).mpr
        (ordinaryExchange_of_boundedExchange f f' g g' h n hf _
          (Reduction.zmodUnderlying_nsmul_id X n I))
  | succ q =>
      let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} X) := hasExtStandard X
      exact ((inverseImage g).map_isZero
        (Reduction.higherDirectImage_zmodInjective_isZero.{u, u + 2} f n I q)).isIso
        (targetImage_zmodInjective_isZero_of_boundedExchange f f' g g' h n hf I q) _

/-- Standard-model bounded exchange gives the original higher exchange in
four independently supplied derived models and universes. -/
theorem higherBaseChangeMap_isIso_of_boundedExchange
    (hf : boundedExchange n f f' g g' h)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' h q).app F) := by
  have hI := injectiveTests_at_composite
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
    (Reduction.zmodUnderlying X n) (Reduction.zmodSingle X n) rfl
    (derivedBaseChangeMap f f' g g' h)
    (fun I _ => (Reduction.derivedBaseChangeMap_single_isIso_iff_higher f f' g g' h _).mpr
      (higherExchange_zmodInjective_of_boundedExchange f f' g g' h n hf I))
  exact Reduction.higherExchange_on_killedCoefficients f f' g g' h n hI F hF q

end ArbitraryModels

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
