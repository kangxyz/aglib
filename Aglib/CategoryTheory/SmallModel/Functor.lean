/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.SmallModel.Exact
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield

/-!
# Functors between chosen small models

Conjugation by Mathlib's chosen SmallModel equivalences defines the actual transported functor.
Its represented-object comparison, exactness properties and kernel retain the independent
source, target and small-model universes.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Localization/SmallModel.lean`.
SHA-256: `6fb9558471ad505fef53de335dbd70f8f9d660680b9fc3368023e0a57742237a`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.ExactCategory
namespace CategoryTheory.SmallModel
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (F : C ⥤ D)

/-- Transport an actual functor through the chosen small-model equivalences. -/
def functor : SmallModel.{w} C ⥤ SmallModel.{w} D :=
  ((equivSmallModel C).inverse ⋙ F) ⋙ (equivSmallModel D).functor

/-- Conjugation by the chosen small-model equivalences preserves finite limits. -/
instance functor_preservesFiniteLimits [PreservesFiniteLimits F] :
    PreservesFiniteLimits (functor F) := by dsimp [functor]; infer_instance

/-- Conjugation by the chosen small-model equivalences preserves finite colimits. -/
instance functor_preservesFiniteColimits [PreservesFiniteColimits F] :
    PreservesFiniteColimits (functor F) := by dsimp [functor]; infer_instance

/-- Conjugation by the chosen small-model equivalences preserves additivity. -/
instance functor_additive [F.Additive] : (functor F).Additive := by
  dsimp [functor]
  infer_instance

/-- The genuine source small-model equivalence commutes with transported F. -/
def comparison : (equivSmallModel C).functor ⋙ functor F ≅ F ⋙ (equivSmallModel D).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (equivSmallModel C).unitIso.symm _ ≪≫ Functor.leftUnitor _) _

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [Abelian C] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The kernel on the small model is the original kernel evaluated on the
actual represented object; no replacement support property is introduced. -/
theorem kernel_iff (M : SmallModel.{w} C) :
    (functor F).kernel M ↔ F.kernel ((equivSmallModel C).inverse.obj M) := by
  change IsZero ((equivSmallModel D).functor.obj (F.obj ((equivSmallModel C).inverse.obj M))) ↔
    IsZero (F.obj ((equivSmallModel C).inverse.obj M))
  exact ⟨fun h ↦ IsZero.of_full_of_faithful_of_isZero _ _ h, fun h ↦ Functor.map_isZero _ h⟩

end CategoryTheory.SmallModel
