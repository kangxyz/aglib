/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.QuasiCompactLowerShriek

/-! # Base-local constructibility of original qc-open extension by zero -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
universe u
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Original extension by zero preserves constructibility on an arbitrary
scheme along a quasi-compact open immersion. Only affine test targets are qcqs. -/
theorem isConstructible_moduleLowerShriek_of_quasiCompact
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (Λ : Type (u + 1)) [Ring Λ]
    (M : Coefficients.ModuleSheaf U Λ)
    (hM : IsConstructible ((Coefficients.moduleSheafEquivalence U Λ).inverse.obj M)) :
    IsConstructible ((Coefficients.moduleSheafEquivalence X Λ).inverse.obj
      ((moduleLowerShriek j Λ).obj M)) := by
  intro V
  let : IsAffine V.1.toScheme := V.property
  let K := (moduleLowerShriek j Λ).obj M
  let M' := (Coefficients.moduleInverseImage (pullback.fst j V.1.ι) Λ).obj M
  have hM' : IsConstructible
      ((Coefficients.moduleSheafEquivalence (pullback j V.1.ι) Λ).inverse.obj M') :=
    moduleIsConstructible_inverseImage Λ (pullback.fst j V.1.ι) M hM
  have h := isConstructible_moduleLowerShriek_of_qcqs
    (pullback.snd j V.1.ι) Λ M' hM'
  obtain ⟨p⟩ := nonempty_constructiblePartition h
  let e : (moduleInverseImage Λ V.1.ι).obj
        ((Coefficients.moduleSheafEquivalence X Λ).inverse.obj K) ≅
      (Coefficients.moduleSheafEquivalence V.1.toScheme Λ).inverse.obj
        ((moduleLowerShriek (pullback.snd j V.1.ι) Λ).obj M') :=
    ((moduleInverseImageValuedIso Λ V.1.ι).app K).symm ≪≫
      (Coefficients.moduleSheafEquivalence V.1.toScheme Λ).inverse.mapIso
        ((moduleLowerShriekBaseChangeIso j V.1.ι Λ).app M)
  exact ⟨p.ofIso e.symm⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
