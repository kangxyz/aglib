/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.RelativeCurveFiniteConstant
public import Aglib.AlgebraicGeometry.Dimension.Finite

/-! # Constructible coefficients on proper relative curves in every degree

The original finite-constant cogenerator and its actual finite composites are
used in the existing successor construction. Only the preceding degree of the
same morphism is needed for its actual cokernel.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Proper relative curves preserve constructibility in all higher direct images. -/
theorem higherDirectImage_isConstructible_of_relativeCurve
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((higherDirectImage f q).obj F) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  induction q generalizing F with
  | zero =>
    exact (Constructible.isConstructible_iff_of_iso
      ((directImage f).rightDerivedZeroIsoSelf.app F)).mpr
      (isConstructible_properDirectImage f hF)
  | succ q ih =>
    let t := Constructible.FiniteCogenerators.Global.finiteConstantProductEmbeddingOfConstructible
      X F hF
    apply higherDirectImage_isConstructible_succ_of_finiteConstantComposites f t hF q
    · intro G hG
      exact ih G hG
    · intro i
      apply finiteConstantHigherDirectImage_isConstructible_of_relativeCurve
        (t.morphism i ≫ f) _ (q + 1) (t.value i)
      intro Ω _ _ η
      let e := pullbackRightPullbackFstIso f η (t.morphism i)
      have hfinite : IsFinite (pullback.snd (t.morphism i) (pullback.fst f η)) := inferInstance
      let := hfinite
      exact (IsHomeomorph.topologicalKrullDim_eq _ e.inv.homeomorph.isHomeomorph).trans_le
        ((pullback.snd (t.morphism i) (pullback.fst f η)).topologicalKrullDim_le_of_isFinite.trans
          (hdim Ω η))

end AlgebraicGeometry.Scheme.EtaleCohomology
