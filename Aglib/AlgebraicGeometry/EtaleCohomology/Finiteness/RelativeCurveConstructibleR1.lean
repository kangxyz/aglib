/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.RelativeCurveFiniteConstantR1
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ProperConstantDegreeZero
public import Aglib.AlgebraicGeometry.Dimension.Finite

/-! # Original constructible R1 for proper relative curves

The existing actual finite-constant cogenerator is used once. Its finite
composites remain proper relative curves by the original fibre pullback and
finite dimension bound. Only degree-zero constructibility of its actual
cokernel and fixed-degree finite-constant R1 are consumed. There is no modulus,
new cogenerator, or degree-two hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Proper relative curves preserve constructibility in the original first
higher direct image, for every actual constructible abelian coefficient. -/
theorem higherDirectImage_R1_isConstructible_of_relativeCurve
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (η : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f η : Scheme.{u}) ≤ 1)
    (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    Constructible.IsConstructible ((higherDirectImage f 1).obj F) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := ⟨⟩
  let t := Constructible.FiniteCogenerators.Global.finiteConstantProductEmbeddingOfConstructible
    X F hF
  apply higherDirectImage_isConstructible_succ_of_finiteConstantComposites f t hF 0
  · intro G hG
    exact (Constructible.isConstructible_iff_of_iso
      ((directImage f).rightDerivedZeroIsoSelf.app G)).mpr
      (isConstructible_properDirectImage f hG)
  · intro i
    apply finiteConstantHigherDirectImage_R1_isConstructible_of_relativeCurve_unrestricted
      (t.morphism i ≫ f) _ (t.value i)
    intro Ω _ _ η
    let e := pullbackRightPullbackFstIso f η (t.morphism i)
    have hfinite : IsFinite (pullback.snd (t.morphism i) (pullback.fst f η)) := inferInstance
    let := hfinite
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.inv.homeomorph.isHomeomorph).trans_le
      ((pullback.snd (t.morphism i) (pullback.fst f η)).topologicalKrullDim_le_of_isFinite.trans
        (hdim Ω η))

end AlgebraicGeometry.Scheme.EtaleCohomology
