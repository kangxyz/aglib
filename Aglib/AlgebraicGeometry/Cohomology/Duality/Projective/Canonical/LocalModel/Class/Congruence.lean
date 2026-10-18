/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Open

/-!
# Original model sections under equality of actual source opens

The original restriction-congruence component is the original presheaf
transport. After the genuine equality of source maps it preserves the
same original model class.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u w
namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction along genuinely equal open maps preserves the same original model class. -/
theorem regularListModelTopClass_restrictFunctorCongr
    {A : CommRingCat.{u}} (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)
    {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A) [HasExt.{w} (ModuleCat.{u} A)]
    {V : Scheme.{u}} (f g : V ⟶ Spec (regularListQuotientRing s))
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) (r : A) (U : V.Opens) :
    ((restrictFunctorCongr h).hom.app
      ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
        (s.length : ℤ))).val.app (op U)
      (regularListModelTopClass s hs J e r (f ''ᵁ U)) =
      regularListModelTopClass s hs J e r (g ''ᵁ U) := by
  subst g
  change (((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
    (s.length : ℤ)).presheaf.map (eqToHom (show f ''ᵁ U = f ''ᵁ U from rfl)).op)
      (regularListModelTopClass s hs J e r (f ''ᵁ U)) = _
  simp only [eqToHom_refl, op_id]
  exact ConcreteCategory.congr_hom
    (((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
      (s.length : ℤ)).presheaf.map_id (op (f ''ᵁ U)))
      (regularListModelTopClass s hs J e r (f ''ᵁ U))

end AlgebraicGeometry.Scheme.Modules
