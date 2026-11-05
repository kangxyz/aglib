/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleCoefficientFunctor

/-! # Original scalar actions before constant-module sheafification

The original scalar map of a constant abelian coefficient acts on every
original cohomology group. Resizing uses the same Shrink linear equivalence,
so its specified underlying comparison retains this action exactly.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u r w s e
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type r) [Ring Λ]

/-- Original scalar multiplication on the whole underlying constant coefficient functor. -/
abbrev constantModuleUnderlyingScalar (a : Λ) :
    constantModuleUnderlying (X := X) Λ ⟶ constantModuleUnderlying (X := X) Λ :=
  Functor.whiskerRight (ModuleCat.forgetScalar Λ a)
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- The actual resized underlying comparison intertwines original scalar maps. -/
theorem smallConstantModuleCohomologyUnderlyingIso_scalar
    (q : ℕ) (M : ModuleCat.{u + 1} Λ) (a : Λ) :
    Functor.whiskerLeft ((smallConstantModuleCohomologyFunctor f Λ q).obj M)
        (ModuleCat.forgetScalar Λ a) ≫
      (smallConstantModuleCohomologyUnderlyingIso f Λ q).hom.app M =
    (smallConstantModuleCohomologyUnderlyingIso f Λ q).hom.app M ≫
      (smallFibreProductCohomologyFunctor f q).map
        ((constantModuleUnderlyingScalar (X := X) Λ a).app M) := by
  ext U x
  let V : ModuleCat.{e} Λ :=
    ((constantModuleCohomologyCoefficientFunctor f Λ q).obj M).obj U
  let : Small.{u + 1} V :=
    fibreProductCohomology_small.{u, w, s, e} f
      ((constantModuleUnderlying (X := X) Λ).obj M) q U.unop
  let b : Shrink.{u + 1} V ≃+ V := Shrink.addEquiv
  let l : Shrink.{u + 1} V ≃ₗ[Λ] V := Shrink.linearEquiv Λ V
  let xM : Shrink.{u + 1} V := x
  change b.symm (b (a • xM)) =
    b.symm
      (Sheaf.H.map ((inverseImage (pullback.snd U.unop.hom f)).map
        ((constantModuleUnderlyingScalar (X := X) Λ a).app M)) q
        (b (b.symm (b xM))))
  rw [b.apply_symm_apply]
  apply congrArg b.symm
  exact l.map_smul a xM

end AlgebraicGeometry.Scheme.EtaleCohomology
