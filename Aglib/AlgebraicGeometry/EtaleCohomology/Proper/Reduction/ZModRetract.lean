/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModImages
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SurjectivePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.InjectiveRetract
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf

/-! # Genuine injective module retracts along an actual surjection

The original abelian inverse image of an n-killed coefficient is again
n-killed. Give it the published canonical genuine-module structure, embed in
an injective module sheaf upstairs, and use the original abelian adjunction.
Faithful inverse image makes that adjoint map monic. Full genuine ZMod
forgetting then lifts it to the module category, where injectivity downstairs
splits it. No forgotten injective is declared injective.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

private theorem zmodModule_nsmul (n : ℕ) (M : ModuleCat.{u + 1} (ZMod n)) (x : M) :
    n • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod n), ZMod.natCast_self, zero_smul]

/-- The original underlying coefficient of a genuine ZMod-module sheaf is
annihilated by the literal modulus on its original identity map. -/
theorem zmodUnderlying_nsmul_id (X : Scheme.{u}) (n : ℕ) (I : ZModSheaf X n) :
    n • 𝟙 ((zmodUnderlying X n).obj I) = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact zmodModule_nsmul n (I.obj.obj U) x

/-- Every genuine module injective downstairs is an actual coefficient retract
of the genuine direct image of an actual module injective upstairs, for an
arbitrary surjective scheme morphism and every modulus. -/
theorem exists_zmodInjective_directImage_retract
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f]
    (n : ℕ) (I : ZModSheaf S n) [Injective I] :
    ∃ J : ZModSheaf X n, Injective J ∧
      Nonempty (Retract I ((zmodDirectImage f n).obj J)) := by
  let U := zmodUnderlying S n
  let V := zmodUnderlying X n
  let A := (inverseImage f).obj (U.obj I)
  have hA : n • 𝟙 A = 0 := by
    have h := congrArg (fun q => (inverseImage f).map q) (zmodUnderlying_nsmul_id S n I)
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_zero] using h
  let M : ZModSheaf X n := TorsionZMod.sheaf X.smallEtaleTopology n A hA
  let eM : V.obj M ≅ A := TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n A hA
  have : EnoughInjectives (ZModSheaf X n) :=
    TorsionZMod.enoughInjectivesStandard.{u + 1, u} X.smallEtaleTopology n
  have : PreservesFiniteLimits V :=
    TorsionZMod.underlying_preservesFiniteLimits.{u + 1, u} X.smallEtaleTopology n
  have : (inverseImage f).Faithful := inverseImage_faithful_of_surjective f
  have : U.Full := zmodUnderlying_full S n
  obtain ⟨P⟩ := EnoughInjectives.presentation M
  let j : A ⟶ V.obj P.J := eM.inv ≫ V.map P.f
  have : Mono j := inferInstance
  let a : U.obj I ⟶ (directImage f).obj (V.obj P.J) :=
    (inverseImageAdjunction f).homEquiv _ _ j
  have : Mono a := inferInstance
  let eR : U.obj ((zmodDirectImage f n).obj P.J) ≅
      (directImage f).obj (V.obj P.J) := (zmodDirectImageUnderlyingIso f n).app P.J
  let i : I ⟶ (zmodDirectImage f n).obj P.J := U.preimage (a ≫ eR.inv)
  have hi : Mono (U.map i) := by
    rw [Functor.map_preimage]
    infer_instance
  have : Mono i := U.mono_of_mono_map hi
  let r : Retract I ((zmodDirectImage f n).obj P.J) :=
    { i := i
      r := Injective.factorThru (𝟙 I) i
      retract := Injective.comp_factorThru (𝟙 I) i }
  exact ⟨P.J, inferInstance, ⟨r⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
