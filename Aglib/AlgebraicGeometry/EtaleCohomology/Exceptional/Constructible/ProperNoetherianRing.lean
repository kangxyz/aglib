/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.ConstructibleAnnihilator
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons

/-! # Original proper higher images over a left-Noetherian coefficient ring

The identity open immersion gives the original proper map as a compactification.
Its canonical lower-shriek identity and coefficient equivalence counit transport
the compactified theorem to the original ringed higher image, without replacing
coefficients or their underlying groups. This leaf is a current unverified draft.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wMX wMS wAX wAS
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Every original proper higher image of a constructible module over a
left-Noetherian `Z/n`-algebra is constructible. The coefficient ring need not
be commutative, and its underlying additive group need not be finite. -/
theorem moduleHigherDirectImage_proper_noetherian_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsProper f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    (F : ModuleSheaf X Λ)
    (hF : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj F)) (q : ℕ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        (((moduleDirectImage f Λ).rightDerived q).obj F)) := by
  let E := moduleSheafEquivalence X Λ
  let M := E.inverse.obj F
  have hkill : n • 𝟙 M = 0 := by
    ext U x
    change n • x = 0
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  let C : Hom.Compactification f :=
    { Xbar := X
      j := 𝟙 X
      p := f
      isOpenImmersion_j := inferInstance
      isProper_p := inferInstance
      fac := Category.id_comp f }
  have h := moduleCompactificationHigherImage_annihilated_isConstructible
    f C Λ n hn M hF hkill q
  let e : (moduleLowerShriek (𝟙 X) Λ).obj (E.functor.obj M) ≅ F :=
    (moduleLowerShriekIdIso Λ X).app (E.functor.obj M) ≪≫ E.counitIso.app F
  exact (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleSheafEquivalence S Λ).inverse.mapIso
      (((moduleDirectImage f Λ).rightDerived q).mapIso e))).mp h

end AlgebraicGeometry.Scheme.EtaleCohomology
