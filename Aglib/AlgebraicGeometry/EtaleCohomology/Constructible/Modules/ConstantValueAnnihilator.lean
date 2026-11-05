/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Images
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.EtaleRestriction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRestriction

/-! # Annihilators detected on the original constant module value

Local injectivity of the actual sheafification unit detects equality of
constant values on any nonempty scheme. Consequently an actual etale
constant trivialization detects the original coefficient annihilator,
without a finite coefficient ring, finite underlying value, or prior torsion
hypothesis on that value.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original constant module sheafification unit is injective on the
terminal chart of a nonempty scheme. -/
theorem constantModuleUnit_injective
    (R : Type r) [Ring R] (X : Scheme.{u}) [Nonempty X]
    (M : ModuleCat.{u + 1} R) :
    Function.Injective
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op (etaleTerminal X))) := by
  let J : GrothendieckTopology X.Etale := X.smallEtaleTopology
  let : HasSheafify J (ModuleCat.{u + 1} R) :=
    ModuleCat.Sheaf.hasSheafify.{u + 1, u, r} R J
  let η : (Functor.const X.Etaleᵒᵖ).obj M ⟶
      ((constantSheaf J (ModuleCat.{u + 1} R)).obj M).obj :=
    toSheafify J ((Functor.const X.Etaleᵒᵖ).obj M)
  let : PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    ModuleCat.Sheaf.forget_preservesFilteredColimits R
  let : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, r}
  let : J.PreservesSheafification (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    inferInstance
  let : CategoryTheory.Presheaf.IsLocallyInjective J η :=
    CategoryTheory.Presheaf.isLocallyInjective_toSheafify'.{u + 1, u, max r (u + 2), u + 1} J
      (D := ModuleCat.{u + 1} R) ((Functor.const X.Etaleᵒᵖ).obj M)
  intro a b hab
  have hcov := CategoryTheory.Presheaf.equalizerSieve_mem J η a b hab
  obtain ⟨V, hOver, hEtale, hV⟩ := (Scheme.mem_smallGrothendieckTopology _ _).mp hcov
  obtain ⟨i, _⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).mp V.mem₀).1
    (Classical.choice (inferInstance : Nonempty X))
  let := hOver
  let W := (V.X i).asOverProp X (hEtale i)
  let f : W ⟶ etaleTerminal X := (V.f i).asOverProp X
  have heq : CategoryTheory.Presheaf.equalizerSieve a b f := hV _ _ ⟨i⟩
  exact heq

/-- A supplied actual etale constant trivialization detects the coefficient's
specified scalar annihilator on its unchanged module value. -/
theorem value_annihilator_of_etale_trivialization
    {X Y : Scheme.{u}} (R : Type r) [Ring R]
    (f : Y ⟶ X) [Etale f] [Nonempty Y]
    (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R)
    (n : ℕ) (hF : n • 𝟙 F = 0)
    (t : (moduleInverseImage R f).obj F ≅
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    ∀ m : M, n • m = 0 := by
  let Q := moduleInverseImage R f
  let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)
  let : (moduleEtaleRestriction R f).Additive := { map_add := by intro A B a b; rfl }
  let : Q.Additive := Functor.additive_of_iso (moduleInverseImageEtaleIso R f).symm
  have hpull : n • 𝟙 (Q.obj F) = 0 := by
    have hmap : Q.map (n • 𝟙 F) = 0 := (congrArg Q.map hF).trans (Q.map_zero F F)
    exact (Q.map_nsmul.trans (congrArg (fun a => n • a) (Q.map_id F))).symm.trans hmap
  have hc : n • 𝟙 (C.obj M) = 0 := by
    apply (cancel_epi t.hom).mp
    rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
    have h := (congrArg (fun a : Q.obj F ⟶ Q.obj F => a ≫ t.hom) hpull).trans zero_comp
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using h
  let η := (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
    (op (etaleTerminal Y))
  intro m
  apply constantModuleUnit_injective R Y M
  have hz := congrArg
    (fun a : C.obj M ⟶ C.obj M => a.hom.app (op (etaleTerminal Y)) (η m)) hc
  change n • η m = 0 at hz
  change η (n • m) = η 0
  simpa only [map_nsmul, map_zero] using hz

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
