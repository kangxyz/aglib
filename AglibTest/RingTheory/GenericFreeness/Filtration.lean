/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.GenericFreeness.Filtration

/-! Focused consumer of the filtration and localization lemmas behind generic freeness (plan
row F12): exhaustive `ℕ`-filtrations with free graded pieces, before and after localization. -/

@[expose] public section

example (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (F : ℕ → Submodule R M)
    (hF : Monotone F) (h0 : F 0 = ⊥) (htop : ⨆ j, F j = ⊤)
    (hfree : ∀ j, Module.Free R (↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype)) :
    Module.Free R M :=
  Module.free_of_filtration F hF h0 htop hfree

example (R C M : Type*) [CommRing R] [CommRing C] [Algebra R C] [AddCommGroup M] [Module R M]
    [Module C M] [IsScalarTower R C M] (S : Submonoid R) (F : ℕ → Submodule C M)
    (hF : Monotone F) (h0 : F 0 = ⊥) (htop : ⨆ j, F j = ⊤)
    (hfree : ∀ j, Module.Free (Localization S)
      (LocalizedModule S (↥(F (j + 1)) ⧸ (F j).comap (F (j + 1)).subtype))) :
    Module.Free (Localization S) (LocalizedModule S M) :=
  Module.free_localizedModule_of_filtration_of_isScalarTower S F hF h0 htop hfree

example (R P : Type*) [CommRing R] [AddCommGroup P] [Module R P] (a c : R)
    [Module.Free (Localization.Away a) (LocalizedModule.Away a P)] :
    Module.Free (Localization.Away (a * c)) (LocalizedModule.Away (a * c) P) :=
  Module.free_localizedModule_away_of_dvd (dvd_mul_right a c)

/--
info: 'Module.free_of_filtration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Module.free_of_filtration

/--
info: 'Module.free_localizedModule_of_filtration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Module.free_localizedModule_of_filtration

/--
info: 'Module.free_localizedModule_of_filtration_of_isScalarTower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Module.free_localizedModule_of_filtration_of_isScalarTower

/--
info: 'Module.free_localizedModule_away_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Module.free_localizedModule_away_of_dvd

/--
info: 'Module.free_localizedModule_of_linearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Module.free_localizedModule_of_linearEquiv

/--
info: 'Module.free_of_isLocalizedModule_of_free_isLocalizedModule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Module.free_of_isLocalizedModule_of_free_isLocalizedModule
