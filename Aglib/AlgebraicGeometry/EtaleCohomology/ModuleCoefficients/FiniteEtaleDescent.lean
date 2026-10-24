/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleModuleTrace
public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.FiniteDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.CoverConservativity
public import Mathlib.CategoryTheory.Sites.Abelian

/-! # Coprime finite-etale descent of finite original module cohomology

The actual module-linear trace retraction and original finite-direct-image
comparison descend finite generation. No Noetherian ring or finite underlying
additive group is needed. An original constant trivialization detects an
explicit coefficient annihilator by cover faithfulness, without using the
torsion-only constant-section unit to justify its own torsion hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Constructible.Modules

universe u r eX eY

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R] {X S : Scheme.{u}}

/-- A literal annihilator of the chosen constant value annihilates the original
sheaf, by faithful actual inverse image along the surjective etale map. -/
theorem moduleSheaf_nsmul_id_eq_zero_of_trivialization
    (f : S ⟶ X) [Etale f] [Surjective f] (F : ModuleSheaf R X)
    (M : ModuleCat.{u + 1} R) (n : ℕ) (hM : ∀ m : M, n • m = 0)
    (e : (moduleInverseImage R f).obj F ≅
      (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    n • 𝟙 F = 0 := by
  let C := constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)
  let Q : ModuleSheaf R X ⥤ ModuleSheaf R S := moduleInverseImage R f
  have : (moduleEtaleRestriction R f).Additive :=
    { map_add := by intro A B a b; rfl }
  have : Q.Additive := Functor.additive_of_iso (moduleInverseImageEtaleIso R f).symm
  have hm : n • 𝟙 M = 0 := by ext m; exact hM m
  have hc₀ : C.map (n • 𝟙 M) = 0 :=
    (congrArg C.map hm).trans (C.map_zero M M)
  have hc₁ : C.map (n • 𝟙 M) = n • 𝟙 (C.obj M) :=
    C.map_nsmul.trans (congrArg (fun a => n • a) (C.map_id M))
  have hc : n • 𝟙 (C.obj M) = 0 := hc₁.symm.trans hc₀
  have hq : n • 𝟙 (Q.obj F) = 0 := by
    apply (cancel_mono e.hom).mp
    rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
    calc
      n • e.hom = e.hom ≫ (n • 𝟙 (C.obj M)) := by
        rw [Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 := by rw [hc, comp_zero]
  apply Q.map_injective
  exact (Q.map_nsmul.trans (congrArg (fun a => n • a) (Q.map_id F))).trans
    (hq.trans (Q.map_zero F F).symm)

variable (Y : Scheme.FiniteEtale X)
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y.obj.left)]

/-- Finite original cohomology descends across a finite-etale cover whose
literal constant rank is coprime to an annihilator of the original module sheaf.
The two Ext universes are independent and the ring need not be Noetherian. -/
theorem moduleSheaf_cohomology_finite_of_finiteEtale_coprime
    (n : ℕ) (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : ModuleSheaf R X) (p : ℕ) (hcop : n.Coprime p) (hp : p • 𝟙 F = 0)
    (q : ℕ)
    [Module.Finite R ((ModuleCat.Sheaf.cohomology Y.obj.left.smallEtaleTopology R q).obj
      ((moduleInverseImage R Y.obj.hom).obj F))] :
    Module.Finite R ((ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q).obj F) := by
  let H := ModuleCat.Sheaf.cohomology X.smallEtaleTopology R q
  have hfinite : Module.Finite R (H.obj ((moduleDirectImage R Y.obj.hom).obj
      ((moduleInverseImage R Y.obj.hom).obj F))) :=
    (Finite.finite_moduleCohomology_directImage_iff R Y.obj.hom
      ((moduleInverseImage R Y.obj.hom).obj F) q).mpr inferInstance
  let := hfinite
  obtain ⟨r, hr⟩ := exists_finiteEtale_moduleSheafRetraction_map R Y n hn F p hcop hp H
  apply Module.Finite.of_surjective r.hom
  intro x
  refine ⟨H.map ((moduleImageAdjunction R Y.obj.hom).unit.app F) x, ?_⟩
  exact congrArg (fun a => a x) hr

end AlgebraicGeometry.Scheme.EtaleCohomology
