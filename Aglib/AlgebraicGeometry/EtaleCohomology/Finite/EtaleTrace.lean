/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleRepresentedTransfer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteEtaleTransfer.Trace
public import Aglib.CategoryTheory.Preadditive.CoprimeScalar

/-! # Natural finite-etale sheaf trace and coprime retraction

The previously constructed free-representable transfer is evaluated on actual
product-test sheaves. The result is a natural map from original direct image
of original inverse image to the original coefficient. Its composite with the
original adjunction unit is multiplication by the actual constant finite-flat
rank. Coprimality with a coefficient annihilator gives a sheaf retraction,
which remains a retraction after any further functor, in particular an actual
extension-by-zero functor when that functor is supplied elsewhere.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u c h

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)

/-- Actual finite-etale sheaf trace, natural in all abelian coefficients and
normalized by the original adjunction unit and actual finite-flat rank. -/
theorem exists_finiteEtale_sheafTrace (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n) :
    ∃ tr : inverseImage Y.obj.hom ⋙ directImage Y.obj.hom ⟶
        𝟭 (AbelianSheaf.{u, u + 1} X),
      ∀ F, (inverseImageAdjunction Y.obj.hom).unit.app F ≫ tr.app F = n • 𝟙 F := by
  obtain ⟨a, ha⟩ := Scheme.FiniteEtale.exists_freeRepresentable_transfer Y n hn
  let U : X.Etale := (Scheme.FiniteEtale.toEtale X).obj Y
  refine ⟨etaleRepresentedTrace U a, fun F => ?_⟩
  exact etaleRepresentedTrace_rank U a n ha F

/-- A coefficient killed by an integer prime to the cover rank is an actual
sheaf retract of the original direct image of its original inverse image. -/
theorem exists_finiteEtale_sheafRetraction (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : AbelianSheaf.{u, u + 1} X) (p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 F = 0) :
    ∃ r : (directImage Y.obj.hom).obj ((inverseImage Y.obj.hom).obj F) ⟶ F,
      (inverseImageAdjunction Y.obj.hom).unit.app F ≫ r = 𝟙 F := by
  obtain ⟨tr, htr⟩ := exists_finiteEtale_sheafTrace Y n hn
  let : IsIso (n • 𝟙 F) := Preadditive.isIso_nsmul_id_of_coprime F n p hcop hp
  refine ⟨tr.app F ≫ inv (n • 𝟙 F), ?_⟩
  rw [← Category.assoc, htr F]
  exact IsIso.hom_inv_id (n • 𝟙 F)

/-- Coprime finite-etale descent splits the original sheaf-level unit. -/
theorem finiteEtale_unit_isSplitMono (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : AbelianSheaf.{u, u + 1} X) (p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 F = 0) : IsSplitMono ((inverseImageAdjunction Y.obj.hom).unit.app F) := by
  obtain ⟨r, hr⟩ := exists_finiteEtale_sheafRetraction Y n hn F p hcop hp
  exact IsSplitMono.mk' ⟨r, hr⟩

/-- The same genuine sheaf retraction survives any further functor. This
applies to an actual extension-by-zero functor without replacing it by ordinary cohomology. -/
theorem exists_finiteEtale_sheafRetraction_map (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : AbelianSheaf.{u, u + 1} X) (p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 F = 0) {C : Type c} [Category.{h} C]
    (G : AbelianSheaf.{u, u + 1} X ⥤ C) :
    ∃ r : G.obj ((directImage Y.obj.hom).obj ((inverseImage Y.obj.hom).obj F)) ⟶ G.obj F,
      G.map ((inverseImageAdjunction Y.obj.hom).unit.app F) ≫ r = 𝟙 _ := by
  obtain ⟨r, hr⟩ := exists_finiteEtale_sheafRetraction Y n hn F p hcop hp
  refine ⟨G.map r, ?_⟩
  exact (G.map_comp _ _).symm.trans ((congrArg G.map hr).trans (G.map_id F))

end AlgebraicGeometry.Scheme.EtaleCohomology
