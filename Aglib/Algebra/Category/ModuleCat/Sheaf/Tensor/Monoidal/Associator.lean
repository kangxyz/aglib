/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Monoidal.LocalIso

/-! # The chosen associator of sheafified ringed-site tensors

Tensor stability of the actual localization class makes the two sheafified
whiskered units invertible. Conjugating the original presheaf associator by
these maps constructs the same chosen associator used by the Zariski client.
Tensor stability is an explicit input here, not a claimed general Hom theorem.
-/

@[expose] public noncomputable section

universe uC vC uR

open CategoryTheory MonoidalCategory

namespace SheafOfModulesOfCommRing

private theorem conjugatedIso_hom {K : Type*} [Category* K] {A B T E : K}
    (a : A ≅ B) (b : A ≅ T) (c : T ≅ E) :
    a.hom ≫ (a.symm ≪≫ b ≪≫ c).hom = b.hom ≫ c.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

private theorem natural_unit_value_of_map_square
    {A B : Type*} [Category* A] [Category* B]
    (L : A ⥤ B) (G : B ⥤ A) (η : 𝟭 A ⟶ L ⋙ G)
    {P Q T S : A} (u : P ⟶ Q) (a : P ⟶ T) (v : T ⟶ S)
    (m : L.obj Q ⟶ L.obj S) (hm : L.map u ≫ m = L.map a ≫ L.map v) :
    u ≫ η.app Q ≫ G.map m = a ≫ v ≫ η.app S := by
  have hu : u ≫ η.app Q = η.app P ≫ G.map (L.map u) := η.naturality u
  have hav : (a ≫ v) ≫ η.app S = η.app P ≫ G.map (L.map (a ≫ v)) :=
    η.naturality (a ≫ v)
  calc
    _ = (u ≫ η.app Q) ≫ G.map m := (Category.assoc _ _ _).symm
    _ = (η.app P ≫ G.map (L.map u)) ≫ G.map m :=
      congrArg (fun k => k ≫ G.map m) hu
    _ = η.app P ≫ G.map (L.map u ≫ m) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => η.app P ≫ k) (G.map_comp (L.map u) m).symm)
    _ = η.app P ≫ G.map (L.map a ≫ L.map v) :=
      congrArg (fun k => η.app P ≫ G.map k) hm
    _ = η.app P ≫ G.map (L.map (a ≫ v)) :=
      congrArg (fun k => η.app P ≫ G.map k) (L.map_comp a v).symm
    _ = (a ≫ v) ≫ η.app S := hav.symm
    _ = _ := Category.assoc _ _ _

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{uR} RingCat.{uR})]
  (R : Sheaf J CommRingCat.{uR}) [HasSheafify J AddCommGrpCat.{uR}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{uR}]
  [(presheafLocalIso R).IsMonoidal]

local notation "𝓛" => associatedSheaf R
local notation "𝓖" => toPresheaf R
local notation "η" => associatedSheafUnit R

/-- The sheafified right whiskering of the original unit is invertible. -/
theorem isIso_associatedSheaf_map_unit_whiskerRight
    (P B : PresheafOfModulesOfCommRing.{uR} R.obj) :
    IsIso ((𝓛).map ((η).app P ▷ B)) :=
  (presheafLocalIso_iff R _).mp
    ((presheafLocalIso R).whiskerRight_mem _ (presheafLocalIso_unit R P) B)

/-- The sheafified left whiskering of the original unit is invertible. -/
theorem isIso_associatedSheaf_map_whiskerLeft_unit
    (A P : PresheafOfModulesOfCommRing.{uR} R.obj) :
    IsIso ((𝓛).map (A ◁ (η).app P)) :=
  (presheafLocalIso_iff R _).mp
    ((presheafLocalIso R).whiskerLeft_mem A _ (presheafLocalIso_unit R P))

/-- The original presheaf associator conjugated by the original whiskered units. -/
def tensorAssociator (M N O : SheafOfModulesOfCommRing R) :
    tensorProduct R (tensorProduct R M N) O ≅ tensorProduct R M (tensorProduct R N O) :=
  (@asIso _ _ _ _ ((𝓛).map ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O))
      (isIso_associatedSheaf_map_unit_whiskerRight R _ _)).symm ≪≫
    (𝓛).mapIso (α_ ((𝓖).obj M) ((𝓖).obj N) ((𝓖).obj O)) ≪≫
    @asIso _ _ _ _ ((𝓛).map ((𝓖).obj M ◁ (η).app ((𝓖).obj N ⊗ (𝓖).obj O)))
      (isIso_associatedSheaf_map_whiskerLeft_unit R _ _)

/-- The defining square retains the three original associator factors. -/
@[reassoc]
theorem map_unit_whiskerRight_comp_tensorAssociator_hom
    (M N O : SheafOfModulesOfCommRing R) :
    (𝓛).map ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O) ≫
        (tensorAssociator R M N O).hom =
      (𝓛).map (α_ ((𝓖).obj M) ((𝓖).obj N) ((𝓖).obj O)).hom ≫
        (𝓛).map ((𝓖).obj M ◁ (η).app ((𝓖).obj N ⊗ (𝓖).obj O)) :=
  conjugatedIso_hom
    (@asIso _ _ _ _ ((𝓛).map ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O))
      (isIso_associatedSheaf_map_unit_whiskerRight R _ _))
    ((𝓛).mapIso (α_ ((𝓖).obj M) ((𝓖).obj N) ((𝓖).obj O)))
    (@asIso _ _ _ _ ((𝓛).map ((𝓖).obj M ◁ (η).app ((𝓖).obj N ⊗ (𝓖).obj O)))
      (isIso_associatedSheaf_map_whiskerLeft_unit R _ _))

/-- The associator's whole presheaf value retains the original sheafification units. -/
theorem associatedSheafUnit_comp_tensorAssociator_hom
    (M N O : SheafOfModulesOfCommRing R) :
    ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O) ≫
        (η).app ((𝓖).obj ((𝓛).obj ((𝓖).obj M ⊗ (𝓖).obj N)) ⊗ (𝓖).obj O) ≫
          (𝓖).map (tensorAssociator R M N O).hom =
      (α_ ((𝓖).obj M) ((𝓖).obj N) ((𝓖).obj O)).hom ≫
        ((𝓖).obj M ◁ (η).app ((𝓖).obj N ⊗ (𝓖).obj O)) ≫
          (η).app ((𝓖).obj M ⊗ (𝓖).obj ((𝓛).obj ((𝓖).obj N ⊗ (𝓖).obj O))) := by
  exact natural_unit_value_of_map_square (𝓛) (𝓖) (η)
    ((η).app ((𝓖).obj M ⊗ (𝓖).obj N) ▷ (𝓖).obj O)
    (α_ ((𝓖).obj M) ((𝓖).obj N) ((𝓖).obj O)).hom
    ((𝓖).obj M ◁ (η).app ((𝓖).obj N ⊗ (𝓖).obj O))
    (tensorAssociator R M N O).hom
    (map_unit_whiskerRight_comp_tensorAssociator_hom R M N O)

/-- The chosen associator on original nested pure section tensors. -/
theorem tensorAssociator_hom_tmul (M N O : SheafOfModulesOfCommRing R) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (o : O.val.obj U) :
    (tensorAssociator R M N O).hom.val.app U
        ((tensorUnitMap R (tensorProduct R M N) O).app U
          ((tensorUnitMap R M N).app U (m ⊗ₜ n) ⊗ₜ o)) =
      (tensorUnitMap R M (tensorProduct R N O)).app U
        (m ⊗ₜ (tensorUnitMap R N O).app U (n ⊗ₜ o)) :=
  congrArg (fun k ↦ k.app U ((m ⊗ₜ n) ⊗ₜ o))
    (associatedSheafUnit_comp_tensorAssociator_hom R M N O)

/-- The inverse chosen associator on original nested pure section tensors. -/
theorem tensorAssociator_inv_tmul (M N O : SheafOfModulesOfCommRing R) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (o : O.val.obj U) :
    (tensorAssociator R M N O).inv.val.app U
        ((tensorUnitMap R M (tensorProduct R N O)).app U
          (m ⊗ₜ (tensorUnitMap R N O).app U (n ⊗ₜ o))) =
      (tensorUnitMap R (tensorProduct R M N) O).app U
        ((tensorUnitMap R M N).app U (m ⊗ₜ n) ⊗ₜ o) := by
  rw [← tensorAssociator_hom_tmul]
  exact congrArg (fun k ↦ k.val.app U ((tensorUnitMap R (tensorProduct R M N) O).app U
    ((tensorUnitMap R M N).app U (m ⊗ₜ n) ⊗ₜ o))) (tensorAssociator R M N O).hom_inv_id

end SheafOfModulesOfCommRing
