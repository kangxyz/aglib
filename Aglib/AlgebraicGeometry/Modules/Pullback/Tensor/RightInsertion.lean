/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.RightUnit

/-!
# Original right insertion under pullback and coefficient change

The original unit inverse and tensor map insert a section into an arbitrary
module. A genuine equation between original sections transports this insertion
through arbitrary arrows in both factors and the native pullback tensor map.
No line, flatness, quasicoherence or invertibility hypothesis is needed.
The local raw one-pole transport consumes this complete original-map law.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback preserves right insertion of the original section, with the original unit map. -/
theorem pullback_rightInsertion {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ N) :
    (pullback f).map ((ρ_ M).inv ≫ tensorSheafMap Y (𝟙 M) s) ≫
        pullbackTensorMap f M N =
      (ρ_ ((pullback f).obj M)).inv ≫
        tensorSheafMap X (𝟙 ((pullback f).obj M))
          ((pullbackUnitIso f).inv ≫ (pullback f).map s) := by
  rw [CategoryTheory.Functor.map_comp, Category.assoc, pullbackTensorMap_naturality,
    CategoryTheory.Functor.map_id]
  have ht :
      tensorSheafMap X (𝟙 ((pullback f).obj M)) (pullbackUnitIso f).hom ≫
        tensorSheafMap X (𝟙 ((pullback f).obj M))
          ((pullbackUnitIso f).inv ≫ (pullback f).map s) =
      tensorSheafMap X (𝟙 ((pullback f).obj M)) ((pullback f).map s) := by
    rw [tensorSheafMap_comp, Category.id_comp, Iso.hom_inv_id_assoc]
  calc
    _ = ((pullback f).map (ρ_ M).inv ≫
        pullbackTensorMap f M (𝟙_ Y.Modules) ≫
        tensorSheafMap X (𝟙 ((pullback f).obj M)) (pullbackUnitIso f).hom) ≫
          tensorSheafMap X (𝟙 ((pullback f).obj M))
            ((pullbackUnitIso f).inv ≫ (pullback f).map s) := by
      simp only [Category.assoc, ht]
    _ = _ := congrArg (fun z => z ≫
      tensorSheafMap X (𝟙 ((pullback f).obj M))
        ((pullbackUnitIso f).inv ≫ (pullback f).map s)) (pullbackTensorMap_rightUnit f M)

/-- A genuine section comparison transports the complete original insertion map.
Both coefficient arrows are arbitrary; neither is inverted. -/
theorem rightInsertion_pullback_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : Y.Modules) (P' Q' : X.Modules)
    (c : P' ⟶ (pullback f).obj P) (d : Q' ⟶ (pullback f).obj Q)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ Q)
    (s' : SheafOfModules.unit X.ringCatSheaf ⟶ Q')
    (h : s' ≫ d = (pullbackUnitIso f).inv ≫ (pullback f).map s) :
    (show P' ⟶
        (show X.Modules from tensorSheaf X ((pullback f).obj P) ((pullback f).obj Q)) from
      (ρ_ P').inv ≫ tensorSheafMap X (𝟙 P') s' ≫ tensorSheafMap X c d) =
    c ≫ (pullback f).map ((ρ_ P).inv ≫ tensorSheafMap Y (𝟙 P) s) ≫
      pullbackTensorMap f P Q := by
  let U : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let T : X.Modules := tensorSheaf X ((pullback f).obj P) ((pullback f).obj Q)
  let t : U ⟶ (pullback f).obj Q := (pullbackUnitIso f).inv ≫ (pullback f).map s
  have ht := (tensorSheafMap_comp X (𝟙 P') s' c d).trans
    (congrArg (fun v => tensorSheafMap X v (s' ≫ d)) (Category.id_comp c))
  have hc := (tensorSheafMap_comp X c (𝟙 U) (𝟙 ((pullback f).obj P)) t).trans
    (congrArg₂ (tensorSheafMap X) (Category.comp_id c) (Category.id_comp t))
  have hn : c ≫ (ρ_ ((pullback f).obj P)).inv =
      (ρ_ P').inv ≫ tensorSheafMap X c (𝟙 U) :=
    rightUnitor_inv_naturality c
  calc
    (show P' ⟶ T from
        (ρ_ P').inv ≫ tensorSheafMap X (𝟙 P') s' ≫ tensorSheafMap X c d) =
        (show P' ⟶ T from (ρ_ P').inv ≫ tensorSheafMap X c (s' ≫ d)) :=
      congrArg (fun v : (show X.Modules from tensorSheaf X P' U) ⟶ T =>
        (ρ_ P').inv ≫ v) ht
    _ = (show P' ⟶ T from (ρ_ P').inv ≫ tensorSheafMap X c t) :=
      congrArg (fun v : U ⟶ (pullback f).obj Q =>
        (ρ_ P').inv ≫ tensorSheafMap X c v) h
    _ = (show P' ⟶ T from (ρ_ P').inv ≫
        (tensorSheafMap X c (𝟙 U) ≫ tensorSheafMap X (𝟙 ((pullback f).obj P)) t)) :=
      congrArg (fun v : (show X.Modules from tensorSheaf X P' U) ⟶ T =>
        (ρ_ P').inv ≫ v) hc.symm
    _ = (show P' ⟶ T from ((ρ_ P').inv ≫ tensorSheafMap X c (𝟙 U)) ≫
        tensorSheafMap X (𝟙 ((pullback f).obj P)) t) :=
      (Category.assoc _ _ _).symm
    _ = (show P' ⟶ T from (c ≫ (ρ_ ((pullback f).obj P)).inv) ≫
        tensorSheafMap X (𝟙 ((pullback f).obj P)) t) :=
      congrArg (fun v : P' ⟶ (show X.Modules from tensorSheaf X ((pullback f).obj P) U) =>
        v ≫ tensorSheafMap X (𝟙 ((pullback f).obj P)) t) hn.symm
    _ = (show P' ⟶ T from c ≫ ((ρ_ ((pullback f).obj P)).inv ≫
        tensorSheafMap X (𝟙 ((pullback f).obj P)) t)) :=
      Category.assoc _ _ _
    _ = (show P' ⟶ T from c ≫
        ((pullback f).map ((ρ_ P).inv ≫ tensorSheafMap Y (𝟙 P) s) ≫
          pullbackTensorMap f P Q)) :=
      congrArg (fun v : (pullback f).obj P ⟶ T => c ≫ v)
        (pullback_rightInsertion f P Q s).symm

end AlgebraicGeometry.Scheme.Modules
