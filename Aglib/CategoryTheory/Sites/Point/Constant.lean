/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Connected

/-! # Constant objects and original point germs

The original constant-presheaf germ is invertible because the native pointed
neighborhood category is connected. A point inverts the sheafification unit,
so the same holds for its composite with the constant-sheaf unit. The original
constant-adjunction transpose retains the corresponding germ equation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

universe u v w uA vA

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {A : Type uA} [Category.{vA} A]
  [HasColimitsOfSize.{w, w} A]

/-- The original germ of a constant presheaf is an isomorphism. -/
theorem constantPresheafGerm_isIso (U : C) (x : Φ.fiber.obj U) (M : A) :
    IsIso (Φ.toPresheafFiber U x ((Functor.const Cᵒᵖ).obj M)) := by
  let P := (Functor.const Cᵒᵖ).obj M
  let D := (Functor.Elements.π Φ.fiber).op ⋙ P
  let c : Cocone D := { pt := M, ι := { app _ := 𝟙 M } }
  let hc : IsColimit c := isColimitConstCocone Φ.fiber.Elementsᵒᵖ M
  let hd : IsColimit (Φ.presheafFiberCocone P) := Φ.isColimitPresheafFiberCocone P
  let e : M ≅ Φ.presheafFiber.obj P := hc.coconePointUniqueUpToIso hd
  have he : e.hom = Φ.toPresheafFiber U x P := by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom hc hd
      (op (Φ.fiber.elementsMk U x))
    change 𝟙 M ≫ e.hom = Φ.toPresheafFiber U x P at h
    exact (Category.id_comp e.hom).symm.trans h
  change IsIso (Φ.toPresheafFiber U x P)
  rw [← he]
  infer_instance

variable [HasProducts.{w} A] [HasWeakSheafify J A]

/-- The original constant unit followed by the original germ is invertible. -/
theorem constantSheafGerm_isIso (U : C) (x : Φ.fiber.obj U) (M : A) :
    IsIso ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) ≫
      Φ.toPresheafFiber U x ((constantSheaf J A).obj M).obj) := by
  change IsIso ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) ≫
    Φ.toPresheafFiber U x (CategoryTheory.sheafify J ((Functor.const Cᵒᵖ).obj M)))
  rw [← Φ.toPresheafFiber_naturality]
  let := Φ.constantPresheafGerm_isIso U x M
  infer_instance

omit [HasProducts.{w} A] in
/-- The original constant-adjunction transpose has its original terminal
section followed by the same germ, rather than an unspecified fibre map. -/
@[reassoc]
theorem constantSheafAdj_transpose_germ {T : C} (hT : IsTerminal T)
    (x : Φ.fiber.obj T) (M : A) (F : Sheaf J A) (b : M ⟶ F.obj.obj (op T)) :
    ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) ≫
        Φ.toPresheafFiber T x ((constantSheaf J A).obj M).obj) ≫
      Φ.sheafFiber.map (((constantSheafAdj J A hT).homEquiv M F).symm b) =
        b ≫ Φ.toPresheafFiber T x F.obj := by
  let a := ((constantSheafAdj J A hT).homEquiv M F).symm b
  have ha : (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) ≫
      a.hom.app (op T) = b := by
    have h := ((constantSheafAdj J A hT).homEquiv M F).apply_symm_apply b
    rw [Adjunction.homEquiv_unit] at h
    simp only [constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, Category.id_comp] at h
    exact h
  change (_ ≫ _) ≫ Φ.presheafFiber.map a.hom = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (CategoryTheory.toSheafify J
      ((Functor.const Cᵒᵖ).obj M)).app (op T) ≫ k)
      (Φ.toPresheafFiber_naturality a.hom T x)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg
        (fun k => k ≫ Φ.toPresheafFiber T x F.obj) ha)))

end CategoryTheory.GrothendieckTopology.Point
