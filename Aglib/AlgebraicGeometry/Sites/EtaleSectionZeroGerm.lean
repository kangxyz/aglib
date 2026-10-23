/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSectionZeroLocus
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Actual etale-local zero neighborhoods and native geometric germs

The original chart is lifted through the chosen separably closed geometric
point, and the equality is the native colimit germ relation. No skyscraper
stalk formula or closed-immersion comparison is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Etale

universe u v

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- An actual local zero neighborhood kills the native geometric-point germ of a section. -/
theorem geometricGerm_eq_zero_of_mem_sectionZeroLocus
    (s : Spec (.of Ω) ⟶ X) (F : X.Etaleᵒᵖ ⥤ Ab.{max u v}) {U : X.Etale}
    (a : F.obj (op U)) (p : (pointSmallEtale s).fiber.obj U)
    (h : p.left (default : Spec (.of Ω)) ∈ sectionZeroLocus F a) :
    (pointSmallEtale s).toPresheafFiber U p F a = 0 := by
  obtain ⟨V, f, y, hy, hz⟩ := h
  obtain ⟨l, hl, _⟩ := exists_fac_of_etale_of_isSepClosed f.left p.left y hy
  have hf : f.left ≫ U.hom = V.hom := by simpa using f.w
  let q : (pointSmallEtale s).fiber.obj V := Over.homMk l (by
    change l ≫ V.hom = s
    rw [← hf, ← Category.assoc, hl]
    exact p.w)
  have hq : (pointSmallEtale s).fiber.map f q = p := by
    apply Over.OverMorphism.ext
    exact hl
  have hw := ConcreteCategory.congr_hom ((pointSmallEtale s).toPresheafFiber_w f q F) a
  rw [hq] at hw
  exact hw.symm.trans ((congrArg ((pointSmallEtale s).toPresheafFiber V q F) hz).trans
    (map_zero _))

end AlgebraicGeometry.Scheme.Etale
