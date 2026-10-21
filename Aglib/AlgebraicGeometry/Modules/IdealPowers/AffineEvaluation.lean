/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.QuasiCoherent
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.CoproductSections
public import Aglib.AlgebraicGeometry.Modules.Rees.AffineOpenImage
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Affine sections of ideal scalar evaluation

Affine sections of the original scalar-evaluation map have precisely the span of
the scalar multiples as their image. The proof uses the original affine coproduct
cocone, so no assertion about arbitrary sheaf coproducts being pointwise is made.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]

/-- The original sections functor on a fixed open, retaining its full ring of functions. -/
abbrev idealSectionsFunctor (U : X.Opens) : X.Modules ⥤ ModuleCat Γ(X, U) :=
  toPresheafOfModules X ⋙ PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)

/-- The local ideal-generated span in the original module of sections. -/
def idealSectionSpan (J : Ideal A) (U : X.Opens) : Submodule Γ(X, U) (Γ(F, U)) :=
  Submodule.span Γ(X, U) {y | ∃ a : J, ∃ x : Γ(F, U),
    y = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (α a) • x}

omit [F.IsQuasicoherent] in
/-- The span presentation equals the native ideal multiple after extension of the ideal. -/
theorem idealSectionSpan_eq_smul (J : Ideal A) (U : X.Opens) :
    idealSectionSpan X α F J U =
      J.map (((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom).comp α) •
        (⊤ : Submodule Γ(X, U) (Γ(F, U))) := by
  rw [Ideal.map, ← Submodule.span_univ, Submodule.span_smul_span]
  apply congrArg (Submodule.span Γ(X, U))
  ext y
  constructor
  · rintro ⟨a, x, rfl⟩
    exact ⟨_, ⟨a, a.property, rfl⟩, x, Set.mem_univ _, rfl⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, x, _, h⟩
    exact ⟨⟨a, ha⟩, x, h.symm⟩

/-- On an affine open, scalar evaluation has exactly the expected ideal-generated range. -/
theorem idealEvaluation_affine_range (J : Ideal A) (U : X.affineOpens) :
    LinearMap.range ((idealSectionsFunctor X U.val).map (idealEvaluation X α F J)).hom =
      idealSectionSpan X α F J U.val := by
  let S := idealSectionsFunctor X U.val
  let P := idealSectionSpan X α F J U.val
  let e := S.map (idealEvaluation X α F J)
  let c := S.mapCocone (Cofan.mk _ (Sigma.ι (fun _ : J => F)))
  have hc : IsColimit c := QuasiCoherent.affineOpenSectionsIsColimit U
    (fun _ => (inferInstance : F.IsQuasicoherent)) (coproductIsCoproduct (fun _ : J => F))
  have hscalar (a : J) (x : Γ(F, U.val)) :
      e ((c.ι.app (Discrete.mk a)) x) =
        X.presheaf.map (homOfLE (le_top : U.val ≤ ⊤)).op (α a) • x := by
    have h := congrArg S.map
      (Sigma.ι_comp_desc (fun a : J => globalScalarEndomorphism X F (α a)) a)
    rw [S.map_comp] at h
    have hx := congrArg (fun k => k x) h
    exact hx.trans (globalScalarEndomorphism_app X F (α a) U.val x)
  have hz : e ≫ ModuleCat.ofHom P.mkQ = 0 := by
    apply hc.hom_ext
    intro a
    ext x
    change P.mkQ (e ((c.ι.app a) x)) = 0
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    apply Submodule.subset_span
    exact ⟨a.as, x, hscalar a.as x⟩
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero P).mp
    exact congrArg (fun f => f x) hz
  · apply Submodule.span_le.mpr
    rintro y ⟨a, x, rfl⟩
    exact ⟨(c.ι.app (Discrete.mk a)) x, hscalar a x⟩

/-- The actual ideal-generated image sheaf has the expected affine section submodule. -/
theorem idealMultiple_affine_range (J : Ideal A) (U : X.affineOpens) :
    LinearMap.range ((idealMultipleι X α F J).val.app (op U.val)).hom =
      idealSectionSpan X α F J U.val := by
  let := QuasiCoherent.quasicoherent_coproduct (fun _ : J => F)
  exact (affineOpenSections_categoricalImage_range U (idealEvaluation X α F J)).trans
    (idealEvaluation_affine_range X α F J U)

end AlgebraicGeometry.Scheme.Modules
