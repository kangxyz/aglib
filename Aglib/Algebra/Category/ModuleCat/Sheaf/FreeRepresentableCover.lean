/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.FreeRepresentable
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation.FiniteCover

/-! # Original free module generators on binary site covers

The original free representable maps act by restriction of actual sections.
A covering pullback square of monomorphisms therefore gives a pushout of the
original native module generators. Gluing is applied to the unchanged
underlying abelian sheaf; scalar forgetting is never assumed full.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf

universe c h r t

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Type r) [Ring R] [HasSheafify J (ModuleCat.{max c h r t} R)]

/-- The original generator map represents restriction along the same site map. -/
theorem freeRepresentableSectionsEquiv_naturality_left {U V : C} (f : U ⟶ V)
    (F : Sheaf J (ModuleCat.{max c h r t} R)) (b : freeRepresentable J R V ⟶ F) :
    freeRepresentableSectionsEquiv J R U F ((freeRepresentableFunctor J R).map f ≫ b) =
      F.obj.map f.op (freeRepresentableSectionsEquiv J R V F b) := by
  let P : Cᵒᵖ ⥤ Type (max c h r t) := uliftYoneda.{max c r t}.obj U
  let Q : Cᵒᵖ ⥤ Type (max c h r t) := uliftYoneda.{max c r t}.obj V
  let K : (Cᵒᵖ ⥤ Type (max c h r t)) ⥤ (Cᵒᵖ ⥤ ModuleCat.{max c h r t} R) :=
    (Functor.whiskeringRight _ _ _).obj (freeWideFunctor.{r, max c h r t} R)
  let q : P ⟶ Q := uliftYoneda.{max c r t}.map f
  let b₀ : (presheafToSheaf J (ModuleCat.{max c h r t} R)).obj (K.obj Q) ⟶ F := b
  let a : K.obj Q ⟶ F.obj :=
    (sheafificationAdjunction J (ModuleCat.{max c h r t} R)).homEquiv (K.obj Q) F b₀
  let z : Q ⟶ F.obj ⋙ forget (ModuleCat.{max c h r t} R) :=
    ((freeWideForgetAdjunction.{r, max c h t} R).whiskerRight Cᵒᵖ).homEquiv Q F.obj a
  have h₀ : (sheafificationAdjunction J (ModuleCat.{max c h r t} R)).homEquiv (K.obj P) F
      ((presheafToSheaf J (ModuleCat.{max c h r t} R)).map (K.map q) ≫ b₀) = K.map q ≫ a :=
    (sheafificationAdjunction J (ModuleCat.{max c h r t} R)).homEquiv_naturality_left (K.map q) b₀
  have h₁ : ((freeWideForgetAdjunction.{r, max c h t} R).whiskerRight Cᵒᵖ).homEquiv
      P F.obj (K.map q ≫ a) = q ≫ z :=
    ((freeWideForgetAdjunction.{r, max c h t} R).whiskerRight Cᵒᵖ).homEquiv_naturality_left q a
  have hz := (congrArg (fun (v : K.obj P ⟶ F.obj) =>
    ((freeWideForgetAdjunction.{r, max c h t} R).whiskerRight Cᵒᵖ).homEquiv P F.obj v) h₀).trans h₁
  have hz' := congrArg
    (fun (v : P ⟶ F.obj ⋙ forget (ModuleCat.{max c h r t} R)) =>
      uliftYonedaEquiv.{max c r t} v) hz
  exact hz'.trans (uliftYonedaEquiv_naturality z f.op).symm

private abbrev coverUnderlying (F : Sheaf J (ModuleCat.{max c h r t} R)) :
    Sheaf J AddCommGrpCat.{max c h r t} :=
  (sheafCompose J (forget₂ (ModuleCat.{max c h r t} R) AddCommGrpCat.{max c h r t})).obj F

open CategoryTheory.Sheaf.TorsionFinitePresentation in
/-- The literal native free-module square associated to an original binary
covering pullback is a pushout. -/
theorem freeRepresentable_square_isPushout (sq : Square C)
    [Mono sq.f₂₄] [Mono sq.f₃₄] (hp : sq.IsPullback)
    (hcover : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄) :
    (sq.map (freeRepresentableFunctor.{r, c, h, t} J R)).IsPushout := by
  let K := freeRepresentableFunctor.{r, c, h, t} J R
  let E₀ (s : PushoutCocone (K.map sq.f₁₂) (K.map sq.f₁₃)) :=
    freeRepresentableSectionsEquiv J R sq.X₂ s.pt s.inl
  let E₁ (s : PushoutCocone (K.map sq.f₁₂) (K.map sq.f₁₃)) :=
    freeRepresentableSectionsEquiv J R sq.X₃ s.pt s.inr
  have he (s : PushoutCocone (K.map sq.f₁₂) (K.map sq.f₁₃)) :
      s.pt.obj.map sq.f₁₂.op (E₀ s) = s.pt.obj.map sq.f₁₃.op (E₁ s) :=
    (freeRepresentableSectionsEquiv_naturality_left J R sq.f₁₂ s.pt s.inl).symm.trans
      ((congrArg (freeRepresentableSectionsEquiv J R sq.X₁ s.pt) s.condition).trans
        (freeRepresentableSectionsEquiv_naturality_left J R sq.f₁₃ s.pt s.inr))
  let z (s : PushoutCocone (K.map sq.f₁₂) (K.map sq.f₁₃)) :=
    FiniteCover.glue.{max c r t} J sq hp hcover (coverUnderlying J R s.pt)
      (E₀ s) (E₁ s) (he s)
  let d (s : PushoutCocone (K.map sq.f₁₂) (K.map sq.f₁₃)) : K.obj sq.X₄ ⟶ s.pt :=
    (freeRepresentableSectionsEquiv J R sq.X₄ s.pt).symm (z s)
  have hd (s : PushoutCocone (K.map sq.f₁₂) (K.map sq.f₁₃)) :
      freeRepresentableSectionsEquiv J R sq.X₄ s.pt (d s) = z s :=
    (freeRepresentableSectionsEquiv J R sq.X₄ s.pt).apply_symm_apply (z s)
  have h₀ (s : PushoutCocone (K.map sq.f₁₂) (K.map sq.f₁₃)) : K.map sq.f₂₄ ≫ d s = s.inl := by
    apply (freeRepresentableSectionsEquiv J R sq.X₂ s.pt).injective
    rw [freeRepresentableSectionsEquiv_naturality_left, hd]
    exact FiniteCover.glue_left.{max c r t} J sq hp hcover (coverUnderlying J R s.pt)
      (E₀ s) (E₁ s) (he s)
  have h₁ (s : PushoutCocone (K.map sq.f₁₂) (K.map sq.f₁₃)) : K.map sq.f₃₄ ≫ d s = s.inr := by
    apply (freeRepresentableSectionsEquiv J R sq.X₃ s.pt).injective
    rw [freeRepresentableSectionsEquiv_naturality_left, hd]
    exact FiniteCover.glue_right.{max c r t} J sq hp hcover (coverUnderlying J R s.pt)
      (E₀ s) (E₁ s) (he s)
  apply Square.IsPushout.mk
  refine PushoutCocone.IsColimit.mk _ d h₀ h₁ ?_
  intro s m hm₀ hm₁
  apply (freeRepresentableSectionsEquiv J R sq.X₄ s.pt).injective
  apply FiniteCover.sections_ext.{max c r t} J sq hp hcover (coverUnderlying J R s.pt)
  · exact (freeRepresentableSectionsEquiv_naturality_left J R sq.f₂₄ s.pt m).symm.trans
      ((congrArg (freeRepresentableSectionsEquiv J R sq.X₂ s.pt) hm₀).trans
        ((congrArg (freeRepresentableSectionsEquiv J R sq.X₂ s.pt) (h₀ s)).symm.trans
          (freeRepresentableSectionsEquiv_naturality_left J R sq.f₂₄ s.pt (d s))))
  · exact (freeRepresentableSectionsEquiv_naturality_left J R sq.f₃₄ s.pt m).symm.trans
      ((congrArg (freeRepresentableSectionsEquiv J R sq.X₃ s.pt) hm₁).trans
        ((congrArg (freeRepresentableSectionsEquiv J R sq.X₃ s.pt) (h₁ s)).symm.trans
          (freeRepresentableSectionsEquiv_naturality_left J R sq.f₃₄ s.pt (d s))))

end ModuleCat.Sheaf
