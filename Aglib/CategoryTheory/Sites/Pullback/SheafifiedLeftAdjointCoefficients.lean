/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Sheafified coefficient left adjoints and the original pullback

The coefficient functor need not preserve sheaves or limits. Its actual right
adjoint does preserve sheaves. Commuting that right adjoint with the original
site pushforward, and uniqueness of left adjoints, compares the original
pullback with coefficient composition followed by sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor

universe uC vC uD vD uA vA uB vB

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] (T : A ⥤ B) (H : B ⥤ A) (adj : T ⊣ H)

/-- The same right-adjoint coefficient action commutes with the actual site
pushforward: both sides have the same original values and restriction maps. -/
def sheafPushforwardRightAdjointCoefficientIso
    [J.HasSheafCompose H] [K.HasSheafCompose H] :
    sheafCompose K H ⋙ G.sheafPushforwardContinuous A J K ≅
      G.sheafPushforwardContinuous B J K ⋙ sheafCompose J H :=
  NatIso.ofComponents
    (fun P => ObjectProperty.isoMk _ (Functor.associator G.op P.obj H).symm)
    (by
      intro P Q a
      apply ObjectProperty.hom_ext
      ext U
      change H.map (a.hom.app (G.op.obj U)) ≫ 𝟙 _ =
        𝟙 _ ≫ H.map (a.hom.app (G.op.obj U))
      simp only [Category.comp_id, Category.id_comp])

variable [HasWeakSheafify J B] [HasWeakSheafify K B]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [(G.sheafPushforwardContinuous B J K).IsRightAdjoint]

/-- The original chosen site pullback commutes with the actual sheafified
coefficient left adjoint, without requiring that coefficient functor to
preserve limits or sheaves. -/
def sheafPullbackSheafifiedLeftAdjointIso :
    G.sheafPullback A J K ⋙ Sheaf.composeAndSheafify K T ≅
      Sheaf.composeAndSheafify J T ⋙ G.sheafPullback B J K := by
  let : H.IsRightAdjoint := adj.isRightAdjoint
  exact (((G.sheafAdjunctionContinuous A J K).comp (Sheaf.adjunction K adj)).ofNatIsoRight
    (sheafPushforwardRightAdjointCoefficientIso G J K H)).leftAdjointUniq
      ((Sheaf.adjunction J adj).comp (G.sheafAdjunctionContinuous B J K))

end CategoryTheory.Functor

namespace CategoryTheory

universe uC vC uA vA uB vB

variable {C : Type uC} [Category.{vC} C]
  {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  (J : GrothendieckTopology C) (T : A ⥤ B) (H : B ⥤ A) (adj : T ⊣ H)
  [HasWeakSheafify J A] [HasWeakSheafify J B]

/-- Constant coefficients are transported by the same sheafification comparison
and the original constant-presheaf coefficient isomorphism. -/
def constantSheafSheafifiedLeftAdjointIso :
    constantSheaf J A ⋙ Sheaf.composeAndSheafify J T ≅
      T ⋙ constantSheaf J B := by
  let : T.IsLeftAdjoint := adj.isLeftAdjoint
  exact isoWhiskerLeft (Functor.const Cᵒᵖ)
      (presheafToSheafCompComposeAndSheafifyIso J T) ≪≫
    isoWhiskerRight (Functor.compConstIso Cᵒᵖ T).symm (presheafToSheaf J B)

end CategoryTheory
