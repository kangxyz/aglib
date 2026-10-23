/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteHypercoverColimit
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Colimit cocones detected on finite sheaf matching diagrams

An actual presheaf cocone whose members and point satisfy the sheaf condition
is colimiting at an object if it is colimiting on the components of one finite
one-hypercover and the coefficient colimit preserves finite limits. The original
cocone maps, both relation arrows, and all universes are retained.
-/

@[expose] public noncomputable section

namespace CategoryTheory.GrothendieckTopology.OneHypercover

open Limits Opposite

universe u v w uA vA uI vI

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type uA} [Category.{vA} A] {U : C}
  (E : J.OneHypercover.{w} U)

/-- An actual presheaf map is invertible at the target when it is invertible on
one-hypercover components and both original matching cones are limiting. -/
theorem isIso_app_of_isLimitMultifork
    {P Q : Cᵒᵖ ⥤ A} (τ : P ⟶ Q)
    (hP : IsLimit (E.multifork P)) (hQ : IsLimit (E.multifork Q))
    [hX : ∀ i, IsIso (τ.app (op (E.X i)))]
    [hY : ∀ i j (k : E.I₁ i j), IsIso (τ.app (op (E.Y k)))] :
    IsIso (τ.app (op U)) := by
  let e : (E.multicospanIndex P).multicospan ≅ (E.multicospanIndex Q).multicospan :=
    WalkingMulticospan.functorExt
      (fun i ↦ @asIso _ _ _ _ (τ.app (op (E.X i))) (hX i))
      (fun i ↦ @asIso _ _ _ _ (τ.app (op (E.Y i.2))) (hY _ _ i.2))
      (fun i ↦ τ.naturality (E.p₁ i.2).op)
      (fun i ↦ τ.naturality (E.p₂ i.2).op)
  let hc := (IsLimit.postcomposeHomEquiv e (E.multifork P)).symm hP
  have heq : τ.app (op U) = (hc.conePointUniqueUpToIso hQ).hom := by
    apply Multifork.IsLimit.hom_ext hQ
    intro i
    have hi := (hc.conePointUniqueUpToIso_hom_comp hQ
      (WalkingMulticospan.left i)).symm
    have hi' : P.map (E.f i).op ≫ τ.app (op (E.X i)) =
        (hc.conePointUniqueUpToIso hQ).hom ≫ (E.multifork Q).ι i := hi
    exact (τ.naturality (E.f i).op).symm.trans hi'
  rw [heq]
  exact Iso.isIso_hom _

variable {I : Type uI} [Category.{vI} I] [HasColimitsOfShape I A]

/-- An evaluated cocone certificate makes the original pointwise descent map invertible. -/
theorem isIso_pointwiseDesc_app_of_isColimit (G : I ⥤ Cᵒᵖ ⥤ A) (c : Cocone G)
    (V : Cᵒᵖ) (h : IsColimit (((evaluation Cᵒᵖ A).obj V).mapCocone c)) :
    IsIso (((pointwiseIsColimit G).desc c).app V) := by
  have h' := (IsColimit.nonempty_isColimit_iff_isIso_desc
    (isColimitOfPreserves ((evaluation Cᵒᵖ A).obj V) (pointwiseIsColimit G))).mp ⟨h⟩
  simpa only [preserves_desc_mapCocone, Functor.mapCocone_pt,
    evaluation_obj_obj, evaluation_obj_map] using h'

/-- Finite original sheaf matching transports actual component colimit
certificates to the actual target cocone. -/
def isColimitEvaluationOfFiniteMatching
    [Finite E.I₀] [∀ i j, Finite (E.I₁ i j)]
    [PreservesFiniteLimits (colim (J := I) (C := A))]
    (G : I ⥤ Cᵒᵖ ⥤ A) (c : Cocone G)
    (hG : ∀ i, Presheaf.IsSheaf J (G.obj i)) (hc : Presheaf.IsSheaf J c.pt)
    (hX : ∀ i, IsColimit (((evaluation Cᵒᵖ A).obj (op (E.X i))).mapCocone c))
    (hY : ∀ i j (k : E.I₁ i j),
      IsColimit (((evaluation Cᵒᵖ A).obj (op (E.Y k))).mapCocone c)) :
    IsColimit (((evaluation Cᵒᵖ A).obj (op U)).mapCocone c) := by
  let : Finite E.multicospanShape.L := inferInstanceAs (Finite E.I₀)
  let : Finite E.multicospanShape.R :=
    inferInstanceAs (Finite (Σ ij : E.I₀ × E.I₀, E.I₁ ij.1 ij.2))
  let P : Cᵒᵖ ⥤ I ⥤ A := G.flip
  let τ : (pointwiseCocone G).pt ⟶ c.pt := (pointwiseIsColimit G).desc c
  have hP : IsLimit (E.multifork P) := by
    apply evaluationJointlyReflectsLimits
    intro i
    exact (Multifork.isLimitMapEquiv (E.multifork P) ((evaluation I A).obj i)).symm
      (E.isLimitMultifork ⟨G.obj i, hG i⟩)
  let (i : E.I₀) : IsIso (τ.app (op (E.X i))) := isIso_pointwiseDesc_app_of_isColimit G c _ (hX i)
  let (i j : E.I₀) (k : E.I₁ i j) : IsIso (τ.app (op (E.Y k))) :=
    isIso_pointwiseDesc_app_of_isColimit G c _ (hY i j k)
  have hτ : IsIso (τ.app (op U)) := E.isIso_app_of_isLimitMultifork τ
    (Multifork.isLimitMapOfPreserves (E.multifork P) colim hP)
    (E.isLimitMultifork ⟨c.pt, hc⟩)
  let H := isColimitOfPreserves ((evaluation Cᵒᵖ A).obj (op U)) (pointwiseIsColimit G)
  have : IsIso (H.desc (((evaluation Cᵒᵖ A).obj (op U)).mapCocone c)) := by
    simpa only [H, τ, preserves_desc_mapCocone, Functor.mapCocone_pt,
      evaluation_obj_obj, evaluation_obj_map] using hτ
  exact H.ofPointIso

end CategoryTheory.GrothendieckTopology.OneHypercover
