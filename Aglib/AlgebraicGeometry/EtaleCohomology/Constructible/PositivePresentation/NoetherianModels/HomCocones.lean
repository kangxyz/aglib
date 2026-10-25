/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRightTailColimit
public import Mathlib.CategoryTheory.Presentable.Limits

/-! # Original Hom cocones for native bounded finite-colimit stages

For a fixed filtered cocone, the source objects whose original Hom cocones
are colimiting are closed under finite colimits. The native finite-limit
interchange supplies the full naturality at that boundary. Original varying
H0 continuity supplies the affine-etale free generators of the bounded
right-image-tail cocone. Closure then supplies every native bounded stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

/-- The original bounded free-generator section equivalence as a whole
natural isomorphism in its bounded target coefficient. -/
def boundedFreeSectionsIso (X : Scheme.{u}) (n : ℕ) (U : X.Etale) :
    coyoneda.obj (op (BoundedPresentation.free X n U)) ≅
      BoundedPresentation.inclusion X n ⋙
        (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents (fun F => (BoundedPresentation.sectionsEquiv X n U F).toIso) (by
    intro F G q
    ext a
    exact BoundedPresentation.sectionsEquiv_naturality X n U a q)

/-- The original fixed-cocone Hom comparison passes from the native free
generators to their actual finite-colimit closure. -/
def canonicalHomCoconeIsColimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (X : Scheme.{u}) (n : ℕ)
    {D : J ⥤ BoundedPresentation.Coefficient X n} (c : Cocone D)
    (hgen : ∀ U : X.AffineEtale,
      IsColimit ((coyoneda.obj
        (op (BoundedPresentation.free X n ((Scheme.AffineEtale.Spec X).obj U)))).mapCocone c))
    (A : BoundedPresentation.Coefficient X n)
    (hA : BoundedPresentation.finiteColimitStages X n A) :
    IsColimit ((coyoneda.obj (op A)).mapCocone c) := by
  let Q : ObjectProperty (BoundedPresentation.Coefficient X n) :=
    fun A => Nonempty (IsColimit ((coyoneda.obj (op A)).mapCocone c))
  have : Q.IsClosedUnderIsomorphisms := {
    of_iso := by
      intro A B e hA
      obtain ⟨hc⟩ := hA
      exact ⟨IsColimit.mapCoconeEquiv (coyoneda.mapIso e.op).symm hc⟩ }
  have hgenerators : BoundedPresentation.generators X n ≤ Q := by
    rintro A ⟨U⟩
    exact ⟨hgen U⟩
  have hclosure : BoundedPresentation.finiteColimitStages X n ≤ Q := by
    apply (BoundedPresentation.generators X n).colimitsCardinalClosure_le
      Cardinal.aleph0.{u + 1} ?_ hgenerators
    intro K _ hK
    have hfinite : Finite (Arrow K) := by
      simpa only [hasCardinalLT_aleph0_iff] using hK
    have hKop : HasCardinalLT (Arrow Kᵒᵖ) Cardinal.aleph0.{u} := by
      rw [hasCardinalLT_arrow_op_iff, hasCardinalLT_aleph0_iff]
      exact hfinite
    refine { colimitsOfShape_le := ?_ }
    rintro A ⟨p⟩
    let cA : Cocone p.diag := Cocone.mk A p.ι
    have hcA : IsColimit cA := p.isColimit
    let t := coyoneda.mapCone cA.op
    have ht : IsLimit t := isLimitOfPreserves coyoneda hcA.op
    let : IsCardinalFiltered J Cardinal.aleph0.{u} :=
      (isCardinalFiltered_aleph0_iff J).2 inferInstance
    refine ⟨Functor.Accessible.Limits.isColimitMapCocone t
      (fun B => isLimitOfPreserves
        ((CategoryTheory.evaluation (BoundedPresentation.Coefficient X n)
          (Type (u + 1))).obj B) ht)
      Cardinal.aleph0.{u} hKop c ?_⟩
    intro k
    exact Classical.choice (p.prop_diag_obj k.unop)
  exact Classical.choice (hclosure A hA)

private theorem nsmul_identity_colimit
    {J : Type u} [SmallCategory J] {X : Scheme.{u}}
    (n : ℕ) (D : J ⥤ AbelianSheaf.{u, u + 1} X) [HasColimit D]
    (hD : ∀ j, n • 𝟙 (D.obj j) = 0) : n • 𝟙 (colimit D) = 0 := by
  apply colimit.hom_ext
  intro j
  have h := congrArg (fun a => a ≫ colimit.ι D j) (hD j)
  simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
    Category.comp_id, zero_comp, comp_zero] using h

/-- The actual bounded lift of a supplied original coefficient diagram. -/
def boundedDiagram {J : Type u} [SmallCategory J] {X : Scheme.{u}}
    (n : ℕ) (D : J ⥤ AbelianSheaf.{u, u + 1} X)
    (hD : ∀ j, n • 𝟙 (D.obj j) = 0) :
    J ⥤ BoundedPresentation.Coefficient X n :=
  (TorsionZMod.killedSheaves X.smallEtaleTopology n).lift D hD

/-- Lift an original cocone into the full bounded category, retaining every
underlying original object, leg and naturality equation. -/
def boundedCocone {J : Type u} [SmallCategory J] {X : Scheme.{u}}
    (n : ℕ) (D : J ⥤ AbelianSheaf.{u, u + 1} X)
    (hD : ∀ j, n • 𝟙 (D.obj j) = 0) (c : Cocone D) (hc : n • 𝟙 c.pt = 0) :
    Cocone (boundedDiagram n D hD) where
  pt := ⟨c.pt, hc⟩
  ι := {
    app j := ObjectProperty.homMk (c.ι.app j)
    naturality {j k} f := by
      apply ObjectProperty.hom_ext
      exact c.ι.naturality f }

open Continuity

variable {I : Type u} [SmallCategory I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (F : DiagramCoefficientSystem X)
  (n : ℕ) (hF : ∀ i, n • 𝟙 (F.obj i) = 0)

include hF in
/-- The original right-image-tail coefficients retain the common annihilator. -/
theorem rightTail_killed (i : I) (a : Under i) :
    n • 𝟙 ((diagramRightTail X F i).obj a) = 0 := by
  change n • 𝟙 ((directImage (X.map a.hom).unop).obj (F.obj a.right)) = 0
  simpa using congrArg (fun f => (directImage (X.map a.hom).unop).map f) (hF a.right)

variable (c : Cocone X) [HasColimit (coneCoefficientFunctor X c F)]

include hF in
private theorem limitCoefficient_killed :
    n • 𝟙 (colimit (coneCoefficientFunctor X c F)) = 0 := by
  apply nsmul_identity_colimit
  intro i
  change n • 𝟙 ((inverseImage (c.ι.app i).unop).obj (F.obj i)) = 0
  simpa using congrArg (fun f => (inverseImage (c.ι.app i).unop).map f) (hF i)

include hF in
/-- The point of the original right-image-tail cocone retains the annihilator. -/
theorem rightTailPoint_killed (i : I) :
    n • 𝟙 (diagramRightTailCocone X F c i).pt = 0 := by
  change n • 𝟙 ((directImage (c.ι.app i).unop).obj
    (colimit (coneCoefficientFunctor X c F))) = 0
  simpa using
    congrArg (fun f => (directImage (c.ι.app i).unop).map f)
      (limitCoefficient_killed X F n hF c)

include hF in
/-- The original fixed-stage right-image tail in the actual bounded category. -/
def boundedRightTail (i : I) :
    Under i ⥤ BoundedPresentation.Coefficient (X.obj i).unop n :=
  boundedDiagram n (diagramRightTail X F i) (rightTail_killed X F n hF i)

/-- The literal original right-image cocone, with only its killed equation
added to place it in the full bounded coefficient category. -/
def boundedRightTailCocone (i : I) : Cocone (boundedRightTail X F n hF i) :=
  boundedCocone n (diagramRightTail X F i) (rightTail_killed X F n hF i)
    (diagramRightTailCocone X F c i) (rightTailPoint_killed X F n hF c i)

/-- Native varying H0 and source finite-colimit closure prove the original
Hom cocone colimiting for every modeled bounded canonical stage. -/
def isColimitBoundedHomRightTail [IsFiltered I]
    (hc : IsColimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop]
    (i : I) (A : BoundedPresentation.Coefficient (X.obj i).unop n)
    (hA : BoundedPresentation.finiteColimitStages (X.obj i).unop n A) :
    IsColimit ((coyoneda.obj (op A)).mapCocone
      (boundedRightTailCocone X F n hF c i)) := by
  apply canonicalHomCoconeIsColimit (X.obj i).unop n
    (boundedRightTailCocone X F n hF c i) ?_ A hA
  intro U
  let T := (Scheme.AffineEtale.Spec (X.obj i).unop).obj U
  have : IsAffine T.left := by
    change IsAffine (Spec U.left.unop)
    infer_instance
  let E := boundedFreeSectionsIso (X.obj i).unop n T
  have hsections := isColimitDiagramRightTailEvaluation X c hc i T F
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have hbounded : IsColimit
      ((BoundedPresentation.inclusion (X.obj i).unop n ⋙
        (sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op T) ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).mapCocone
            (boundedRightTailCocone X F n hF c i)) :=
    isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1}) hsections
  exact IsColimit.mapCoconeEquiv E.symm hbounded

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
