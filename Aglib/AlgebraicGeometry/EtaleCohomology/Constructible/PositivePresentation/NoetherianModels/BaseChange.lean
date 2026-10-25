/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.GenuineModules
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineObjects

/-! # Original bounded stages under affine scheme base change

The original inverse-image functor restricts to the actual full category of
n-killed coefficients and preserves its colimits. Along an affine scheme
map, the original affine-etale generators still have affine source.
The native free-generator comparison and finite-colimit closure therefore
retain the original stage predicate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

/-- The actual inverse image, restricted to the original killed-coefficient
full subcategories. Its objects and underlying arrows are the original ones. -/
def boundedInverseImage {X S : Scheme.{u}} (f : S ⟶ X) (n : ℕ) :
    BoundedPresentation.Coefficient X n ⥤ BoundedPresentation.Coefficient S n :=
  (TorsionZMod.killedSheaves S.smallEtaleTopology n).lift
    (BoundedPresentation.inclusion X n ⋙ inverseImage f) (fun F => by
      change n • 𝟙 ((inverseImage f).obj F.obj) = 0
      simpa using congrArg (fun a => (inverseImage f).map a) F.property)

/-- The full inclusion recovers the original underlying inverse image. -/
def boundedInverseImageUnderlyingIso {X S : Scheme.{u}} (f : S ⟶ X) (n : ℕ) :
    boundedInverseImage f n ⋙ BoundedPresentation.inclusion S n ≅
      BoundedPresentation.inclusion X n ⋙ inverseImage f :=
  (TorsionZMod.killedSheaves S.smallEtaleTopology n).liftCompιIso
    (BoundedPresentation.inclusion X n ⋙ inverseImage f) _

instance boundedInverseImage_preservesColimits {X S : Scheme.{u}}
    (f : S ⟶ X) (n : ℕ) :
    PreservesColimitsOfSize.{u + 1, u + 1} (boundedInverseImage f n) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (boundedInverseImage f n ⋙ BoundedPresentation.inclusion S n) :=
    preservesColimits_of_natIso (boundedInverseImageUnderlyingIso f n).symm
  exact preservesColimits_of_reflects_of_preserves
    (boundedInverseImage f n) (BoundedPresentation.inclusion S n)

/-- Original coefficient isomorphisms lift through the full bounded inclusion. -/
def boundedIso {X : Scheme.{u}} {n : ℕ}
    {F G : BoundedPresentation.Coefficient X n} (e : F.obj ≅ G.obj) : F ≅ G :=
  ObjectProperty.isoMk _ e

/-- Original inverse-image composition in the actual bounded categories. -/
def boundedInverseImageComp {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (n : ℕ) :
    boundedInverseImage (g ≫ f) n ≅ boundedInverseImage f n ⋙ boundedInverseImage g n :=
  NatIso.ofComponents (fun F => boundedIso ((inverseImageComp f g).app F.obj)) (by
    intro F G a
    apply ObjectProperty.hom_ext
    exact (inverseImageComp f g).hom.naturality a.hom)

/-- The original triangle comparison, lifted without changing its maps. -/
def boundedPullbackTriangleIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ X) (a : Y ⟶ Z) (h : a ≫ g = f) (n : ℕ) :
    boundedInverseImage f n ≅ boundedInverseImage g n ⋙ boundedInverseImage a n :=
  NatIso.ofComponents (fun F => boundedIso ((pullbackTriangleIso f g a h).app F.obj)) (by
    intro F G b
    apply ObjectProperty.hom_ext
    exact (pullbackTriangleIso f g a h).hom.naturality b.hom)

/-- The pullback of an original affine-etale generator along an affine map
has an actual affine-etale model and the native original free-sheaf iso. -/
theorem exists_affineGeneratorInverseImageIso {X S : Scheme.{u}}
    (f : S ⟶ X) [IsAffineHom f] (n : ℕ) (U : X.AffineEtale) :
    ∃ V : S.AffineEtale,
      Nonempty ((boundedInverseImage f n).obj
        (BoundedPresentation.free X n ((Scheme.AffineEtale.Spec X).obj U)) ≅
          BoundedPresentation.free S n ((Scheme.AffineEtale.Spec S).obj V)) := by
  let W : S.Etale := (siteBaseChange f).obj ((Scheme.AffineEtale.Spec X).obj U)
  have htotal : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
    change IsAffine (Spec U.left.unop)
    infer_instance
  have : IsAffine W.left := by
    change IsAffine (pullback ((Scheme.AffineEtale.Spec X).obj U).hom f)
    let P : MorphismProperty Scheme.{u} := @IsAffineHom
    let : P.IsStableUnderBaseChange := isAffineHom_isStableUnderBaseChange
    have hfst : IsAffineHom (pullback.fst ((Scheme.AffineEtale.Spec X).obj U).hom f) :=
      MorphismProperty.pullback_fst (P := P) _ _ (inferInstance : IsAffineHom f)
    exact @isAffine_of_isAffineHom
      (pullback ((Scheme.AffineEtale.Spec X).obj U).hom f)
      ((Scheme.AffineEtale.Spec X).obj U).left
      (pullback.fst ((Scheme.AffineEtale.Spec X).obj U).hom f) hfst htotal
  let V := EtaleAffineBasis.affineModel W
  let e : (inverseImage f).obj
      (freeZModRepresentable.{u + 1} X.smallEtaleTopology n
        ((Scheme.AffineEtale.Spec X).obj U)) ≅
      freeZModRepresentable.{u + 1} S.smallEtaleTopology n
        ((Scheme.AffineEtale.Spec S).obj V) :=
    freeZModRepresentableInverseImageIso f n ((Scheme.AffineEtale.Spec X).obj U) ≪≫
      freeZModRepresentableIsoOfEtaleIso n (EtaleAffineBasis.affineModelIso W).symm
  exact ⟨V, ⟨boundedIso e⟩⟩

/-- The original native stage predicate is stable under the actual affine
base changes used in the projective-line coefficient-ring system. -/
theorem finiteColimitStage_inverseImage {X S : Scheme.{u}}
    (f : S ⟶ X) [IsAffineHom f] (n : ℕ)
    (F : BoundedPresentation.Coefficient X n)
    (hF : BoundedPresentation.finiteColimitStages X n F) :
    BoundedPresentation.finiteColimitStages S n ((boundedInverseImage f n).obj F) := by
  let P := BoundedPresentation.finiteColimitStages S n
  let Q : ObjectProperty (BoundedPresentation.Coefficient X n) :=
    P.inverseImage (boundedInverseImage f n)
  have : P.IsClosedUnderIsomorphisms := by
    dsimp only [P, BoundedPresentation.finiteColimitStages]
    infer_instance
  have : Q.IsClosedUnderIsomorphisms := by
    dsimp only [Q]
    infer_instance
  have hgen : BoundedPresentation.generators X n ≤ Q := by
    rintro F ⟨U⟩
    obtain ⟨V, ⟨e⟩⟩ := exists_affineGeneratorInverseImageIso f n U
    have hp : P (BoundedPresentation.free S n ((Scheme.AffineEtale.Spec S).obj V)) :=
      (BoundedPresentation.generators S n).le_colimitsCardinalClosure
        Cardinal.aleph0.{u + 1} _ ⟨V⟩
    exact P.prop_of_iso e.symm hp
  have hclosure : BoundedPresentation.finiteColimitStages X n ≤ Q := by
    apply (BoundedPresentation.generators X n).colimitsCardinalClosure_le
      Cardinal.aleph0.{u + 1} ?_ hgen
    intro J _ hJ
    have : P.IsClosedUnderColimitsOfShape J :=
      (BoundedPresentation.generators S n).isClosedUnderColimitsOfShape_colimitsCardinalClosure
        Cardinal.aleph0.{u + 1} J hJ
    dsimp only [Q]
    infer_instance
  exact hclosure F hF

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
