/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.CategoryTheory.Sites.Pullback.FlatCoefficients
public import Aglib.CategoryTheory.Sites.Pullback.RepresentedTarget
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Aglib.CategoryTheory.Adjunction.Mates.RepresentedCoherence
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Base change of actual represented additive coefficients

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen
source basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
variable {X S : Scheme.{u}}

/-- The actual pulled-back commutative group object. -/
abbrev baseChangedGroup (f : S ⟶ X) (H : Grp (Over X)) : Grp (Over S) :=
  (Over.pullback f).mapGrp.obj H

instance baseChangedGroup_comm (f : S ⟶ X) (H : Grp (Over X)) [IsCommMonObj H.X] :
    IsCommMonObj (baseChangedGroup f H).X := by
  exact inferInstanceAs (IsCommMonObj ((Over.pullback f).obj H.X))

instance baseChangedGroup_etale (f : S ⟶ X) (H : Grp (Over X)) [Etale H.X.hom] :
    Etale (baseChangedGroup f H).X.hom := by
  change Etale (Limits.pullback.snd H.X.hom f)
  infer_instance

/-- The canonical map sends a section to its scheme-theoretic pullback. -/
def representedBaseChangeUnit (f : S ⟶ X) (H : Grp (Over X)) [IsCommMonObj H.X] :
    representedPresheaf H ⟶ (siteBaseChange f).op ⋙ representedPresheaf (baseChangedGroup f H) where
  app U := AddCommGrpCat.ofHom {
    toFun t := ⟨Additive.ofMul ((Over.pullback f).map t.down.toMul)⟩
    map_zero' := by
      apply ULift.ext
      exact congrArg Additive.ofMul ((Over.pullback f).map_one (M := H.X))
    map_add' t t' := by
      apply ULift.ext
      exact congrArg Additive.ofMul ((Over.pullback f).map_mul t.down.toMul t'.down.toMul) }
  naturality {U V} g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro t
    change ULift.up (Additive.ofMul ((Over.pullback f).map
      ((Scheme.Etale.forget X).map g.unop ≫ t.down.toMul))) =
      ULift.up (Additive.ofMul ((Over.pullback f).map ((Scheme.Etale.forget X).map g.unop) ≫
        (Over.pullback f).map t.down.toMul))
    rw [Functor.map_comp]

/-- For an étale coefficient scheme, its underlying small-site presheaf is
represented by that scheme, with explicit universe and additive transports. -/
def representedUnderlyingIso (H : Grp (Over X)) [IsCommMonObj H.X] [Etale H.X.hom] :
    uliftYoneda.{u + 1}.obj (Scheme.Etale.mk H.X.hom) ≅
      representedPresheaf H ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents (fun U => Equiv.toIso
    (Equiv.ulift.trans
      (((Functor.FullyFaithful.ofFullyFaithful (Scheme.Etale.forget X)).homEquiv.trans
        Additive.ofMul).trans Equiv.ulift.symm))) (by
    intro U V g
    ext t
    change ULift.up (Additive.ofMul ((Scheme.Etale.forget X).map (g.unop ≫ t.down))) =
      ULift.up (Additive.ofMul ((Scheme.Etale.forget X).map g.unop ≫
        (Scheme.Etale.forget X).map t.down))
    rw [Functor.map_comp])

/-- Forgetting addition, the canonical base-change map is the Yoneda left
Kan-extension unit, transported through the actual represented presheaves. -/
theorem representedBaseChangeUnit_forget_isLeftKan (f : S ⟶ X)
    (H : Grp (Over X)) [IsCommMonObj H.X] [Etale H.X.hom] :
    (representedPresheaf (baseChangedGroup f H) ⋙ CategoryTheory.forget AddCommGrpCat.{u +
      1}).IsLeftKanExtension
      (Functor.whiskerRight (representedBaseChangeUnit f H) (CategoryTheory.forget
        AddCommGrpCat.{u + 1}) ≫
        (Functor.associator _ _ _).hom) := by
  apply (Functor.isLeftKanExtension_iff_of_iso₂
    (uliftYonedaMap.{u + 1} (siteBaseChange f) (Scheme.Etale.mk H.X.hom))
    (Functor.whiskerRight (representedBaseChangeUnit f H) (CategoryTheory.forget AddCommGrpCat.{u
      + 1}) ≫
      (Functor.associator _ _ _).hom)
    (representedUnderlyingIso H) (representedUnderlyingIso (baseChangedGroup f H)) ?_).mp
  · infer_instance
  · ext U t
    rfl

section KanReflection
open CategoryTheory.Limits
universe a b
variable {C D : Type a} [Category.{b} C] [Category.{b} D]

/-- For a flat site functor, filtered pointwise Kan extensions of abelian
presheaves are preserved by forgetting addition. -/
theorem forget_preserves_flat_leftKan (F : C ⥤ D) [RepresentablyFlat F]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max a b}) :
    (CategoryTheory.forget AddCommGrpCat.{max a b}).PreservesLeftKanExtension P F.op := by
  exact Functor.forget_preserves_flat_leftKan.{a, b, a, b, 0} F P

/-- Reflect the universal property of a flat abelian left Kan extension
from the underlying set-valued extension. This is proved using preservation
of the filtered pointwise colimits and reflection of isomorphisms. -/
theorem abelian_isLeftKan_of_underlying (F : C ⥤ D) [RepresentablyFlat F]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max a b}) (Q : Dᵒᵖ ⥤ AddCommGrpCat.{max a b})
    (α : P ⟶ F.op ⋙ Q)
    (h : (Q ⋙ CategoryTheory.forget AddCommGrpCat.{max a b}).IsLeftKanExtension
      (Functor.whiskerRight α (CategoryTheory.forget AddCommGrpCat.{max a b}) ≫
        (Functor.associator _ _ _).hom)) : Q.IsLeftKanExtension α := by
  exact Functor.abelian_isLeftKan_of_underlying.{a, b, a, b, 0} F P Q α h

end KanReflection

/-- The canonical scheme-section map is the actual abelian presheaf left
Kan extension, with no supplied comparison premise. -/
instance representedBaseChangeUnit_isLeftKan (f : S ⟶ X)
    (H : Grp (Over X)) [IsCommMonObj H.X] [Etale H.X.hom] :
    (representedPresheaf (baseChangedGroup f H)).IsLeftKanExtension
      (representedBaseChangeUnit f H) := by
  let := flat_of_preservesFiniteLimits (siteBaseChange f)
  exact abelian_isLeftKan_of_underlying (siteBaseChange f) _ _ _
    (representedBaseChangeUnit_forget_isLeftKan f H)

/-- The same proved universal property at the actual represented-sheaf projection. -/
local instance representedSheafBaseChangeUnit_isLeftKan (f : S ⟶ X)
    (H : Grp (Over X)) [IsCommMonObj H.X] [Etale H.X.hom] :
    (representedSheaf (baseChangedGroup f H)).obj.IsLeftKanExtension
      (representedBaseChangeUnit f H) :=
  representedBaseChangeUnit_isLeftKan f H

/-- Represented additive presheaves commute with the actual pointwise left
Kan extension of the small-site base-change functor. -/
def representedPresheafBaseChangeIso (f : S ⟶ X)
    (H : Grp (Over X)) [IsCommMonObj H.X] [Etale H.X.hom] :
    (siteBaseChange f).op.lan.obj (representedPresheaf H) ≅
      representedPresheaf (baseChangedGroup f H) :=
  Functor.presheafLeftKanTargetIso (siteBaseChange f) (representedPresheaf H)
    (representedPresheaf (baseChangedGroup f H)) (representedBaseChangeUnit f H)

/-- Actual small-étale inverse image of a represented additive sheaf is
the sheaf represented by the scheme-theoretically pulled-back group object. -/
def representedSheafBaseChangeIso (f : S ⟶ X)
    (H : Grp (Over X)) [IsCommMonObj H.X] [Etale H.X.hom] :
    (inverseImage f).obj (representedSheaf H) ≅ representedSheaf (baseChangedGroup f H) := by
  let := hasSheafifyLarge X
  let := hasSheafifyLarge S
  exact Functor.sheafPullbackTargetIso (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (representedSheaf H) (representedSheaf (baseChangedGroup f H))
    (representedBaseChangeUnit f H)

/-- Scheme pullback of sections commutes with every coefficient group map. -/
theorem representedBaseChangeUnit_naturality (f : S ⟶ X)
    {H K : Grp (Over X)} [IsCommMonObj H.X] [IsCommMonObj K.X] (q : H ⟶ K) :
    (representedSheafMap q).hom ≫ representedBaseChangeUnit f K =
      representedBaseChangeUnit f H ≫ Functor.whiskerLeft (siteBaseChange f).op
        (representedSheafMap ((Over.pullback f).mapGrp.map q)).hom := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro t
  change ULift.up (Additive.ofMul ((Over.pullback f).map (t.down.toMul ≫ q.hom.hom))) =
    ULift.up (Additive.ofMul ((Over.pullback f).map t.down.toMul ≫
      (Over.pullback f).map q.hom.hom))
  rw [Functor.map_comp]

/-- The presheaf Kan-extension comparison is natural in coefficient maps. -/
theorem representedPresheafBaseChangeIso_naturality (f : S ⟶ X)
    {H K : Grp (Over X)} [IsCommMonObj H.X] [IsCommMonObj K.X]
    [Etale H.X.hom] [Etale K.X.hom] (q : H ⟶ K) :
    (siteBaseChange f).op.lan.map (representedSheafMap q).hom ≫
      (representedPresheafBaseChangeIso f K).hom =
    (representedPresheafBaseChangeIso f H).hom ≫
      (representedSheafMap ((Over.pullback f).mapGrp.map q)).hom := by
  exact Functor.presheafLeftKanTargetIso_naturality (siteBaseChange f)
    (representedBaseChangeUnit f H) (representedBaseChangeUnit f K)
    (representedSheafMap q).hom (representedSheafMap ((Over.pullback f).mapGrp.map q)).hom
    (representedBaseChangeUnit_naturality f q)

/-- Actual represented-sheaf base change is natural in coefficient maps. -/
theorem representedSheafBaseChangeIso_naturality (f : S ⟶ X)
    {H K : Grp (Over X)} [IsCommMonObj H.X] [IsCommMonObj K.X]
    [Etale H.X.hom] [Etale K.X.hom] (q : H ⟶ K) :
    (inverseImage f).map (representedSheafMap q) ≫ (representedSheafBaseChangeIso f K).hom =
      (representedSheafBaseChangeIso f H).hom ≫
        representedSheafMap ((Over.pullback f).mapGrp.map q) := by
  let := hasSheafifyLarge X
  let := hasSheafifyLarge S
  have h := Functor.sheafPullbackTargetIso_naturality (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (P := representedSheaf H) (P' := representedSheaf K)
    (Q := representedSheaf (baseChangedGroup f H))
    (Q' := representedSheaf (baseChangedGroup f K))
    (representedBaseChangeUnit f H) (representedBaseChangeUnit f K)
    (representedSheafMap q) (representedSheafMap ((Over.pullback f).mapGrp.map q))
    (representedBaseChangeUnit_naturality f q)
  exact h

namespace SchemeTorsorBaseChange

section RepresentedSheaves

variable (f : S ⟶ X) (A : Grp (Over X)) [IsCommMonObj A.X]

attribute [local instance] hasSheafifyLarge

/-- The actual coefficient section pullback, as a morphism into direct image. -/
def representedCoefficientUnit :
    representedSheaf A ⟶ (directImage f).obj (representedSheaf (baseChangedGroup f A)) :=
  ⟨representedBaseChangeUnit f A⟩

/-- The canonical represented-sheaf isomorphism has precisely the actual
scheme-section pullback as its adjunction unit. -/
theorem representedSheafBaseChangeIso_unit [Etale A.X.hom] :
    (inverseImageAdjunction f).unit.app (representedSheaf A) ≫
        (directImage f).map (representedSheafBaseChangeIso f A).hom =
      representedCoefficientUnit f A := by
  exact Functor.sheafPullbackTargetIso_unit (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (representedSheaf A) (representedSheaf (baseChangedGroup f A))
    (representedBaseChangeUnit f A)

/-- Thus the coefficient adjoint is the fixed actual represented-sheaf
base-change isomorphism, not an arbitrary identification. -/
theorem representedCoefficientUnit_adjoint [Etale A.X.hom] :
    ((inverseImageAdjunction f).homEquiv _ _).symm (representedCoefficientUnit f A) =
      (representedSheafBaseChangeIso f A).hom := by
  exact Functor.sheafPullbackTargetIso_adjoint (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (representedSheaf A) (representedSheaf (baseChangedGroup f A))
    (representedBaseChangeUnit f A)

end RepresentedSheaves

end SchemeTorsorBaseChange

namespace RepresentedBaseChange

open SchemeTorsorBaseChange

attribute [local instance] hasSheafifyLarge

/-- Literal represented coefficient units compose through the original
site comparison and the specified canonical Over pullback arrow. -/
theorem coefficientUnit_comp {T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    (A : Grp (Over X)) [IsCommMonObj A.X]
    (q : baseChangedGroup g (baseChangedGroup f A) ⟶ baseChangedGroup (g ≫ f) A)
    (hq : q.hom.hom = (Over.pullbackComp g f).inv.app A.X) :
    representedCoefficientUnit f A ≫
        (directImage f).map
          (representedCoefficientUnit g (baseChangedGroup f A) ≫
            (directImage g).map (representedSheafMap q)) ≫
        (directImageCompIso f g).hom.app (representedSheaf (baseChangedGroup (g ≫ f) A)) =
      representedCoefficientUnit (g ≫ f) A := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  let V := (Scheme.Etale.forget X).obj U.unop
  let c := Over.pullbackComp g f
  let k := (Scheme.Etale.forget T).map ((siteBaseChangeComp f g).hom.app U.unop)
  have hk : k = c.hom.app V :=
    Adjunction.RepresentedCoherence.forget_pullbackComp_hom g f
      etaleMorphismProperty.{u} (⊤ : MorphismProperty Scheme.{u}) U.unop
  change ULift.up (Additive.ofMul
      (k ≫ (Over.pullback g).map ((Over.pullback f).map a.down.toMul) ≫
        q.hom.hom)) =
    ULift.up (Additive.ofMul ((Over.pullback (g ≫ f)).map a.down.toMul))
  apply ULift.ext
  apply congrArg Additive.ofMul
  rw [hk, hq]
  exact (Category.assoc _ _ _).symm.trans
    ((c.app A.X).comp_inv_eq.mpr (c.hom.naturality a.down.toMul).symm)

/-- The original represented-sheaf comparisons compose whenever the given
coefficient arrow has the original canonical pullback-composition value.
The coefficient group need only be commutative and etale. -/
theorem iso_comp_of_hom {T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)
    (A : Grp (Over X)) [IsCommMonObj A.X] [Etale A.X.hom]
    (q : baseChangedGroup g (baseChangedGroup f A) ⟶ baseChangedGroup (g ≫ f) A)
    (hq : q.hom.hom = (Over.pullbackComp g f).inv.app A.X) :
    (inverseImageComp f g).hom.app (representedSheaf A) ≫
        (inverseImage g).map (representedSheafBaseChangeIso f A).hom ≫
        (representedSheafBaseChangeIso g (baseChangedGroup f A)).hom ≫
        representedSheafMap q =
      (representedSheafBaseChangeIso (g ≫ f) A).hom := by
  apply ((inverseImageAdjunction (g ≫ f)).homEquiv _ _).injective
  have hc : conjugateEquiv ((inverseImageAdjunction f).comp (inverseImageAdjunction g))
      (inverseImageAdjunction (g ≫ f)) (inverseImageComp f g).hom =
        (directImageCompIso f g).hom :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv
      (inverseImageAdjunction f) (inverseImageAdjunction g)
      (inverseImageAdjunction (g ≫ f)) (directImageCompIso f g)
  have hf : (inverseImageAdjunction f).homEquiv _ _
      (representedSheafBaseChangeIso f A).hom = representedCoefficientUnit f A := by
    simpa only [Adjunction.homEquiv_unit] using representedSheafBaseChangeIso_unit f A
  have hg : (inverseImageAdjunction g).homEquiv _ _
      (representedSheafBaseChangeIso g (baseChangedGroup f A)).hom =
        representedCoefficientUnit g (baseChangedGroup f A) := by
    simpa only [Adjunction.homEquiv_unit] using
      representedSheafBaseChangeIso_unit g (baseChangedGroup f A)
  have hfg : (inverseImageAdjunction (g ≫ f)).homEquiv _ _
      (representedSheafBaseChangeIso (g ≫ f) A).hom =
        representedCoefficientUnit (g ≫ f) A := by
    simpa only [Adjunction.homEquiv_unit] using
      representedSheafBaseChangeIso_unit (g ≫ f) A
  have hs := (inverseImageAdjunction g).homEquiv_naturality_right
    (representedSheafBaseChangeIso g (baseChangedGroup f A)).hom (representedSheafMap q)
  rw [hg] at hs
  have h := Adjunction.RepresentedCoherence.homEquiv_comp
    (inverseImageAdjunction f) (inverseImageAdjunction g)
    (inverseImageAdjunction (g ≫ f)) (inverseImageComp f g).hom
    (directImageCompIso f g).hom hc (representedSheaf A)
    (representedSheaf (baseChangedGroup f A)) (representedSheaf (baseChangedGroup (g ≫ f) A))
    (representedSheafBaseChangeIso f A).hom
    ((representedSheafBaseChangeIso g (baseChangedGroup f A)).hom ≫ representedSheafMap q)
  rw [hf, hs] at h
  exact h.trans ((coefficientUnit_comp f g A q hq).trans hfg.symm)

end RepresentedBaseChange

section Cohomology
universe w w'
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
attribute [local instance] hasSheafifyLarge

/-- Scheme pullback on actual Ext H¹, expressed in the actual represented
coefficient sheaf of the pulled-back group scheme. -/
def representedH1Pullback (f : S ⟶ X) (H : Grp (Over X))
    [IsCommMonObj H.X] [Etale H.X.hom] :
    H1Etale X (representedSheaf H) →+ H1Etale S (representedSheaf (baseChangedGroup f H)) :=
  (coefficientMap (representedSheafBaseChangeIso f H).hom).comp
    (h1Pullback f (representedSheaf H))

/-- Scheme pullback and every actual coefficient group map commute on Ext H¹. -/
theorem representedH1Pullback_coefficientMap (f : S ⟶ X)
    {H K : Grp (Over X)} [IsCommMonObj H.X] [IsCommMonObj K.X]
    [Etale H.X.hom] [Etale K.X.hom] (q : H ⟶ K)
    (a : H1Etale X (representedSheaf H)) :
    representedH1Pullback f K (coefficientMap (representedSheafMap q) a) =
      coefficientMap (representedSheafMap ((Over.pullback f).mapGrp.map q))
        (representedH1Pullback f H a) := by
  simp only [representedH1Pullback, AddMonoidHom.comp_apply, h1Pullback_coefficientMap]
  change ((coefficientMap (representedSheafBaseChangeIso f K).hom).comp
    (coefficientMap ((inverseImage f).map (representedSheafMap q))))
      (h1Pullback f (representedSheaf H) a) =
    ((coefficientMap (representedSheafMap ((Over.pullback f).mapGrp.map q))).comp
      (coefficientMap (representedSheafBaseChangeIso f H).hom))
        (h1Pullback f (representedSheaf H) a)
  rw [← coefficientMap_comp, ← coefficientMap_comp, representedSheafBaseChangeIso_naturality]
end Cohomology

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 94a7f1ab17f8be7514417d18ed7c260f85e34ccd54c874beaa8148787914a1e8.
Definitions, hypotheses and universes are retained modulo native names. -/
