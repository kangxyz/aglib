/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationLaws
public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange.Evaluation

/-! The original coevaluation morphism is the same actual universal group character. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.Group.CartierDuality
open AlgebraicGeometry.Scheme.OverField (FScheme Base)

universe u

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]

example :
    (universalCharacter (k := k) G).hom.hom.left ≫ prod.snd =
      (evaluation (k := k) G).left ≫ prod.snd :=
  universalCharacter_evaluation G

example :
    (universalCharacter (k := k) G).hom.hom.left =
      prod.lift
        ((Over.pullback (dualGroup (k := k) G).X.hom).mapGrp.obj G).X.hom
        ((evaluation (k := k) G).left ≫ prod.snd) :=
  universalCharacter_evaluation_map G

example (T : AlgebraicGeometry.Scheme.{u})
    (h : T ⟶ ((Over.pullback (dualGroup (k := k) G).X.hom).mapGrp.obj G).X.left) :
    h ≫ (universalCharacter (k := k) G).hom.hom.left ≫ prod.snd =
      h ≫ (evaluation (k := k) G).left ≫ prod.snd :=
  congrArg (fun q => h ≫ q) (universalCharacter_evaluation G)

open MonoidalCategory
open scoped CategoryTheory.MonObj

local instance : GrpObj (MultiplicativeGroup.scheme (dualGroup (k := k) G).X.left) :=
  (MultiplicativeGroup.groupScheme (dualGroup (k := k) G).X.left).grp

example :
    evaluationOverDual (k := k) G = (universalCharacter (k := k) G).hom.hom :=
  evaluationOverDual_eq_universal G

example : IsMonHom (evaluationOverDual (k := k) G) :=
  evaluationOverDual_isMonHom G

example :
    η[((Over.pullback (dualGroup (k := k) G).X.hom).mapGrp.obj G).X] ≫
        evaluationOverDual (k := k) G =
      η[MultiplicativeGroup.scheme (dualGroup (k := k) G).X.left] :=
  evaluationOverDual_one G

example :
    μ[((Over.pullback (dualGroup (k := k) G).X.hom).mapGrp.obj G).X] ≫
        evaluationOverDual (k := k) G =
      (evaluationOverDual (k := k) G ⊗ₘ evaluationOverDual (k := k) G) ≫
        μ[MultiplicativeGroup.scheme (dualGroup (k := k) G).X.left] :=
  evaluationOverDual_mul G

variable {G} {H : Grp (FScheme k)} [IsFinite H.X.hom] [IsCommMonObj H.X]

example (f : G ⟶ H) :
    (f.hom.hom ⊗ₘ 𝟙 (dualGroup H).X) ≫ evaluation H =
      (𝟙 G.X ⊗ₘ (dualMap f).hom.hom) ≫ evaluation G :=
  evaluation_naturality f

example (f : G ⟶ H) (T : FScheme k) (p : T ⟶ G.X ⊗ (dualGroup H).X) :
    p ≫ (f.hom.hom ⊗ₘ 𝟙 (dualGroup H).X) ≫ evaluation H =
      p ≫ (𝟙 G.X ⊗ₘ (dualMap f).hom.hom) ≫ evaluation G :=
  congrArg (fun q => p ≫ q) (evaluation_naturality f)

variable (G)

example (T : FScheme k) (p : T ⟶ (dualGroup G).X) :
    (characterOfPoint G T p).hom.hom.left =
      prod.lift ((Over.pullback T.hom).mapGrp.obj G).X.hom
        (groupPullbackBaseMap G p ≫ (evaluation G).left ≫ prod.snd) :=
  characterOfPoint_evaluation_map G T p

example (T : FScheme k) (U : Over T.left) :
    (U ⟶ ((Over.pullback T.hom).mapGrp.obj (dualGroup G)).X) ≃
      ((Over.pullback U.hom).mapGrp.obj ((Over.pullback T.hom).mapGrp.obj G) ⟶
        MultiplicativeGroup.groupScheme U.left) :=
  characterEquivBaseChange G T U

example (T : FScheme k) {U V : Over T.left} (h : V ⟶ U)
    (p : U ⟶ ((Over.pullback T.hom).mapGrp.obj (dualGroup G)).X) :
    ((BaseChange.groupSchemeBaseChangeComp V.hom T.hom).hom.app G) ≫
        characterEquivBaseChange G T V (h ≫ p) =
      restrictCharacter G ((Over.map T.hom).map h)
        (((BaseChange.groupSchemeBaseChangeComp U.hom T.hom).hom.app G) ≫
          characterEquivBaseChange G T U p) :=
  characterEquivBaseChange_naturality G T h p

local instance : GrpObj (MultiplicativeGroup.scheme G.X.left) :=
  (MultiplicativeGroup.groupScheme G.X.left).grp

example : IsMonHom (evaluationOverPrimal G) :=
  evaluationOverPrimal_isMonHom G

example :
    η[((Over.pullback G.X.hom).mapGrp.obj (dualGroup G)).X] ≫ evaluationOverPrimal G =
      η[MultiplicativeGroup.scheme G.X.left] :=
  evaluationOverPrimal_one G

example :
    μ[((Over.pullback G.X.hom).mapGrp.obj (dualGroup G)).X] ≫ evaluationOverPrimal G =
      (evaluationOverPrimal G ⊗ₘ evaluationOverPrimal G) ≫
        μ[MultiplicativeGroup.scheme G.X.left] :=
  evaluationOverPrimal_mul G

example :
    (β_ G.X (dualGroup G).X).hom ≫
        (𝟙 (dualGroup G).X ⊗ₘ (bidualIso G).hom.hom.hom) ≫
        evaluation (dualGroup G) = evaluation G :=
  evaluation_bidual G

example (T : FScheme k) (p : T ⟶ G.X ⊗ (dualGroup G).X) :
    p ≫ (β_ G.X (dualGroup G).X).hom ≫
        (𝟙 (dualGroup G).X ⊗ₘ (bidualIso G).hom.hom.hom) ≫
        evaluation (dualGroup G) = p ≫ evaluation G :=
  congrArg (fun q => p ≫ q) (evaluation_bidual G)


section FieldBaseChange

attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type u) [Field K] [Algebra k K]

example :
    (Over.pullback (Spec.algebraMap k K)).mapGrp.obj (dualGroup G) ≅
      dualGroup (k := K) ((Over.pullback (Spec.algebraMap k K)).mapGrp.obj G) :=
  dualGroupBaseChangeIso K G (Spec.algebraMap k K)

example :
    let i : Base K ⟶ Base k := Spec.algebraMap k K
    let H := (Over.pullback i).mapGrp.obj G
    let a := (dualGroupBaseChangeIso K G i).hom.hom.hom
    let b := CartierDuality.evaluation (k := K) H
    (𝟙 H.X ⊗ₘ a) ≫ b =
      Functor.LaxMonoidal.μ (Over.pullback i) G.X (dualGroup G).X ≫
        (Over.pullback i).map (CartierDuality.evaluation G) ≫
        (MultiplicativeBaseChange.unitsBaseChangeIso i).hom.hom.hom :=
  dualGroupBaseChangeIso_evaluation K G (Spec.algebraMap k K)

example (T : FScheme K)
    (p : T ⟶ ((Over.pullback (Spec.algebraMap k K)).mapGrp.obj G).X ⊗
      ((Over.pullback (Spec.algebraMap k K)).mapGrp.obj (dualGroup G)).X) :
    let i : Base K ⟶ Base k := Spec.algebraMap k K
    let H := (Over.pullback i).mapGrp.obj G
    let a := (dualGroupBaseChangeIso K G i).hom.hom.hom
    let b := CartierDuality.evaluation (k := K) H
    p ≫ ((𝟙 H.X ⊗ₘ a) ≫ b) =
      p ≫ (Functor.LaxMonoidal.μ (Over.pullback i) G.X (dualGroup G).X ≫
        (Over.pullback i).map (CartierDuality.evaluation G) ≫
        (MultiplicativeBaseChange.unitsBaseChangeIso i).hom.hom.hom) :=
  congrArg (fun q => p ≫ q) (dualGroupBaseChangeIso_evaluation K G (Spec.algebraMap k K))

end FieldBaseChange
