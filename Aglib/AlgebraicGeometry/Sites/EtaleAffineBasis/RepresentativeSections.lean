/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.SectionsSeparation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleNaturality

/-! # Original relative sections represented on etale coefficient objects -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- An original coefficient section transported to a relative scheme. -/
def etaleRepresentativeSection {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (Y : Over X) (U : X.Etale)
    (a : Y ⟶ (Etale.forget X).obj U) (s : F.obj.obj (op U)) :
    (pullbackSectionsFunctor F).obj (op Y) :=
  (pullbackSectionsFunctor F).map a.op
    ((pullbackSectionsEtaleEvaluationIso F U).inv s)

/-- Restriction retains the literal composite of the original relative maps. -/
lemma etaleRepresentativeSection_restrict {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y Z : Over X} (g : Z ⟶ Y)
    (U : X.Etale) (a : Y ⟶ (Etale.forget X).obj U) (s : F.obj.obj (op U)) :
    (pullbackSectionsFunctor F).map g.op (etaleRepresentativeSection F Y U a s) =
      etaleRepresentativeSection F Z U (g ≫ a) s :=
  (ConcreteCategory.congr_hom ((pullbackSectionsFunctor F).map_comp a.op g.op)
    ((pullbackSectionsEtaleEvaluationIso F U).inv s)).symm

/-- Refining a representative uses the original coefficient restriction map. -/
lemma etaleRepresentativeSection_refine {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (Y : Over X) {T U : X.Etale}
    (p : T ⟶ U) (a : Y ⟶ (Etale.forget X).obj T) (s : F.obj.obj (op U)) :
    etaleRepresentativeSection F Y U (a ≫ (Etale.forget X).map p) s =
      etaleRepresentativeSection F Y T a (F.obj.map p.op s) := by
  have h : (pullbackSectionsFunctor F).map ((Etale.forget X).map p).op
      ((pullbackSectionsEtaleEvaluationIso F U).inv s) =
      (pullbackSectionsEtaleEvaluationIso F T).inv (F.obj.map p.op s) := by
    apply (ConcreteCategory.bijective_of_isIso
      (pullbackSectionsEtaleEvaluationIso F T).hom).injective
    have hn := ConcreteCategory.congr_hom (pullbackSectionsMap_etaleEvaluation F p)
      ((pullbackSectionsEtaleEvaluationIso F U).inv s)
    have hU := ConcreteCategory.congr_hom
      (pullbackSectionsEtaleEvaluationIso F U).inv_hom_id s
    have hT := ConcreteCategory.congr_hom
      (pullbackSectionsEtaleEvaluationIso F T).inv_hom_id (F.obj.map p.op s)
    exact hn.trans ((congrArg (F.obj.map p.op) hU).trans hT.symm)
  exact (ConcreteCategory.congr_hom
    ((pullbackSectionsFunctor F).map_comp ((Etale.forget X).map p).op a.op)
    ((pullbackSectionsEtaleEvaluationIso F U).inv s)).trans
    (congrArg ((pullbackSectionsFunctor F).map a.op) h)

/-- Common original coefficient witnesses on an actual cover prove equality
of the original relative sections. -/
theorem etaleRepresentativeSection_eq_of_covering_witnesses
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → Y.Etale)
    (hcover : Sieve.ofArrows W (fun j ↦ (etaleTerminalIsTerminal Y).from (W j)) ∈
      Y.smallEtaleTopology (etaleTerminal Y))
    (U V : X.Etale) (a : Over.mk f ⟶ (Etale.forget X).obj U)
    (b : Over.mk f ⟶ (Etale.forget X).obj V)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (T : J → X.Etale) (p : ∀ j, T j ⟶ U) (q : ∀ j, T j ⟶ V)
    (c : ∀ j, Over.mk ((W j).hom ≫ f) ⟶ (Etale.forget X).obj (T j))
    (hp : ∀ j, c j ≫ (Etale.forget X).map (p j) = Over.homMk (W j).hom ≫ a)
    (hq : ∀ j, c j ≫ (Etale.forget X).map (q j) = Over.homMk (W j).hom ≫ b)
    (hst : ∀ j, F.obj.map (p j).op s = F.obj.map (q j).op t) :
    etaleRepresentativeSection F (Over.mk f) U a s =
      etaleRepresentativeSection F (Over.mk f) V b t := by
  apply pullbackSections_eq_of_etale_cover f F W hcover
  intro j
  let g : Over.mk ((W j).hom ≫ f) ⟶ Over.mk f := Over.homMk (W j).hom
  exact (etaleRepresentativeSection_restrict F g U a s).trans
    ((congrArg (fun z ↦ etaleRepresentativeSection F _ U z s) (hp j).symm).trans
      ((etaleRepresentativeSection_refine F _ (p j) (c j) s).trans
        ((congrArg (etaleRepresentativeSection F _ (T j) (c j)) (hst j)).trans
          ((etaleRepresentativeSection_refine F _ (q j) (c j) t).symm.trans
            ((congrArg (fun z ↦ etaleRepresentativeSection F _ V z t) (hq j)).trans
              (etaleRepresentativeSection_restrict F g V b t).symm)))))

end AlgebraicGeometry.Scheme.EtaleAffineBasis
