/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.SectionsSeparation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleNaturality
public import Aglib.CategoryTheory.Functor.RepresentativeSections

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
  Functor.representativeSection_restrict (Etale.forget X) (pullbackSectionsFunctor F)
    (pullbackSectionsEtaleNatIso F) g U a s

/-- Refining a representative uses the original coefficient restriction map. -/
lemma etaleRepresentativeSection_refine {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (Y : Over X) {T U : X.Etale}
    (p : T ⟶ U) (a : Y ⟶ (Etale.forget X).obj T) (s : F.obj.obj (op U)) :
    etaleRepresentativeSection F Y U (a ≫ (Etale.forget X).map p) s =
      etaleRepresentativeSection F Y T a (F.obj.map p.op s) :=
  Functor.representativeSection_refine (Etale.forget X) (pullbackSectionsFunctor F)
    (pullbackSectionsEtaleNatIso F) p a s

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
  let g (j : J) : Over.mk ((W j).hom ≫ f) ⟶ Over.mk f := Over.homMk (W j).hom
  exact Functor.representativeSection_eq_of_witnesses (Etale.forget X)
    (pullbackSectionsFunctor F) (pullbackSectionsEtaleNatIso F) g
    (fun x y hxy => pullbackSections_eq_of_etale_cover f F W hcover x y hxy)
    U V a b s t T p q c hp hq hst

end AlgebraicGeometry.Scheme.EtaleAffineBasis
