/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.UnitSectionsAmalgamation
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.SectionsSeparation
/-! # Native functorial restriction interfaces for original sheaf gluing -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- The original sheaf amalgamation, expressed in the original section functor. -/
theorem exists_canonical_unitSections_amalgamation
    {X S : Scheme.{u}} (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → S.Etale) (U : J → X.Etale)
    (a : ∀ j, W j ⟶ (siteBaseChange f).obj (U j))
    (t : ∀ j, F.obj.obj (op (U j)))
    (hcover : Sieve.ofArrows W (fun j ↦ (etaleTerminalIsTerminal S).from (W j)) ∈
      S.smallEtaleTopology (etaleTerminal S))
    (hcompatible : Presieve.Arrows.Compatible
      (((inverseImage f).obj F).obj ⋙ CategoryTheory.forget Ab.{u + 1})
      (fun j ↦ (etaleTerminalIsTerminal S).from (W j))
      (fun j ↦ unitSectionMap f F (a j) (t j))) :
    ∃ s : (pullbackSectionsFunctor F).obj (op (Over.mk f)), ∀ j,
      (pullbackSectionsFunctor F).map
        (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f)).op s =
      etaleRepresentativeSection F (Over.mk ((W j).hom ≫ f)) (U j)
        (unitRepresentativeArrow f (a j)) (t j) := by
  obtain ⟨s, hs⟩ := exists_unitSections_amalgamation f F W U a t hcover hcompatible
  refine ⟨s, fun j ↦ ?_⟩
  exact (ConcreteCategory.congr_hom (pullbackSectionsFunctor_map F
    (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f))) s).trans
      (hs j)

/-- Canonical relative section restrictions along an original cover detect equality. -/
theorem canonicalSections_eq_of_etale_cover {X S : Scheme.{u}}
    (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → S.Etale)
    (hcover : Sieve.ofArrows W (fun j ↦ (etaleTerminalIsTerminal S).from (W j)) ∈
      S.smallEtaleTopology (etaleTerminal S))
    (s t : (pullbackSectionsFunctor F).obj (op (Over.mk f)))
    (h : ∀ j, (pullbackSectionsFunctor F).map
        (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f)).op s =
      (pullbackSectionsFunctor F).map
        (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f)).op t) :
    s = t := by
  apply pullbackSections_eq_of_etale_cover f F W hcover s t
  intro j
  let a : Over.mk ((W j).hom ≫ f) ⟶ Over.mk f := Over.homMk (W j).hom
  exact (ConcreteCategory.congr_hom (pullbackSectionsFunctor_map F a) s).symm.trans
    ((h j).trans (ConcreteCategory.congr_hom (pullbackSectionsFunctor_map F a) t))

end AlgebraicGeometry.Scheme.EtaleAffineBasis
