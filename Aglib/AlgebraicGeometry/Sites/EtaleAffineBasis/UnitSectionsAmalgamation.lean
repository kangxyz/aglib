/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteSectionRepresentatives
public import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Gluing original unit representatives in the original inverse-image sheaf -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- Compatible unit representatives glue in the original inverse-image sheaf.
The resulting original global section has the literal relative restriction
formula on each chart. No fixed-base comparison of section functors is used. -/
theorem exists_unitSections_amalgamation
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
    ∃ s : (globalSections S).obj ((inverseImage f).obj F), ∀ j,
      pullbackSectionsMap F
        (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ f)) (V := Over.mk f)) s =
      etaleRepresentativeSection F (Over.mk ((W j).hom ≫ f)) (U j)
        (unitRepresentativeArrow f (a j)) (t j) := by
  let H := (inverseImage f).obj F
  have htype : Presieve.IsSheaf S.smallEtaleTopology (H.obj ⋙ CategoryTheory.forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget Ab.{u + 1})).obj H).property
  obtain ⟨s, hs, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp
    (htype.isSheafFor (Presieve.ofArrows W
      (fun j ↦ (etaleTerminalIsTerminal S).from (W j))) hcover)
      (fun j ↦ unitSectionMap f F (a j) (t j)) hcompatible
  refine ⟨s, fun j ↦ ?_⟩
  exact pullbackSectionsMap_eq_representative_of_unit_eq f F (W j) (U j) (a j)
    ((etaleTerminalIsTerminal S).from (W j)) s (t j) (hs j).symm

end AlgebraicGeometry.Scheme.EtaleAffineBasis
