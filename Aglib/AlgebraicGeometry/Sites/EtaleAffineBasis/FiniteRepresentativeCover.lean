/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteSectionRepresentatives
/-! # Finite original representative covers with explicit geometric covering data -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- An actual original section has finite affine representative charts covering every point. -/
theorem exists_finite_representative_cover {S X : Scheme.{u}} [CompactSpace S]
    (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk f))) :
    ∃ (J : Type u) (_ : Finite J) (Y : J → Over S),
      (∀ j, IsAffine (Y j).left) ∧ (∀ j, Etale (Y j).hom) ∧
      (∀ x : S, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x) ∧
      ∃ (U : J → X.Etale)
        (a : ∀ j, Over.mk ((Y j).hom ≫ f) ⟶ (Etale.forget X).obj (U j))
        (t : ∀ j, F.obj.obj (op (U j))),
      ∀ j, pullbackSectionsMap F
        (Over.homMk (Y j).hom (U := Over.mk ((Y j).hom ≫ f)) (V := Over.mk f)) s =
      etaleRepresentativeSection F (Over.mk ((Y j).hom ≫ f)) (U j) (a j) (t j) := by
  classical
  obtain ⟨J, hJ, Y, hY, hcov, hrep⟩ :=
    exists_finite_affine_section_representatives (S := S) f F s
  choose U a t ht using hrep
  have hcover : ∀ x : S, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x := by
    have hsurj := (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mp hcov
    intro x
    have hx : x ∈ Set.iUnion (fun j ↦ Set.range
        (((etaleTerminalIsTerminal S).from (Y j)).left)) := by
      rw [hsurj]
      trivial
    obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hx
    refine ⟨j, y, ?_⟩
    have hw := MorphismProperty.Over.w ((etaleTerminalIsTerminal S).from (Y j))
    have he : ((etaleTerminalIsTerminal S).from (Y j)).left = (Y j).hom :=
      (Category.comp_id _).symm.trans hw
    exact (congrArg (fun z ↦ z y) he).symm.trans hy
  exact ⟨J, hJ, (fun j ↦ (Etale.forget S).obj (Y j)), hY,
    (fun j ↦ (Y j).prop), hcover, U, a, t, ht⟩

end AlgebraicGeometry.Scheme.EtaleAffineBasis
