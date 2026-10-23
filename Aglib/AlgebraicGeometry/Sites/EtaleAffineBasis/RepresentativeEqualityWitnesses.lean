/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeSections
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.InverseImageSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitTransport

/-! # Finite affine witnesses extracted from equality of actual relative sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private lemma terminal_witness_triangle {X S : Scheme.{u}} (f : S ⟶ X)
    {Z : S.Etale} {T U : X.Etale} (a : S ⟶ U.left) (ha : a ≫ U.hom = f)
    (g : Z ⟶ etaleTerminal S) (c : Z ⟶ (siteBaseChange f).obj T) (p : T ⟶ U)
    (h : c ≫ (siteBaseChange f).map p = g ≫ relativeTerminalTest f U a ha) :
    (c.left ≫ pullback.fst T.hom f) ≫ p.left = Z.hom ≫ a := by
  have hm : ((siteBaseChange f).map p).left ≫ pullback.fst U.hom f =
      pullback.fst T.hom f ≫ p.left := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _
  have ht : (relativeTerminalTest f U a ha).left ≫ pullback.fst U.hom f = a :=
    pullback.lift_fst _ _ _
  have hg : g.left = Z.hom := (Category.comp_id _).symm.trans (MorphismProperty.Over.w g)
  have he := congrArg (fun z : Z ⟶ (siteBaseChange f).obj U ↦
    z.left ≫ pullback.fst U.hom f) h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ c.left ≫ z) hm.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (he.trans ((Category.assoc _ _ _).trans
          ((congrArg (fun z ↦ g.left ≫ z) ht).trans
            (congrArg (fun z ↦ z ≫ a) hg))))))

/-- Equality of represented original sections supplies an actual finite affine
cover and common original coefficient witnesses, including both triangles. -/
theorem exists_finite_affine_representative_equality_witnesses
    {X S : Scheme.{u}} (f : S ⟶ X) [CompactSpace S]
    (F : AbelianSheaf.{u, u + 1} X) (U V : X.Etale)
    (a : S ⟶ U.left) (b : S ⟶ V.left)
    (ha : a ≫ U.hom = f) (hb : b ≫ V.hom = f)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (h : etaleRepresentativeSection F (Over.mk f) U (Over.homMk a ha) s =
      etaleRepresentativeSection F (Over.mk f) V (Over.homMk b hb) t) :
    ∃ (J : Type u) (_ : Finite J) (Y : J → Over S),
      (∀ j, IsAffine (Y j).left) ∧ (∀ j, Etale (Y j).hom) ∧
      (∀ x : S, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x) ∧
      ∃ (T : J → X.Etale) (p : ∀ j, T j ⟶ U) (q : ∀ j, T j ⟶ V)
        (w : ∀ j, (Y j).left ⟶ (T j).left),
        (∀ j, w j ≫ (T j).hom = (Y j).hom ≫ f) ∧
        (∀ j, w j ≫ (p j).left = (Y j).hom ≫ a) ∧
        (∀ j, w j ≫ (q j).left = (Y j).hom ≫ b) ∧
        ∀ j, F.obj.map (p j).op s = F.obj.map (q j).op t := by
  have hU := ConcreteCategory.congr_hom
    (pullbackSectionsMap_relativeTerminalTest F f U a ha) s
  have hV := ConcreteCategory.congr_hom
    (pullbackSectionsMap_relativeTerminalTest F f V b hb) t
  have hunit : unitSectionMap f F (relativeTerminalTest f U a ha) s =
      unitSectionMap f F (relativeTerminalTest f V b hb) t := hU.symm.trans (h.trans hV)
  have : CompactSpace (etaleTerminal S).left := inferInstanceAs (CompactSpace S)
  obtain ⟨J, hJ, Z, g, hZ, hcov, heq⟩ :=
    exists_finite_affine_inverseImage_unit_equality f F (etaleTerminal S) U V
      (relativeTerminalTest f U a ha) (relativeTerminalTest f V b hb) s t hunit
  choose T c p q hp hq hst using heq
  refine ⟨J, hJ, fun j ↦ Over.mk (Z j).hom, hZ, fun j ↦ (Z j).prop, ?_,
    T, p, q, fun j ↦ (unitRepresentativeArrow f (c j)).left, ?_, ?_, ?_, hst⟩
  · intro x
    have htop := (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mp hcov
    have hx : x ∈ ⋃ j, Set.range (g j).left := htop.symm ▸ Set.mem_univ x
    obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hx
    refine ⟨j, y, ?_⟩
    have hg : (g j).left = (Z j).hom :=
      (Category.comp_id _).symm.trans (MorphismProperty.Over.w (g j))
    exact (congrArg (fun z ↦ z y) hg).symm.trans hy
  · intro j
    exact Over.w (unitRepresentativeArrow f (c j))
  · intro j
    exact terminal_witness_triangle f a ha (g j) (c j) (p j) (hp j)
  · intro j
    exact terminal_witness_triangle f b hb (g j) (c j) (q j) (hq j)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
