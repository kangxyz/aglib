/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRestriction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.FiniteGeneratorsLifting
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Finite constant sources for epimorphisms onto constant modules

Finite quotient generators are lifted locally into a finite submodule of the
actual middle-sheaf sections. The resulting constant source has epic composite
to the quotient on the actual slice. This neither splits the extension nor
requires a free module in a larger universe.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf

universe u v r

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type r} [Ring R]

attribute [local instance] hasSheafify

/-- The native restriction transformation associated to a linear section map. -/
def sectionToSlicePresheaf (U : C) (F : Sheaf J (ModuleCat.{max u v} R))
    (M : ModuleCat.{max u v} R) (a : M ⟶ F.obj.obj (op U)) :
    (Functor.const (Over U)ᵒᵖ).obj M ⟶
      ((J.overPullback (ModuleCat.{max u v} R) U).obj F).obj where
  app V := a ≫ F.obj.map V.unop.hom.op
  naturality V W f := by
    change a ≫ F.obj.map W.unop.hom.op =
      (a ≫ F.obj.map V.unop.hom.op) ≫ F.obj.map f.unop.left.op
    rw [Category.assoc, ← F.obj.map_comp, ← op_comp, Over.w f.unop]

/-- A linear map to actual sections induces a morphism from constant modules
to the actual slice restriction. -/
def sectionToSlice (U : C) (F : Sheaf J (ModuleCat.{max u v} R))
    (M : ModuleCat.{max u v} R) (a : M ⟶ F.obj.obj (op U)) :
    (constantSheaf (J.over U) (ModuleCat.{max u v} R)).obj M ⟶
      (J.overPullback (ModuleCat.{max u v} R) U).obj F :=
  ((sheafificationAdjunction (J.over U) (ModuleCat.{max u v} R)).homEquiv _ _).symm
    (sectionToSlicePresheaf J U F M a)

/-- The map from sections retains the original sheafification-unit equation. -/
theorem sectionToSlice_unit (U : C) (F : Sheaf J (ModuleCat.{max u v} R))
    (M : ModuleCat.{max u v} R) (a : M ⟶ F.obj.obj (op U)) (V : Over U) :
    (constantUnit (J.over U) M).app (op V) ≫
        (sectionToSlice J U F M a).hom.app (op V) = a ≫ F.obj.map V.hom.op := by
  exact congrArg
    (fun η : (Functor.const (Over U)ᵒᵖ).obj M ⟶
      ((J.overPullback (ModuleCat.{max u v} R) U).obj F).obj => η.app (op V))
    (toSheafify_sheafifyLift (J.over U) (sectionToSlicePresheaf J U F M a) _)

set_option backward.isDefEq.respectTransparency false in
/-- Lifting all constant values at the slice base makes the actual slice map
locally surjective, although neither original quotient map is sectionwise epic. -/
theorem sectionToSlice_comp_locallySurjective
    {N : ModuleCat.{max u v} R} (F : Sheaf J (ModuleCat.{max u v} R))
    (p : F ⟶ (constantSheaf J (ModuleCat.{max u v} R)).obj N)
    (U : C) (M : ModuleCat.{max u v} R) (a : M ⟶ F.obj.obj (op U))
    (ha : ∀ n : N, ∃ m : M, p.hom.app (op U) (a m) = (constantUnit J N).app (op U) n) :
    CategoryTheory.Sheaf.IsLocallySurjective
      (sectionToSlice J U F M a ≫ (J.overPullback (ModuleCat.{max u v} R) U).map p) := by
  let : PreservesFilteredColimits (forget (ModuleCat.{max u v} R)) :=
    forget_preservesFilteredColimits R
  let : J.PreservesSheafification (forget (ModuleCat.{max u v} R)) :=
    GrothendieckTopology.instPreservesSheafification J (forget (ModuleCat.{max u v} R))
  let : CategoryTheory.Presheaf.IsLocallySurjective J (constantUnit J N) :=
    CategoryTheory.Presheaf.isLocallySurjective_toSheafify' J
      (D := ModuleCat.{max u v} R) ((Functor.const Cᵒᵖ).obj N)
  let η := Functor.whiskerLeft (Over.forget U).op (constantUnit J N)
  let : CategoryTheory.Presheaf.IsLocallySurjective (J.over U) η :=
    CategoryTheory.Presheaf.isLocallySurjective_whisker
      (J.over U) J (Over.forget U) (constantUnit J N)
  constructor
  intro V z
  refine (J.over U).superset_covering ?_
    (CategoryTheory.Presheaf.imageSieve_mem (J.over U) η z)
  intro W f hf
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := ha n
  refine ⟨(constantUnit (J.over U) M).app (op W) m, ?_⟩
  have hunit : (sectionToSlice J U F M a).hom.app (op W)
        ((constantUnit (J.over U) M).app (op W) m) = F.obj.map W.hom.op (a m) :=
    congrArg (fun b : M ⟶ F.obj.obj (op W.left) => b m)
      (sectionToSlice_unit J U F M a W)
  have hp := NatTrans.naturality_apply p.hom W.hom.op (a m)
  have hN := NatTrans.naturality_apply (constantUnit J N) W.hom.op n
  change p.hom.app (op W.left)
      ((sectionToSlice J U F M a).hom.app (op W)
        ((constantUnit (J.over U) M).app (op W) m)) = _
  rw [hunit, hp, hm]
  exact hN.symm.trans hn


/-- An epimorphism onto a finite constant module admits, on a covering sieve,
a finite constant source mapping epimorphically to that quotient. -/
theorem exists_cover_constant_generators
    {N : ModuleCat.{max u v} R} [Module.Finite R N]
    (F : Sheaf J (ModuleCat.{max u v} R))
    (p : F ⟶ (constantSheaf J (ModuleCat.{max u v} R)).obj N) [Epi p] (U : C) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
      ∃ M : ModuleCat.{max u v} R, Module.Finite R M ∧
        ∃ a : (constantSheaf (J.over V) (ModuleCat.{max u v} R)).obj M ⟶
          (J.overPullback (ModuleCat.{max u v} R) V).obj F,
          Epi (a ≫ (J.overPullback (ModuleCat.{max u v} R) V).map p) := by
  let : HasLimitsOfSize.{max u v, max u v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{max u v, max u v, max u v, r}
  let : PreservesFilteredColimits (forget (ModuleCat.{max u v} R)) :=
    forget_preservesFilteredColimits R
  let : J.PreservesSheafification (forget (ModuleCat.{max u v} R)) :=
    GrothendieckTopology.instPreservesSheafification J (forget (ModuleCat.{max u v} R))
  let : CategoryTheory.Sheaf.IsLocallySurjective p :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{max u v} R) p).mpr
      inferInstance
  obtain ⟨T, hT, h⟩ := ModuleCat.Presheaf.exists_cover_finite_span_lifts J p.hom N
    ((constantUnit J N).app (op U))
  refine ⟨T, hT, ?_⟩
  intro V f hf
  obtain ⟨P, hP, hP'⟩ := h f hf
  let M : ModuleCat.{max u v} R := ModuleCat.of R P
  let a : M ⟶ F.obj.obj (op V) := ModuleCat.ofHom P.subtype
  have ha : ∀ n : N, ∃ m : M, p.hom.app (op V) (a m) =
      (constantUnit J N).app (op V) n := by
    intro n
    obtain ⟨m, hm⟩ := hP' n
    refine ⟨m, hm.trans ?_⟩
    have hn := NatTrans.naturality_apply (constantUnit J N) f.op n
    exact hn.symm
  refine ⟨M, Module.Finite.of_fg hP, sectionToSlice J V F M a, ?_⟩
  let := sectionToSlice_comp_locallySurjective J F p V M a ha
  infer_instance

end ModuleCat.Sheaf
