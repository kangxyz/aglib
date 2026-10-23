/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLift
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic
public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison

/-! # The original constant-integer source and degree-zero value lift

The map is fixed by the actual constant-one section at a terminal object. No
injectivity claim about lifted sheaves enters this normalization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.BasisAcyclicity

open ModuleCoefficients

universe e e' c h v t

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
  [HasSheafify J AddCommGrpCat.{max v t}]
  {T : C} (hT : IsTerminal T)

/-- The original constant-integer source comparison, characterized by the
lift of the original section represented by its identity. -/
def valueLiftConstantMap :
    (constantSheaf J AddCommGrpCat.{max v t}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
      (valueLift.{c, h, v, t} J).obj
        ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ))) :=
  (constantHomSectionsEquiv hT _).symm
    (ULift.up (constantHomSectionsEquiv hT _ (𝟙 _)))

/-- The actual source comparison sends the original universal section to its
value lift. -/
lemma valueLiftConstantMap_sections :
    constantHomSectionsEquiv hT _ (valueLiftConstantMap.{c, h, v, t} hT) =
      ULift.up (constantHomSectionsEquiv hT
        ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ))) (𝟙 _)) :=
  Equiv.apply_symm_apply _ _

/-- The normalized comparison on Hom is literally `ULift.up` on sections. -/
lemma valueLiftConstantMap_comp_sections (F : Sheaf J AddCommGrpCat.{v})
    (f : (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    constantHomSectionsEquiv hT _
        (valueLiftConstantMap.{c, h, v, t} hT ≫ (valueLift J).map f) =
      ULift.up (constantHomSectionsEquiv hT F f) := by
  rw [constantHomSectionsEquiv_naturality, valueLiftConstantMap_sections]
  change ULift.up (f.hom.app (op T) (constantHomSectionsEquiv hT _ (𝟙 _))) = _
  rw [← constantHomSectionsEquiv_naturality, Category.id_comp]

/-- Degree-zero source comparison is a bijection on the original Hom sets. -/
theorem valueLiftConstantMap_hom_bijective (F : Sheaf J AddCommGrpCat.{v}) :
    Function.Bijective (fun f :
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F =>
      valueLiftConstantMap.{c, h, v, t} hT ≫ (valueLift J).map f) := by
  have he : Function.Bijective (fun f :
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F =>
      ULift.up.{t} (constantHomSectionsEquiv hT F f)) :=
    ULift.up_bijective.comp (constantHomSectionsEquiv hT F).bijective
  have hh : (fun f => constantHomSectionsEquiv hT _
      (valueLiftConstantMap.{c, h, v, t} hT ≫ (valueLift J).map f)) =
      (fun f => ULift.up.{t} (constantHomSectionsEquiv hT F f)) := by
    funext f
    exact valueLiftConstantMap_comp_sections hT F f
  rw [← hh] at he
  exact (Function.Bijective.of_comp_iff' (constantHomSectionsEquiv hT _).bijective _).mp he

variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})]
  [J.HasSheafCompose (forget AddCommGrpCat.{max v t})]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{e'} (Sheaf J AddCommGrpCat.{max v t})]

/-- The original all-degree map whose eventual equivalence is proved using
acyclic lifted injectives, not injective preservation. -/
abbrev valueLiftCohomologyMap (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    Sheaf.H.{e} F n →+ Sheaf.H.{e'} ((valueLift.{c, h, v, t} J).obj F) n :=
  (valueLift.{c, h, v, t} J).extPrecompMap (valueLiftConstantMap.{c, h, v, t} hT) F n

/-- The original degree-zero Ext comparison is bijective. -/
theorem valueLiftCohomologyMap_zero_bijective (F : Sheaf J AddCommGrpCat.{v}) :
    Function.Bijective (valueLiftCohomologyMap.{e, e', c, h, v, t} hT F 0) := by
  constructor
  · intro x y hxy
    apply Ext.homEquiv₀.injective
    apply (valueLiftConstantMap_hom_bijective.{c, h, v, t} hT F).injective
    have hx := (valueLift.{c, h, v, t} J).extPrecompMap_mk₀
      (valueLiftConstantMap.{c, h, v, t} hT) (Ext.homEquiv₀ x)
    have hy := (valueLift.{c, h, v, t} J).extPrecompMap_mk₀
      (valueLiftConstantMap.{c, h, v, t} hT) (Ext.homEquiv₀ y)
    rw [Ext.mk₀_homEquiv₀_apply] at hx hy
    apply Ext.homEquiv₀.symm.injective
    exact hx.symm.trans (hxy.trans hy)
  · intro y
    obtain ⟨f, hf⟩ := (valueLiftConstantMap_hom_bijective.{c, h, v, t} hT F).surjective
      (Ext.homEquiv₀ y)
    refine ⟨Ext.mk₀ f, ?_⟩
    change (valueLift.{c, h, v, t} J).extPrecompMap
      (valueLiftConstantMap.{c, h, v, t} hT) F 0 (Ext.mk₀ f) = y
    change valueLiftConstantMap.{c, h, v, t} hT ≫ (valueLift.{c, h, v, t} J).map f =
      Ext.homEquiv₀ y at hf
    rw [Functor.extPrecompMap_mk₀, hf, Ext.mk₀_homEquiv₀_apply]

end CategoryTheory.Sheaf.BasisAcyclicity
