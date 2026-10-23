/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedScalarSections
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.DerivedNaturalityPacket

/-!
# Native coefficient maps under the derived sections comparison

Both coefficient morphisms are the original maps: native right-derived module
sections on the source and Yoneda composition with `Ext.mk₀` on the target.
-/

@[expose] public noncomputable section

universe u v r w e s

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {T : C} (hT : IsTerminal T) (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [EnoughInjectives (SheafOfModules.{max u v r w} R)]
  [HasExt.{e} (SheafOfModules.{max u v r w} R)]
  {M N : SheafOfModules.{max u v r w} R}

/-- The original derived evaluation coefficient map agrees with native Ext postcomposition. -/
lemma derivedTerminalSectionsExtAddEquiv_naturality (f : M ⟶ N) (n : ℕ)
    (x : ((SheafOfModules.evaluation.{max u v r w} R (op T)).rightDerived n).obj M) :
    derivedTerminalSectionsExtAddEquiv.{u, v, r, w, e} hT R N n
        (((SheafOfModules.evaluation.{max u v r w} R (op T)).rightDerived n).map f x) =
      (derivedTerminalSectionsExtAddEquiv.{u, v, r, w, e} hT R M n x).comp
        (Ext.mk₀ f) (add_zero _) := by
  unfold derivedTerminalSectionsExtAddEquiv
  exact representedIso_ext_naturality
    (SheafOfModules.liftedUnit.{u, v, max u v w, r} R)
    ((SheafOfModules.evaluation.{max u v r w} R (op T)).rightDerived n) n
    (derivedTerminalSectionsIso.{u, v, r, w} hT R n) f x

variable (Λ : Type s) [Ring Λ] (α : Λ →+* R.obj.obj (op T))

/-- The original coefficient-valued derived sections map agrees with native Ext postcomposition. -/
lemma derivedScalarTerminalSectionsExtAddEquiv_naturality (f : M ⟶ N) (n : ℕ)
    (x : ((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n).obj M) :
    derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, e, s} hT R Λ α N n
        (((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n).map f x) =
      (derivedScalarTerminalSectionsExtAddEquiv.{u, v, r, w, e, s} hT R Λ α M n x).comp (Ext.mk₀ f)
        (add_zero _) := by
  unfold derivedScalarTerminalSectionsExtAddEquiv
  exact scalarIso_ext_naturality (SheafOfModules.liftedUnit.{u, v, max u v w, r} R)
    ((SheafOfModules.evaluation.{max u v r w} R (op T)).rightDerived n)
    ((scalarTerminalSections.{u, v, r, w, s} R Λ α).rightDerived n) α
    (derivedScalarTerminalSectionsIso.{u, v, r, w, s} R Λ α n) n
    (fun M => derivedTerminalSectionsExtAddEquiv.{u, v, r, w, e} hT R M n)
    (fun f x => derivedTerminalSectionsExtAddEquiv_naturality.{u, v, r, w, e} hT R f n x) f x

end CategoryTheory.Sheaf.ModuleCoefficients
