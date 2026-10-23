/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.ExactSequences
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Exact products in the native Čech complex -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe w v u v' u'

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)

instance cechAdditive : (cechComplexFunctor (A := A) U).Additive where
  map_add := by
    intro P Q f g
    ext n : 1
    apply Pi.hom_ext
    intro a
    simp [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
      FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
      AlgebraicTopology.AlternatingCofaceMapComplex.map, Preadditive.add_comp]

/-- Sectionwise short exactness is retained by native Čech cochains when the
coefficient category has exact products. -/
theorem cech_shortExact_of_exact_products
    [∀ (n : ℕ), HasExactLimitsOfShape (Discrete (Fin (n + 1) → ι)) A]
    (S : ShortComplex (Cᵒᵖ ⥤ A)) (hS : S.ShortExact) :
    (S.map (cechComplexFunctor U)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let D : Discrete (Fin (n + 1) → ι) ⥤ Cᵒᵖ :=
    Discrete.functor (fun a => op (∏ᶜ fun i => U (a i)))
  let e (P : Cᵒᵖ ⥤ A) : limit (D ⋙ P) ≅
      ∏ᶜ (fun a : Fin (n + 1) → ι => P.obj (op (∏ᶜ fun i => U (a i)))) :=
    HasLimit.isoOfNatIso (Discrete.natIso (fun _ => Iso.refl _))
  apply ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃) ?_ ?_)
    (hS.map_of_exact (((Functor.whiskeringLeft _ _ A).obj D) ⋙ lim))
  all_goals
    apply Pi.hom_ext
    intro a
    simp [e, D, cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
      FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp,
      AlgebraicTopology.AlternatingCofaceMapComplex.map, Pi.π, Function.comp_def,
      HasLimit.isoOfNatIso_hom_π, HasLimit.isoOfNatIso_hom_π_assoc]

end CategoryTheory.Sheaf.ModuleCoefficients
