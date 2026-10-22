/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Quotient
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Original quotient factorizations of diagrams

Pointwise factorizations through the original epi quotient units are
automatically natural. In particular this applies to maps into ordinary
annihilated kernels, without declaring the kernel diagram to be adic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u v w
variable (X : Scheme.{u}) (K : X.IdealSheafData)
  {J : Type v} [Category.{w} J] {F G H : J ⥤ X.Modules}

/-- Original epi units force the naturality of pointwise quotient descents. -/
def diagramQuotientDesc (η : F ⟶ G)
    (δ : ∀ j, (idealSheafQuotientFunctor X K).obj (F.obj j) ⟶ G.obj j)
    (hδ : ∀ j, (idealSheafQuotientUnit X K).app (F.obj j) ≫ δ j = η.app j) :
    F ⋙ idealSheafQuotientFunctor X K ⟶ G where
  app := δ
  naturality {j k} a := by
    apply (cancel_epi ((idealSheafQuotientUnit X K).app (F.obj j))).mp
    change (idealSheafQuotientUnit X K).app (F.obj j) ≫
      (idealSheafQuotientFunctor X K).map (F.map a) ≫ δ k =
      (idealSheafQuotientUnit X K).app (F.obj j) ≫ δ j ≫ G.map a
    rw [← (idealSheafQuotientUnit X K).naturality_assoc]
    dsimp only [Functor.id_map]
    rw [hδ k, ← Category.assoc, hδ j]
    exact η.naturality a

/-- The descended component retains the supplied factorization verbatim. -/
@[reassoc]
theorem diagramQuotientDesc_unit (η : F ⟶ G)
    (δ : ∀ j, (idealSheafQuotientFunctor X K).obj (F.obj j) ⟶ G.obj j)
    (hδ : ∀ j, (idealSheafQuotientUnit X K).app (F.obj j) ≫ δ j = η.app j)
    (j : J) :
    (idealSheafQuotientUnit X K).app (F.obj j) ≫
      (diagramQuotientDesc X K η δ hδ).app j = η.app j := hδ j

/-- A map into ordinary annihilated kernels factors through the source quotient. -/
def diagramQuotientDescOfKernel (η : F ⟶ G) (α : G ⟶ H)
    (hzero : ∀ j, η.app j ≫ α.app j = 0)
    (hk : ∀ j, killedByIdealSheaf K (kernel (α.app j))) :
    F ⋙ idealSheafQuotientFunctor X K ⟶ G :=
  diagramQuotientDesc X K η
    (fun j => idealSheafQuotientDesc X K
      (kernel.lift (α.app j) (η.app j) (hzero j)) (hk j) ≫ kernel.ι (α.app j))
    (fun j => by
      have hu := idealSheafQuotientUnit_desc X K
        (kernel.lift (α.app j) (η.app j) (hzero j)) (hk j)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z : F.obj j ⟶ kernel (α.app j) => z ≫ kernel.ι (α.app j))
          hu).trans (kernel.lift_ι (α.app j) (η.app j) (hzero j))))

/-- The kernel-based descent is characterized by the same original units. -/
@[reassoc]
theorem diagramQuotientDescOfKernel_unit (η : F ⟶ G) (α : G ⟶ H)
    (hzero : ∀ j, η.app j ≫ α.app j = 0)
    (hk : ∀ j, killedByIdealSheaf K (kernel (α.app j))) (j : J) :
    (idealSheafQuotientUnit X K).app (F.obj j) ≫
      (diagramQuotientDescOfKernel X K η α hzero hk).app j = η.app j := by
  exact diagramQuotientDesc_unit X K η _ _ j

end AlgebraicGeometry.Scheme.Modules.Coherent
