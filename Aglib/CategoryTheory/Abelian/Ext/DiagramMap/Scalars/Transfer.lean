/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Preadditive.ScalarDiagram.Transfer
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Coefficients

/-! # Scalar linearity and the original mate of exact Ext transfer

The actual coefficient square supplies scalar compatibility for the existing
exact Ext diagram map. Its scalar mate and unit use that same transfer. The
specified Ext value universe also accommodates the coefficient rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped ChangeOfRings TensorProduct

universe u v u' v' i j k l r w

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{max r w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{max r w} D]
  {I : Type i} [Category.{j} I] {J : Type k} [Category.{l} J]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (F : I ⥤ C) (G : J ⥤ D) (P : I ⥤ J) (e : F ⋙ L ≅ P ⋙ G)
  {R S : Type r} [CommRing R] [CommRing S] (σ : R →+* S)
  (A : C) (B : D) (ρ : R →+* End A) (τ : S →+* End B)
  (φ : L.obj A ⟶ B)
  (hφ : ∀ a : R, L.map (ρ a) ≫ φ = φ ≫ τ (σ a)) (n : ℕ)

/-- The unchanged exact transfer between the original coefficient module diagrams. -/
def extScalarDiagramMap :
    F.extModuleDiagram A ρ n ⟶
      (P.op ⋙ G.extModuleDiagram B τ n) ⋙ ModuleCat.restrictScalars σ :=
  ((F.op ⋙ extFunctor.{max r w} n).flip).coefficientModuleDiagramMap
    ((G.op ⋙ extFunctor.{max r w} n).flip) σ A B ρ τ P.op
    (L.extDiagramMap F (P ⋙ G) e φ n)
    (fun a => L.extDiagramMap_coefficients F G P e φ φ (ρ a) (τ (σ a)) (hφ a) n)

/-- The same original exact transfer is retained at every index. -/
theorem extScalarDiagramMap_apply (U : Iᵒᵖ) (x : Ext.{max r w} (F.obj U.unop) A n) :
    (L.extScalarDiagramMap F G P e σ A B ρ τ φ hφ n).app U x =
      L.extCoefficientTransfer (e.inv.app U.unop) φ n x := rfl

/-- The original scalar-adjunction mate of the coefficient-linear Ext transfer. -/
def extScalarTensorDiagramMap :
    F.extModuleDiagram A ρ n ⋙ ModuleCat.extendScalars σ ⟶
      P.op ⋙ G.extModuleDiagram B τ n :=
  ((F.op ⋙ extFunctor.{max r w} n).flip).coefficientTensorDiagramMap
    ((G.op ⋙ extFunctor.{max r w} n).flip) σ A B ρ τ P.op
    (L.extDiagramMap F (P ⋙ G) e φ n)
    (fun a => L.extDiagramMap_coefficients F G P e φ φ (ρ a) (τ (σ a)) (hφ a) n)

/-- The original mate unit, evaluated on the original Ext class. -/
theorem extScalarTensorDiagramMap_one_tmul
    (U : Iᵒᵖ) (x : Ext.{max r w} (F.obj U.unop) A n) :
    letI := F.extCoefficientModule A ρ n U
    (L.extScalarTensorDiagramMap F G P e σ A B ρ τ φ hφ n).app U
      ((1 : S) ⊗ₜ[R,σ] x) = L.extCoefficientTransfer (e.inv.app U.unop) φ n x :=
  ((F.op ⋙ extFunctor.{max r w} n).flip).coefficientTensorDiagramMap_one_tmul
    ((G.op ⋙ extFunctor.{max r w} n).flip) σ A B ρ τ P.op
    (L.extDiagramMap F (P ⋙ G) e φ n)
    (fun a => L.extDiagramMap_coefficients F G P e φ φ (ρ a) (τ (σ a)) (hφ a) n) U x

end CategoryTheory.Functor
