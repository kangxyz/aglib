/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.Transfer
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.TopComparison

/-! # Scalar Ext top comparison from the original source objects

The original opposite source categories index the complete scalar Ext functors.
Their actual source maps and isomorphisms construct both open and global
objects and transfers together. No auxiliary indexing model or independently
supplied native cohomology module is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped ChangeOfRings TensorProduct

universe u v u' v' r w

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{max r w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{max r w} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {R S : Type r} [CommRing R] [CommRing S] (σ : R →+* S)
  (A : C) (B : D) (ρ : R →+* End A) (τ : S →+* End B)
  (φ : L.obj A ⟶ B) (hφ : ∀ a : R, L.map (ρ a) ≫ φ = φ ≫ τ (σ a)) (n : ℕ)

/-- Exact transfer on the whole original opposite source category. -/
def extScalarSourceTransformation :
    (𝟭 C).extModuleDiagram A ρ n ⟶
      (L.op ⋙ (𝟭 D).extModuleDiagram B τ n) ⋙ ModuleCat.restrictScalars σ :=
  L.extScalarDiagramMap (𝟭 C) (𝟭 D) L (Iso.refl _) σ A B ρ τ φ hφ n

/-- Retain the actual source arrow in the same complete scalar Ext functors. -/
def extScalarSourceMap {U : C} {V : D} (s : V ⟶ L.obj U) :
    ((𝟭 C).extModuleDiagram A ρ n).obj (op U) ⟶
      (ModuleCat.restrictScalars σ).obj (((𝟭 D).extModuleDiagram B τ n).obj (op V)) :=
  (L.extScalarSourceTransformation σ A B ρ τ φ hφ n).app (op U) ≫
    (ModuleCat.restrictScalars σ).map (((𝟭 D).extModuleDiagram B τ n).map s.op)

/-- The source-map construction is exactly the original exact Ext transfer. -/
theorem extScalarSourceMap_apply {U : C} {V : D} (s : V ⟶ L.obj U)
    (x : Ext.{max r w} U A n) :
    L.extScalarSourceMap σ A B ρ τ φ hφ n s x = L.extCoefficientTransfer s φ n x := by
  change (Ext.mk₀ s).comp
      (((Ext.mk₀ (𝟙 (L.obj U))).comp (x.mapExactFunctor L) (Nat.zero_add n)).comp
        (Ext.mk₀ φ) (Nat.add_zero n)) (Nat.zero_add n) =
    ((Ext.mk₀ s).comp (x.mapExactFunctor L) (Nat.zero_add n)).comp
      (Ext.mk₀ φ) (Nat.add_zero n)
  simp only [Ext.mk₀_id_comp, Ext.comp_assoc_of_third_deg_zero]

/-- The source-transfer mate uses the original scalar adjunction. -/
def extScalarSourceMate {U : C} {V : D} (s : V ⟶ L.obj U) :
    (ModuleCat.extendScalars σ).obj (((𝟭 C).extModuleDiagram A ρ n).obj (op U)) ⟶
      ((𝟭 D).extModuleDiagram B τ n).obj (op V) :=
  ((ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ).homEquiv _ _).symm
    (L.extScalarSourceMap σ A B ρ τ φ hφ n s)

/-- The mate's unit retains the original class and original exact transfer. -/
theorem extScalarSourceMate_one_tmul {U : C} {V : D} (s : V ⟶ L.obj U)
    (x : Ext.{max r w} U A n) :
    letI := (𝟭 C).extCoefficientModule A ρ n (op U)
    L.extScalarSourceMate σ A B ρ τ φ hφ n s ((1 : S) ⊗ₜ[R,σ] x) =
      L.extCoefficientTransfer s φ n x := by
  have h := Equiv.apply_symm_apply
    ((ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ).homEquiv _ _)
    (L.extScalarSourceMap σ A B ρ τ φ hφ n s)
  exact (congrArg (fun f => f x) h).trans
    (L.extScalarSourceMap_apply σ A B ρ τ φ hφ n s x)

variable {U₀ U₁ U₂ : C} {V₁ V₂ : D}
  (j : U₁ ⟶ U₀) (eU : U₁ ≅ U₂) (eV : V₁ ≅ V₂)
  (s₁ : V₁ ⟶ L.obj U₁) (s₂ : V₂ ⟶ L.obj U₂)
  (hs : eV.inv ≫ s₁ = s₂ ≫ L.map eU.inv)

include hs in
/-- Original source coherence gives the whole coefficient-linear top square. -/
theorem extScalarSourceMap_top :
    L.extScalarSourceMap σ A B ρ τ φ hφ n s₁ ≫
        (ModuleCat.restrictScalars σ).map
          ((((𝟭 D).extModuleDiagram B τ n).mapIso eV.op).symm.hom) =
      (((𝟭 C).extModuleDiagram A ρ n).mapIso eU.op).symm.hom ≫
        L.extScalarSourceMap σ A B ρ τ φ hφ n s₂ := by
  let F := (𝟭 C).extModuleDiagram A ρ n
  let G := (𝟭 D).extModuleDiagram B τ n
  let T := L.extScalarSourceTransformation σ A B ρ τ φ hφ n
  let res := ModuleCat.restrictScalars σ
  have hs' : s₁.op ≫ eV.inv.op = (L.map eU.inv).op ≫ s₂.op :=
    congrArg (fun f => f.op) hs
  change (T.app (op U₁) ≫ res.map (G.map s₁.op)) ≫ res.map (G.map eV.inv.op) =
    F.map eU.inv.op ≫ (T.app (op U₂) ≫ res.map (G.map s₂.op))
  calc
    _ = T.app (op U₁) ≫ res.map (G.map (s₁.op ≫ eV.inv.op)) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = T.app (op U₁) ≫ res.map (G.map ((L.map eU.inv).op ≫ s₂.op)) :=
      congrArg (fun f => T.app (op U₁) ≫ res.map (G.map f)) hs'
    _ = (T.app (op U₁) ≫ res.map (G.map (L.map eU.inv).op)) ≫
        res.map (G.map s₂.op) := by simp only [Functor.map_comp, Category.assoc]
    _ = (F.map eU.inv.op ≫ T.app (op U₂)) ≫ res.map (G.map s₂.op) :=
      congrArg (fun f => f ≫ res.map (G.map s₂.op)) (T.naturality eU.inv.op).symm
    _ = _ := Category.assoc _ _ _

/-- Construct all five original scalar Ext objects and their top comparison
from the same source functors, before any native sheaf specialization. -/
def extScalarTopComparison : ModuleCat.TensorTopComparison.{r, w} σ := by
  let F := (𝟭 C).extModuleDiagram A ρ n
  let G := (𝟭 D).extModuleDiagram B τ n
  let η₁ := L.extScalarSourceMap σ A B ρ τ φ hφ n s₁
  let η₂ := L.extScalarSourceMap σ A B ρ τ φ hφ n s₂
  let eA := (F.mapIso eU.op).symm
  let eB := (G.mapIso eV.op).symm
  let adj := ModuleCat.extendRestrictScalarsAdj.{max r w, r, r} σ
  exact ModuleCat.TensorTopComparison.ofMaps
    (F.obj (op U₀)) (F.obj (op U₁)) (F.obj (op U₂))
    (G.obj (op V₁)) (G.obj (op V₂)) (F.map j.op) η₁ eA eB
    (L.extScalarSourceMate σ A B ρ τ φ hφ n s₂)
    (adj.homEquiv_naturality_right_square eA.hom η₂ η₁ eB.hom
      (L.extScalarSourceMap_top σ A B ρ τ φ hφ n eU eV s₁ s₂ hs).symm).symm

/-- The retained source top isomorphism has the original inverse-source action. -/
theorem extScalarTopComparison_sourceTop_hom (x : Ext.{max r w} U₁ A n) :
    (L.extScalarTopComparison σ A B ρ τ φ hφ n j eU eV s₁ s₂ hs).sourceTop.hom x =
      (Ext.mk₀ eU.inv).comp x (Nat.zero_add n) := rfl

/-- The inverse source top isomorphism has the original forward-source action. -/
theorem extScalarTopComparison_sourceTop_inv (x : Ext.{max r w} U₂ A n) :
    (L.extScalarTopComparison σ A B ρ τ φ hφ n j eU eV s₁ s₂ hs).sourceTop.inv x =
      (Ext.mk₀ eU.hom).comp x (Nat.zero_add n) := rfl

/-- The retained target top isomorphism has the original inverse-source action. -/
theorem extScalarTopComparison_targetTop_hom (x : Ext.{max r w} V₁ B n) :
    (L.extScalarTopComparison σ A B ρ τ φ hφ n j eU eV s₁ s₂ hs).targetTop.hom x =
      (Ext.mk₀ eV.inv).comp x (Nat.zero_add n) := rfl

/-- The inverse target top isomorphism has the original forward-source action. -/
theorem extScalarTopComparison_targetTop_inv (x : Ext.{max r w} V₂ B n) :
    (L.extScalarTopComparison σ A B ρ τ φ hφ n j eU eV s₁ s₂ hs).targetTop.inv x =
      (Ext.mk₀ eV.hom).comp x (Nat.zero_add n) := rfl

/-- The global mate retains the literal original class and exact transfer. -/
theorem extScalarTopComparison_globalTensor_one_tmul (x : Ext.{max r w} U₂ A n) :
    letI := (𝟭 C).extCoefficientModule A ρ n (op U₂)
    (L.extScalarTopComparison σ A B ρ τ φ hφ n j eU eV s₁ s₂ hs).globalTensor
      ((1 : S) ⊗ₜ[R,σ] x) = L.extCoefficientTransfer s₂ φ n x :=
  L.extScalarSourceMate_one_tmul σ A B ρ τ φ hφ n s₂ x

end CategoryTheory.Functor
