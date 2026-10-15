/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.FreeAbelianPullback
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules
public import Mathlib.Topology.Sheaves.MayerVietoris
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-! # Geometric compatibility of the original Mayer–Vietoris sequence

Actual inverse image carries the native open-free Mayer–Vietoris short
complex to the native short complex on the inverse-image opens. Its
extension class therefore retains the original geometric connecting map.
All coefficient sheaves and scheme morphisms are arbitrary.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Abelian

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The generic native open-free inverse-image comparison on the Zariski site. -/
abbrev additiveOpenPullbackIso :
    additiveOpenFreeFunctor X ⋙ zariskiPullback p ≅
      Opens.map p.base ⋙ additiveOpenFreeFunctor Y :=
  TopCat.Sheaf.openFreeAbelianPullbackIso p.base

/-- The native Mayer–Vietoris square with all four opens taken by actual inverse image. -/
def mayerVietorisPullbackSquare (U V : X.Opens) :
    (Opens.grothendieckTopology Y).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    ((Opens.mayerVietorisSquare U V).toSquare.map (Opens.map p.base)) rfl rfl

/-- Actual inverse image identifies the original native Mayer–Vietoris short complexes. -/
def mayerVietorisPullbackShortComplexIso (U V : X.Opens) :
    ((Opens.mayerVietorisSquare U V).shortComplex.map (zariskiPullback p)) ≅
      (mayerVietorisPullbackSquare p U V).shortComplex := by
  refine ShortComplex.isoMk ((additiveOpenPullbackIso p).app (U ⊓ V))
    ((zariskiPullback p).mapBiprod ((additiveOpenFreeFunctor X).obj U)
        ((additiveOpenFreeFunctor X).obj V) ≪≫
      biprod.mapIso ((additiveOpenPullbackIso p).app U) ((additiveOpenPullbackIso p).app V))
    ((additiveOpenPullbackIso p).app (U ⊔ V)) ?_ ?_
  · apply biprod.hom_ext
    · dsimp [GrothendieckTopology.MayerVietorisSquare.shortComplex,
        mayerVietorisPullbackSquare]
      simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      erw [← Functor.map_comp_assoc, biprod.lift_fst]
      exact ((additiveOpenPullbackIso p).hom.naturality
        (homOfLE (show U ⊓ V ≤ U from inf_le_left))).symm
    · dsimp [GrothendieckTopology.MayerVietorisSquare.shortComplex,
        mayerVietorisPullbackSquare]
      simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
      erw [← Functor.map_comp_assoc, biprod.lift_snd]
      erw [(zariskiPullback p).map_neg]
      simp only [Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg
        ((additiveOpenPullbackIso p).hom.naturality
          (homOfLE (show U ⊓ V ≤ V from inf_le_right))).symm
  · rw [← cancel_epi ((zariskiPullback p).mapBiprod
      ((additiveOpenFreeFunctor X).obj U) ((additiveOpenFreeFunctor X).obj V)).inv]
    simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
    apply biprod.hom_ext'
    · dsimp [GrothendieckTopology.MayerVietorisSquare.shortComplex,
        mayerVietorisPullbackSquare]
      simp only [biprod.inl_desc, biprod.inl_map_assoc, biprod.inl_desc_assoc]
      erw [← Functor.map_comp_assoc, biprod.inl_desc]
      exact ((additiveOpenPullbackIso p).hom.naturality
        (homOfLE (show U ≤ U ⊔ V from le_sup_left))).symm
    · dsimp [GrothendieckTopology.MayerVietorisSquare.shortComplex,
        mayerVietorisPullbackSquare]
      simp only [biprod.inr_desc, biprod.inr_map_assoc, biprod.inr_desc_assoc]
      erw [← Functor.map_comp_assoc, biprod.inr_desc]
      exact ((additiveOpenPullbackIso p).hom.naturality
        (homOfLE (show V ≤ U ⊔ V from le_sup_right))).symm

/-- The original geometric map on the native open-Ext cohomology presheaves. -/
def zariskiCohomologyOpenMap
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B) (n : ℕ) :
    Sheaf.cohomologyPresheaf.{u + 1} A n ⟶
      (Opens.map p.base).op ⋙ Sheaf.cohomologyPresheaf.{u + 1} B n where
  app U := AddCommGrpCat.ofHom
    (((Ext.mk₀ a).postcomp ((additiveOpenFreeFunctor Y).obj (p ⁻¹ᵁ U.unop))
      (Nat.add_zero n)).comp
      (((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app U.unop)).precomp
        ((zariskiPullback p).obj A) (Nat.zero_add n)).comp
        ((zariskiPullback p).mapExtAddHom ((additiveOpenFreeFunctor X).obj U.unop) A n)))
  naturality U V i := by
    ext x
    change Ext.{u + 1} ((additiveOpenFreeFunctor X).obj U.unop) A n at x
    change ((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app V.unop)).comp
        (((Ext.mk₀ ((additiveOpenFreeFunctor X).map i.unop)).comp x
          (Nat.zero_add n)).mapExactFunctor (zariskiPullback p))
        (Nat.zero_add n)).comp (Ext.mk₀ a) (Nat.add_zero n) =
      (Ext.mk₀ ((additiveOpenFreeFunctor Y).map ((Opens.map p.base).map i.unop))).comp
        (((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app U.unop)).comp
          (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
          (Ext.mk₀ a) (Nat.add_zero n)) (Nat.zero_add n)
    simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      ← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀]
    have hn := ((additiveOpenPullbackIso p).inv.naturality i.unop).symm
    exact congrArg (fun k => ((Ext.mk₀ k).comp (x.mapExactFunctor (zariskiPullback p))
      (Nat.zero_add n)).comp (Ext.mk₀ a) (Nat.add_zero n)) hn

/-- The actual extension class of the inverse-image Mayer–Vietoris sequence is the
image of the original extension class under the original open-free comparisons. -/
theorem mayerVietorisPullback_extClass_inv (U V : X.Opens) :
    (Ext.mk₀ ((additiveOpenPullbackIso p).inv.app (U ⊔ V))).comp
        ((Opens.mayerVietorisSquare U V).shortComplex_shortExact.extClass.mapExactFunctor
          (zariskiPullback p)) (Nat.zero_add 1) =
      (mayerVietorisPullbackSquare p U V).shortComplex_shortExact.extClass.comp
        (Ext.mk₀ ((additiveOpenPullbackIso p).inv.app (U ⊓ V))) (Nat.add_zero 1) := by
  rw [Ext.mapExactFunctor_extClass]
  exact (ShortComplex.ShortExact.extClass_naturality
    (mayerVietorisPullbackSquare p U V).shortComplex_shortExact
    ((Opens.mayerVietorisSquare U V).shortComplex_shortExact.map_of_exact (zariskiPullback p))
    (mayerVietorisPullbackShortComplexIso p U V).inv).symm

/-- The original geometric open-cohomology maps commute with the native Mayer–Vietoris
connecting homomorphism. -/
theorem mayerVietoris_delta_geometric (U V : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B) (n : ℕ) :
    (Opens.mayerVietorisSquare U V).δ A n (n + 1) rfl ≫
        (zariskiCohomologyOpenMap p A B a (n + 1)).app (op (U ⊔ V)) =
      (zariskiCohomologyOpenMap p A B a n).app (op (U ⊓ V)) ≫
        (mayerVietorisPullbackSquare p U V).δ B n (n + 1) rfl := by
  ext x
  change Ext.{u + 1} ((additiveOpenFreeFunctor X).obj (U ⊓ V)) A n at x
  let c := (Opens.mayerVietorisSquare U V).shortComplex_shortExact.extClass
  let d := (mayerVietorisPullbackSquare p U V).shortComplex_shortExact.extClass
  change ((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app (U ⊔ V))).comp
      ((c.comp x (show 1 + n = n + 1 by omega)).mapExactFunctor (zariskiPullback p))
      (Nat.zero_add (n + 1))).comp (Ext.mk₀ a) (Nat.add_zero (n + 1)) =
    d.comp (((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app (U ⊓ V))).comp
      (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
      (Ext.mk₀ a) (Nat.add_zero n)) (show 1 + n = n + 1 by omega)
  rw [Ext.mapExactFunctor_comp]
  rw [← Ext.comp_assoc _ _ _ (Nat.zero_add 1) (show 1 + n = n + 1 by omega)
    (show 0 + 1 + n = n + 1 by omega)]
  rw [mayerVietorisPullback_extClass_inv]
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]

/-- Coefficient maps commute with the native Mayer–Vietoris connecting homomorphism. -/
theorem mayerVietoris_delta_coefficient (U V : X.Opens)
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (a : A ⟶ B) (n : ℕ) :
    (Opens.mayerVietorisSquare U V).δ A n (n + 1) rfl ≫
        ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) (n + 1)).map a).app
          (op (U ⊔ V)) =
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map a).app
        (op (U ⊓ V)) ≫ (Opens.mayerVietorisSquare U V).δ B n (n + 1) rfl := by
  ext x
  change Ext.{u + 1} ((additiveOpenFreeFunctor X).obj (U ⊓ V)) A n at x
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ (show 1 + n = n + 1 by omega)

end AlgebraicGeometry.Scheme.Cohomology
