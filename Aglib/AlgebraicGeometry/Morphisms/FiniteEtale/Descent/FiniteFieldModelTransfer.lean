/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCommonMorphisms
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalOverDescent

/-! Transport of actual local models and their structural isomorphisms along one stage map. -/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
universe u

section Charts
variable {S B T : Scheme.{u}} (𝒰 : S.OpenCover)
  [Category.{u} 𝒰.I₀] [𝒰.LocallyDirected]
  (a : B ⟶ S) (b : T ⟶ B) (f : T ⟶ S) (h : b ≫ a = f)

/-- The existing pulled-back open cover and the over-category pullback have opposite factor order.
-/
def chartPullbackIso : chartDiagram (𝒰.pullback₁ a) ≅ chartDiagram 𝒰 ⋙ Over.pullback a :=
  NatIso.ofComponents (fun i ↦ Over.isoMk (pullbackSymmetry a (𝒰.f i))
    (pullbackSymmetry_hom_comp_snd _ _)) (by
      intro i j d
      apply Over.OverMorphism.ext
      change (pullback.map a (𝒰.f i) a (𝒰.f j) (𝟙 _) (𝒰.trans d) (𝟙 _) (by simp) (by simp)) ≫
        (pullbackSymmetry a (𝒰.f j)).hom =
          (pullbackSymmetry a (𝒰.f i)).hom ≫ ((Over.pullback a).map ((chartDiagram 𝒰).map d)).left
      apply pullback.hom_ext <;>
        simp [chartDiagram, Scheme.Cover.functorOfLocallyDirected, Over.pullback_map_left,
          Category.assoc])

/-- Comparison of the geometric chart diagrams before and after changing the finite stage. -/
def geometricChartTransferIso :
    chartDiagram (𝒰.pullback₁ a) ⋙ Over.pullback b ≅ chartDiagram 𝒰 ⋙ Over.pullback f :=
  Functor.isoWhiskerRight (chartPullbackIso 𝒰 a) (Over.pullback b) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (chartDiagram 𝒰) (overCompNatIso a b f h)

variable (Y : Scheme.FiniteEtale T)

/-- The comparison of geometric local diagrams for the pulled-back cover and the original cover,
using the factorization `h`. -/
def geometricModelTransferIso : geometricLocalDiagram b (𝒰.pullback₁ a) Y ≅
    geometricLocalDiagram f 𝒰 Y :=
  Functor.isoWhiskerRight (geometricChartTransferIso 𝒰 a b f h)
    (Over.pullback Y.obj.hom ⋙ Over.map Y.obj.hom)

@[reassoc] theorem geometricModelTransferIso_structure (i : 𝒰.I₀) :
    (geometricModelTransferIso 𝒰 a b f h Y).hom.app i ≫
        (geometricLocalStructure f 𝒰 Y).app i =
      (geometricLocalStructure b (𝒰.pullback₁ a) Y).app i ≫
        (geometricChartTransferIso 𝒰 a b f h).hom.app i :=
  ((Over.mapPullbackAdj Y.obj.hom).counit.naturality
    ((geometricChartTransferIso 𝒰 a b f h).hom.app i))

variable (A : 𝒰.I₀ → Over S) (m : ∀ i, A i ⟶ (chartDiagram 𝒰).obj i)
  (α : ∀ i, (Over.pullback f).obj (A i) ≅ (geometricLocalDiagram f 𝒰 Y).obj i)
  (hm : ∀ i, (Over.pullback f).map (m i) =
    (α i).hom ≫ (geometricLocalStructure f 𝒰 Y).app i)

/-- The local model `A i` pulled back along `a` to a scheme over `B`. -/
def transferredObject (i : 𝒰.I₀) : Over B := (Over.pullback a).obj (A i)

/-- The structural map of the transferred model to its pulled-back chart. -/
def transferredStructure (i : 𝒰.I₀) :
    transferredObject 𝒰 a A i ⟶ (chartDiagram (𝒰.pullback₁ a)).obj i :=
  (Over.pullback a).map (m i) ≫ (chartPullbackIso 𝒰 a).inv.app i

/-- The geometric identification of the transferred model, obtained from `α` and the base-change
comparison. -/
def transferredIso (i : 𝒰.I₀) :
    (Over.pullback b).obj (transferredObject 𝒰 a A i) ≅
      (geometricLocalDiagram b (𝒰.pullback₁ a) Y).obj i :=
  overCompIso a b f h (A i) ≪≫ α i ≪≫ (geometricModelTransferIso 𝒰 a b f h Y).symm.app i

include hm in
theorem transferredStructure_commutes (i : 𝒰.I₀) :
    (Over.pullback b).map (transferredStructure 𝒰 a A m i) =
      (transferredIso 𝒰 a b f h Y A α i).hom ≫
        (geometricLocalStructure b (𝒰.pullback₁ a) Y).app i := by
  apply (cancel_mono ((geometricChartTransferIso 𝒰 a b f h).hom.app i)).mp
  simp only [transferredStructure, Functor.map_comp, Category.assoc]
  have Hβ : (Over.pullback b).map ((chartPullbackIso 𝒰 a).inv.app i) ≫
      (geometricChartTransferIso 𝒰 a b f h).hom.app i =
        (overCompIso a b f h ((chartDiagram 𝒰).obj i)).hom := by
    simp [geometricChartTransferIso, overCompNatIso]
  rw [Hβ, overCompIso_naturality, hm]
  simp only [transferredIso, Iso.trans_hom, Category.assoc]
  rw [← geometricModelTransferIso_structure]
  simp

instance transferredStructure_finite [∀ i, IsFinite (m i).left] (i : 𝒰.I₀) :
    IsFinite (transferredStructure 𝒰 a A m i).left := by
  have : IsFinite ((Over.pullback a).map (m i)).left :=
    MorphismProperty.of_isPullback (overPullback_map_isPullback a (m i)).flip inferInstance
  change IsFinite (((Over.pullback a).map (m i)).left ≫ ((chartPullbackIso 𝒰 a).inv.app i).left)
  infer_instance

instance transferredStructure_etale [∀ i, Etale (m i).left] (i : 𝒰.I₀) :
    Etale (transferredStructure 𝒰 a A m i).left := by
  have : Etale ((Over.pullback a).map (m i)).left :=
    MorphismProperty.of_isPullback (overPullback_map_isPullback a (m i)).flip inferInstance
  change Etale (((Over.pullback a).map (m i)).left ≫ ((chartPullbackIso 𝒰 a).inv.app i).left)
  infer_instance

/-- A descended old-stage arrow has the required conjugate image for the transported models. -/
theorem transferred_arrow {i j : 𝒰.I₀} (d : i ⟶ j)
    (g : transferredObject 𝒰 a A i ⟶ transferredObject 𝒰 a A j)
    (hg : (Over.pullback b).map g ≫ (overCompIso a b f h (A j)).hom =
      (overCompIso a b f h (A i)).hom ≫ (α i).hom ≫
        (geometricLocalDiagram f 𝒰 Y).map d ≫ (α j).inv) :
    (Over.pullback b).map g =
      (transferredIso 𝒰 a b f h Y A α i).hom ≫
        (geometricLocalDiagram b (𝒰.pullback₁ a) Y).map d ≫
          (transferredIso 𝒰 a b f h Y A α j).inv := by
  apply (cancel_mono ((overCompIso a b f h (A j)).hom)).mp
  rw [hg]
  simp only [transferredIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_inv, Iso.app_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [((geometricModelTransferIso 𝒰 a b f h Y).hom.naturality_assoc d)]
  simp
end Charts
end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 5516ec3eb35f7961f84b4acff4e110badb98c80c1971ef6ac285bdc7a9dbb1b1.
Definitions, hypotheses and universes are retained modulo native names. -/
