/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomSection
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.Bidual` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`8cfac6a70c7f4e910be55eff3621c3a7e6b39aef9c7b667c093d04105517fd60`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules (locallyBijective_of_local_isIso)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle dualEvaluationIso dualEvaluationIso_hom dualLineBundle dualLocalIso
    dualSheaf evaluationPresheaf evaluationSheaf isLocallyRankOne_iff_local_unit)
open _root_.AlgebraicGeometry.Scheme.Modules
  (tensorSheafBraiding tensorSheafLeftUnit tensorSheafMap)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Original statements, maps and hypotheses are preserved. General foundations use
native Aglib; the transpose/evaluation proof is adapted via native sheafification
naturality. Historical source and validation receipts below retain their
original basis. Native compilation of this module, including reassoc generation, passed against
Aglib `415896064689def8ca298cefd3dcbc979e103099`.
-/
/-!
# Canonical biduality of actual line bundles

The bidual map is literal evaluation on the constructed internal Hom sheaf.
Genuine local unit bases prove that this canonical map is an isomorphism for
line bundles. Its evaluation square identifies a morphism with its transpose
using the actual tensor symmetry and unit isomorphism. No additional theorem
family is retained.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable (X : Scheme.{u}) (M : SheafOfModules.{u} X.ringCatSheaf)

/-- Evaluation by a section, on every smaller open. -/
def bidualSection (U : X.Opens) (m : M.val.obj (op U)) :
    (dualSheaf X (dualSheaf X M)).val.obj (op U) :=
  ⟨{
    app V := AddCommGrpCat.ofHom {
      toFun ell := ell.val.app (op (Over.mk (𝟙 V.unop.left)))
        (M.val.map V.unop.hom.op m)
      map_zero' := rfl
      map_add' ell ell' := rfl }
    naturality {V W} i := by
      ext ell
      change ell.val.app (op (Over.mk i.unop.left)) (M.val.map W.unop.hom.op m) =
        X.presheaf.map i.unop.left.op
          (ell.val.app (op (Over.mk (𝟙 V.unop.left))) (M.val.map V.unop.hom.op m))
      have hn := NatTrans.naturality_apply ell.val
        (Over.homMk i.unop.left : Over.mk i.unop.left ⟶
          Over.mk (𝟙 V.unop.left)).op (M.val.map V.unop.hom.op m)
      change ell.val.app (op (Over.mk i.unop.left))
          (M.val.map i.unop.left.op (M.val.map V.unop.hom.op m)) = _ at hn
      rw [← M.val.map_comp_apply, ← op_comp, Over.w i.unop] at hn
      exact hn
  }, by
    intro V r ell
    change X.presheaf.map (𝟙 V.unop.left).op r •
      (show Γ(X, V.unop.left) from ell.val.app (op (Over.mk (𝟙 V.unop.left)))
        (M.val.map V.unop.hom.op m)) = _
    simp⟩

/-- The canonical evaluation morphism to the actual double dual. -/
def bidualMap : M ⟶ dualSheaf X (dualSheaf X M) where
  val.app U := ModuleCat.ofHom {
    toFun m := bidualSection X M U.unop m
    map_add' m n := by
      apply Subtype.ext
      change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom X (dualSheaf X M)
        (SheafOfModules.unit X.ringCatSheaf) U.unop) = _
      ext V ell
      change ell.val.app (op (Over.mk (𝟙 V.unop.left))) (M.val.map V.unop.hom.op (m + n)) = _
      rw [map_add, map_add]
      rfl
    map_smul' r m := by
      apply Subtype.ext
      change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom X (dualSheaf X M)
        (SheafOfModules.unit X.ringCatSheaf) U.unop) = _
      ext V ell
      change ell.val.app (op (Over.mk (𝟙 V.unop.left)))
          (M.val.map V.unop.hom.op (r • m)) =
        X.presheaf.map V.unop.hom.op r •
          (show Γ(X, V.unop.left) from ell.val.app (op (Over.mk (𝟙 V.unop.left)))
            (M.val.map V.unop.hom.op m))
      rw [M.val.map_smul]
      exact ell.property _ _ _ }
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom X (dualSheaf X M)
      (SheafOfModules.unit X.ringCatSheaf) V.unop) = _
    ext W ell
    change ell.val.app (op (Over.mk (𝟙 W.unop.left))) (M.val.map W.unop.hom.op (M.val.map i m)) =
      ell.val.app (op (Over.mk (𝟙 W.unop.left))) (M.val.map (W.unop.hom ≫ i.unop).op m)
    rw [← M.val.map_comp_apply, op_comp]
    rfl

/-- The defining formula is literally evaluation, with restriction to the chosen open. -/
@[simp] theorem bidualMap_apply (U : X.Opens) (m : M.val.obj (op U))
    (V : (Over U)ᵒᵖ) (ell : (dualSheaf X M).val.obj (op V.unop.left)) :
    ((bidualMap X M).val.app (op U) m).val.app V ell =
      ell.val.app (op (Over.mk (𝟙 V.unop.left))) (M.val.map V.unop.hom.op m) := rfl

@[simp] theorem bidualMap_evaluate (U : X.Opens) (m : M.val.obj (op U))
    (ell : (dualSheaf X M).val.obj (op U)) :
    ((bidualMap X M).val.app (op U) m).val.app (op (Over.mk (𝟙 U))) ell =
      ell.val.app (op (Over.mk (𝟙 U))) m := by
  rw [bidualMap_apply]
  congr 1
  change M.val.presheaf.map (𝟙 (op U)) m = m
  exact ConcreteCategory.congr_hom (M.val.presheaf.map_id (op U)) m

/-- In the dual unit coordinates induced from a local basis, bidual evaluation
has exactly the original coordinates. -/
theorem bidualMap_local_coordinates (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).map (bidualMap X M) ≫
      (dualLocalIso X (dualSheaf X M) U (dualLocalIso X M U e)).hom = e.hom := by
  apply SheafOfModules.hom_ext
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change ((bidualMap X M).val.app (op V.unop.left) m).val.app
      (op (Over.mk (𝟙 V.unop.left)))
      ((dualLocalIso X M U e).inv.val.app V (1 : Γ(X, V.unop.left))) =
    e.hom.val.app V m
  rw [bidualMap_evaluate]
  change (show Γ(X, V.unop.left) from e.hom.val.app V m) *
      X.presheaf.map (𝟙 V.unop.left).op (1 : Γ(X, V.unop.left)) =
    e.hom.val.app V m
  rw [map_one, mul_one]

/-- Bidual evaluation is an isomorphism on every genuine unit chart. -/
theorem bidualMap_over_isIso (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map (bidualMap X M)) := by
  let d := dualLocalIso X (dualSheaf X M) U (dualLocalIso X M U e)
  have h : (SheafOfModules.overFunctor X.ringCatSheaf U).map (bidualMap X M) =
      (e ≪≫ d.symm).hom := by
    apply (cancel_mono d.hom).mp
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using bidualMap_local_coordinates X M U e
  rw [h]
  infer_instance

/-- Actual local unit bases prove that the canonical map, rather than an
isomorphism merely obtained from a Picard-class equality, is invertible. -/
instance bidualMap_isIso (L : LineBundle X) : IsIso (bidualMap X L.val) := by
  have h := locallyBijective_of_local_isIso X (bidualMap X L.val).val (by
    intro x
    obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
    refine ⟨U, hxU, ?_⟩
    have := bidualMap_over_isIso X L.val U e
    exact Functor.map_isIso (SheafOfModules.forget (X.ringCatSheaf.over U))
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map (bidualMap X L.val)))
  have := h.1
  have := h.2
  have : IsIso ((SheafOfModules.forget X.ringCatSheaf).map (bidualMap X L.val)) :=
    _root_.PresheafOfModules.isIso_of_locallyBijective (J := Opens.grothendieckTopology X)
      (bidualMap X L.val).val L.val.isSheaf (dualSheaf X (dualSheaf X L.val)).isSheaf
  exact isIso_of_reflects_iso (bidualMap X L.val) (SheafOfModules.forget X.ringCatSheaf)

/-- The canonical bidual isomorphism of an actual line bundle. -/
def bidualIso (L : LineBundle X) : L.val ≅ (dualLineBundle X (dualLineBundle X L)).val :=
  asIso (bidualMap X L.val)

@[simp] theorem bidualIso_hom (L : LineBundle X) : (bidualIso X L).hom = bidualMap X L.val := rfl

/-- The bidual evaluation square before sheafification. -/
theorem bidualMap_transpose_evaluationPresheaf
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        (bidualMap X M).val (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ).val ≫
      evaluationPresheaf X (dualSheaf X M) (SheafOfModules.unit X.ringCatSheaf) =
    (BraidedCategory.braiding (C := PresheafOfModulesOfCommRing.{u} X.presheaf)
        M.val (SheafOfModules.unit X.ringCatSheaf).val).hom ≫
      (MonoidalCategory.leftUnitor (C := PresheafOfModulesOfCommRing.{u} X.presheaf)
        M.val).hom ≫ φ.val := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m r
  change ((bidualMap X M).val.app U m).val.app (op (Over.mk (𝟙 U.unop)))
      ((AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ).val.app U r) = φ.val.app U
          (r • m)
  rw [bidualMap_evaluate, AlgebraicGeometry.Scheme.Modules.InternalHom.transpose_apply]
  change X.presheaf.map (𝟙 U.unop).op r • φ.val.app U m = φ.val.app U (r • m)
  rw [show X.presheaf.map (𝟙 U.unop).op r = r by simp]
  exact ((φ.val.app U).hom.map_smul r m).symm

/-- Evaluation of a transposed actual morphism after canonical biduality is
that morphism after the actual right-unit isomorphism. -/
@[reassoc] theorem bidualMap_transpose_evaluation
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheafMap X (bidualMap X M) (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ) ≫
      evaluationSheaf X (dualSheaf X M) (SheafOfModules.unit X.ringCatSheaf) =
    (tensorSheafBraiding X M (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (tensorSheafLeftUnit X M).hom ≫ φ := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)
  let unitSheaf : SheafOfModules.{u} X.ringCatSheaf :=
    SheafOfModules.unit X.ringCatSheaf
  let l := (MonoidalCategory.leftUnitor
    (C := PresheafOfModulesOfCommRing.{u} X.presheaf) M.val).hom
  have hl : (tensorSheafLeftUnit X M).hom = (adj.homEquiv _ M).symm l :=
    (adj.homEquiv_counit _ _ l).symm
  have hev (P Q : SheafOfModules.{u} X.ringCatSheaf) :
      evaluationSheaf X P Q = (adj.homEquiv _ Q).symm (evaluationPresheaf X P Q) := by
    have he : adj.homEquiv
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
          (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X P Q).val P.val) Q =
        PresheafOfModules.sheafificationHomEquiv.{u} (𝟙 X.ringCatSheaf.obj) := by
      apply Equiv.ext
      intro f
      exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
    rw [he]
    rfl
  have hmap {P P' Q Q' : SheafOfModules.{u} X.ringCatSheaf}
      (a : P ⟶ P') (b : Q ⟶ Q') :
      tensorSheafMap X a b =
        (PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)).map
          (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) a.val b.val) := rfl
  have hbraid (P Q : SheafOfModules.{u} X.ringCatSheaf) :
      (tensorSheafBraiding X P Q).hom =
        (PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)).map
          (BraidedCategory.braiding
            (C := PresheafOfModulesOfCommRing.{u} X.presheaf) P.val Q.val).hom := rfl
  rw [hl, hev, hmap, hbraid]
  erw [← adj.homEquiv_naturality_left_symm (Y := unitSheaf)
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        (bidualMap X M).val (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ).val)
      (evaluationPresheaf X (dualSheaf X M) (SheafOfModules.unit X.ringCatSheaf)),
    ← adj.homEquiv_naturality_right_symm (Y := M) (Y' := unitSheaf) l φ,
    ← adj.homEquiv_naturality_left_symm (Y := unitSheaf)
      (BraidedCategory.braiding (C := PresheafOfModulesOfCommRing.{u} X.presheaf)
        M.val (SheafOfModules.unit X.ringCatSheaf).val).hom
      (l ≫ (SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map φ)]
  exact congrArg (adj.homEquiv _ unitSheaf).symm
    (bidualMap_transpose_evaluationPresheaf X M φ)

/-- The evaluation compatibility in the exact dual-line-bundle form. -/
@[reassoc] theorem bidualMap_transpose_dualEvaluation (L : LineBundle X)
    (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheafMap X (bidualMap X L.val)
        (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ) ≫
      (dualEvaluationIso X (dualLineBundle X L)).hom =
    (tensorSheafBraiding X L.val (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (tensorSheafLeftUnit X L.val).hom ≫ φ := by
  rw [dualEvaluationIso_hom]
  exact bidualMap_transpose_evaluation X L.val φ

end AlgebraicGeometry.Scheme.Modules.Invertible
