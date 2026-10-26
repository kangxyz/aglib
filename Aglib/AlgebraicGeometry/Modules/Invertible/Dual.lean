/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Evaluation

/-!
# Line-bundle duality and the ordinary Picard group

The dual is the constructed structure-linear Hom sheaf into the structure
sheaf. Evaluation is an actual tensor-sheaf morphism; on rank-one local charts
it is scalar multiplication and therefore becomes an isomorphism.
Evaluation, its inverse and symmetry prove the dual inverse law on
isomorphism classes. This gives the ordinary additive `PicardGroup` of an
arbitrary scheme and actual tensor powers of line bundles.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Picard.Dual`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
The primary namespace is `AlgebraicGeometry.Scheme.Modules.Invertible`;
source names are provenance.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable (X : Scheme.{u})
/-- The structure-linear internal-Hom sheaf from M to the structure-module unit. -/
def dualSheaf (M : SheafOfModules.{u} X.ringCatSheaf) : SheafOfModules.{u} X.ringCatSheaf :=
  InternalHom.sheaf X M (SheafOfModules.unit X.ringCatSheaf)

/-- The local trivialization of the dual induced by the supplied trivialization of M. -/
def dualLocalIso (M : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (dualSheaf X M).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  InternalHom.overHomIso X (M' := SheafOfModules.unit X.ringCatSheaf)
    (N := SheafOfModules.unit X.ringCatSheaf) (N' := SheafOfModules.unit X.ringCatSheaf)
    U e (Iso.refl (SheafOfModules.unit (X.ringCatSheaf.over U))) ≪≫
    (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso
      (InternalHom.unitSourceIso X (SheafOfModules.unit X.ringCatSheaf))

theorem dualSheaf_locallyRankOne (M : SheafOfModules.{u} X.ringCatSheaf)
    (hM : IsLocallyRankOne X M) :
    IsLocallyRankOne X (dualSheaf X M) := by
  rw [isLocallyRankOne_iff_local_unit] at hM ⊢
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM x
  exact ⟨U, hxU, ⟨dualLocalIso X M U e⟩⟩

/-- The dual of an actual line bundle, with its local rank-one property. -/
def dualLineBundle (L : LineBundle X) : LineBundle X :=
  ⟨dualSheaf X L.val, dualSheaf_locallyRankOne X L.val L.property⟩

variable (M N : SheafOfModules.{u} X.ringCatSheaf)
/-- The actual generic presheaf evaluation on the original Zariski site. -/
abbrev evaluationPresheaf :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      (InternalHom.sheaf X M N).val M.val ⟶ N.val :=
  _root_.SheafOfModules.InternalHom.evaluationPresheaf.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N

/-- The actual generic sheaf evaluation on the original sheafified tensor. -/
abbrev evaluationSheaf : tensorSheaf X (InternalHom.sheaf X M N) M ⟶ N :=
  _root_.SheafOfModules.InternalHom.evaluationSheaf.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N

/-- The original presheaf map is the actual generic evaluation on the same objects. -/
theorem evaluationPresheaf_eq_generic :
    evaluationPresheaf X M N =
      _root_.SheafOfModules.InternalHom.evaluationPresheaf.{u, u, u}
        (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N := rfl

/-- The original sheaf map is the actual generic evaluation on the same tensor. -/
theorem evaluationSheaf_eq_generic :
    evaluationSheaf X M N =
      _root_.SheafOfModules.InternalHom.evaluationSheaf.{u, u, u}
        (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N := rfl

/-- The original evaluation formula on pointwise pure tensors. -/
theorem evaluationPresheaf_app_tmul (U : X.Opensᵒᵖ)
    (s : (InternalHom.sheaf X M N).val.obj U) (m : M.val.obj U) :
    (evaluationPresheaf X M N).app U (s ⊗ₜ m) =
      s.val.app (op (Over.mk (𝟙 U.unop))) m :=
  _root_.SheafOfModules.InternalHom.evaluationPresheaf_app_tmul.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N U s m

/-- The original evaluation formula on sheafification-unit generators. -/
theorem evaluationSheaf_tmul (U : X.Opensᵒᵖ)
    (s : (InternalHom.sheaf X M N).val.obj U) (m : M.val.obj U) :
    (evaluationSheaf X M N).val.app U
        ((tensorSheafUnit X (InternalHom.sheaf X M N) M).app U (s ⊗ₜ m)) =
      s.val.app (op (Over.mk (𝟙 U.unop))) m :=
  _root_.SheafOfModules.InternalHom.evaluationSheaf_tmul.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N U s m

/-- The local tensor-presheaf identification of the dual of M tensored with M, using the
supplied trivialization. -/
def dualEvaluationLocalIso (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
        (dualSheaf X M).val M.val) ≅
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val :=
  tensorPresheafOverIso X (dualSheaf X M) M U ≪≫
    CategoryTheory.MonoidalCategory.tensorIso
      (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
      ((SheafOfModules.forget _).mapIso (dualLocalIso X M U e))
      ((SheafOfModules.forget _).mapIso e) ≪≫
    CategoryTheory.MonoidalCategory.leftUnitor
      (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val

theorem dualEvaluationLocalIso_hom (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (dualEvaluationLocalIso X M U e).hom =
      (_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).map
        (evaluationPresheaf X M (SheafOfModules.unit X.ringCatSheaf)) := by
  ext V : 1
  let : CommRing ((X.ringCatSheaf.over U).obj.obj V) := inferInstanceAs (CommRing Γ(X, V.unop.left))
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s m
  let r : Γ(X, V.unop.left) := e.hom.val.app V m
  let v : M.val.obj (op V.unop.left) := e.inv.val.app V (1 : Γ(X, V.unop.left))
  have hgen : r • v = m := by
    have h := (e.inv.val.app V).hom.map_smul r (1 : Γ(X, V.unop.left))
    change e.inv.val.app V (r * (1 : Γ(X, V.unop.left))) = r • v at h
    rw [mul_one] at h
    rw [← h]
    exact congrArg (fun z : M.over U ⟶ M.over U => z.val.app V m) e.hom_inv_id
  change (show Γ(X, V.unop.left) from s.val.app (op (Over.mk (𝟙 V.unop.left))) v) * r =
    (show Γ(X, V.unop.left) from s.val.app (op (Over.mk (𝟙 V.unop.left))) m)
  rw [mul_comm]
  have hs := s.property (op (Over.mk (𝟙 V.unop.left))) r v
  change s.val.app (op (Over.mk (𝟙 V.unop.left))) (r • v) =
    r * (show Γ(X, V.unop.left) from s.val.app (op (Over.mk (𝟙 V.unop.left))) v) at hs
  rw [hgen] at hs
  exact hs.symm

theorem evaluationPresheaf_locallyBijective (L : LineBundle X) :
    _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
        (evaluationPresheaf X L.val (SheafOfModules.unit X.ringCatSheaf)) ∧
      _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
        (evaluationPresheaf X L.val (SheafOfModules.unit X.ringCatSheaf)) := by
  apply locallyBijective_of_local_isIso X
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
  refine ⟨U, hxU, ?_⟩
  rw [← dualEvaluationLocalIso_hom X L.val U e]
  infer_instance

/-- The actual dual evaluation isomorphism from the dual line bundle tensored with the line
bundle to the unit. -/
def dualEvaluationIso (L : LineBundle X) :
    tensorSheaf X (dualLineBundle X L).val L.val ≅ SheafOfModules.unit X.ringCatSheaf :=
  sheafificationMapIsoOfLocallyBijective X
    (evaluationPresheaf X L.val (SheafOfModules.unit X.ringCatSheaf))
    (evaluationPresheaf_locallyBijective X L) ≪≫
      sheafifyForgetIso X (SheafOfModules.unit X.ringCatSheaf)

theorem dualEvaluationIso_hom (L : LineBundle X) :
    (dualEvaluationIso X L).hom = evaluationSheaf X L.val (SheafOfModules.unit X.ringCatSheaf) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
    (dualSheaf X L.val).val L.val.val
  let O := SheafOfModules.unit X.ringCatSheaf
  let adj := _root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have he : adj.homEquiv P O =
      _root_.PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) := by
    apply Equiv.ext
    intro f
    exact _root_.PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
  calc
    (dualEvaluationIso X L).hom =
        (adj.homEquiv P O).symm (evaluationPresheaf X L.val O) :=
      (adj.homEquiv_counit P O (evaluationPresheaf X L.val O)).symm
    _ = evaluationSheaf X L.val O := by rw [he]; rfl

/-- A dual is again an actual line bundle, and evaluation trivializes its tensor with L. -/
theorem dual_tensor_class_eq_zero (L : LineBundle X) :
    tensorClass X (Quotient.mk (lineBundleSetoid X) (dualLineBundle X L))
      (Quotient.mk (lineBundleSetoid X) L) = (0 : LineBundleClass X) := by
  apply Quotient.sound
  exact ⟨dualEvaluationIso X L ≪≫
    (CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩

/-- Inversion is defined by the actual linear dual sheaf. -/
def dualClass (a : LineBundleClass X) : LineBundleClass X :=
  Quotient.liftOn a (fun L => Quotient.mk (lineBundleSetoid X) (dualLineBundle X L)) (by
    intro L M ⟨e⟩
    apply Quotient.sound
    -- The dual isomorphism is obtained globally by precomposition.
    let a : dualSheaf X L.val ⟶ dualSheaf X M.val := {
      val.app U := (InternalHom.overHomMap X ⊤
        ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).map e.inv)
        (𝟙 ((SheafOfModules.unit X.ringCatSheaf).over ⊤))).val.app
          (op (Over.mk (homOfLE le_top : U.unop ⟶ ⊤)))
      val.naturality := by intros; rfl }
    let b : dualSheaf X M.val ⟶ dualSheaf X L.val := {
      val.app U := (InternalHom.overHomMap X ⊤
        ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).map e.hom)
        (𝟙 ((SheafOfModules.unit X.ringCatSheaf).over ⊤))).val.app
          (op (Over.mk (homOfLE le_top : U.unop ⟶ ⊤)))
      val.naturality := by intros; rfl }
    refine ⟨⟨a, b, ?_, ?_⟩⟩
    · apply SheafOfModules.hom_ext
      ext U : 1
      exact congrArg (fun f => f.val.app (op (Over.mk (homOfLE le_top : U.unop ⟶ ⊤))))
        (InternalHom.overHomIso X ⊤ ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e)
          (Iso.refl ((SheafOfModules.unit X.ringCatSheaf).over ⊤))).hom_inv_id
    · apply SheafOfModules.hom_ext
      ext U : 1
      exact congrArg (fun f => f.val.app (op (Over.mk (homOfLE le_top : U.unop ⟶ ⊤))))
        (InternalHom.overHomIso X ⊤ ((SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e)
          (Iso.refl ((SheafOfModules.unit X.ringCatSheaf).over ⊤))).inv_hom_id)

instance lineBundleClassAddCommGroup : AddCommGroup (LineBundleClass X) where
  __ := lineBundleClassAddCommMonoid X
  neg := dualClass X
  neg_add_cancel a := by
    induction a using Quotient.inductionOn with | h L =>
      exact dual_tensor_class_eq_zero X L
  zsmul := @zsmulRec (LineBundleClass X)
    ⟨0⟩ ⟨(· + ·)⟩ ⟨dualClass X⟩ (fun n a => n • a)

/-- The Picard group is the isomorphism classes of actual invertible module sheaves. -/
abbrev PicardGroup := LineBundleClass X

/-- Canonical class of an actual line bundle. -/
def classOf (L : LineBundle X) : PicardGroup X := Quotient.mk (lineBundleSetoid X) L

@[simp] theorem classOf_tensor (L M : LineBundle X) :
    classOf X (tensorLineBundle X L M) = classOf X L + classOf X M := rfl

@[simp] theorem classOf_trivial : classOf X (trivialLineBundle X) = 0 := rfl

@[simp] theorem classOf_dual (L : LineBundle X) :
    classOf X (dualLineBundle X L) = -classOf X L := rfl

/-- The coevaluation, with the conventional L-before-dual ordering. -/
def dualCoevaluation (L : LineBundle X) :
    SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X L.val (dualLineBundle X L).val :=
  (dualEvaluationIso X L).inv ≫ (tensorSheafBraiding X (dualLineBundle X L).val L.val).hom

theorem dualCoevaluation_evaluation (L : LineBundle X) :
    dualCoevaluation X L ≫ (tensorSheafBraiding X (dualLineBundle X L).val L.val).inv ≫
      evaluationSheaf X L.val (SheafOfModules.unit X.ringCatSheaf) = 𝟙 _ := by
  rw [← dualEvaluationIso_hom]
  simp [dualCoevaluation]

/-- Actual tensor powers, including the zero power and level one. -/
def tensorPowerLineBundle (L : LineBundle X) : ℕ → LineBundle X
  | 0 => trivialLineBundle X
  | n + 1 => tensorLineBundle X L (tensorPowerLineBundle L n)

@[simp] theorem classOf_tensorPower (L : LineBundle X) (n : ℕ) :
    classOf X (tensorPowerLineBundle X L n) = n • classOf X L := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change classOf X (tensorLineBundle X L (tensorPowerLineBundle X L n)) = _
    rw [classOf_tensor, ih, succ_nsmul, add_comm]
end AlgebraicGeometry.Scheme.Modules.Invertible
