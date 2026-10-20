/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.AssociatedBundle
public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.UnitPower
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorSum
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.FrameTensor` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`6b14bd43f9ba550a71b7c0b16e1c06300140b778233df53a21bc90f3aab07d44`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle PicardGroup classOf tensorLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap pullbackTensorMap_leftUnit tensorSheafIso tensorSheafLeftUnit tensorSheafMap
    tensorSheafMap_comp)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Tensor frames and the actual additive Picard--Gm H1 comparison

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The frame of L tensor M is literally the canonical tensor-pullback comparison,
followed by the tensor of the two O-linear frames and multiplication O tensor O
into O. Native pullback coherence proves its sheaf naturality, and positive
scalar postcomposition gives multiplication of the two actual global units.
The resulting coefficient-relative torsor map proves Ext additivity through
the actual contracted sum, with no Picard/H1 or additive law as a premise.

The Picard group used here has its already constructed tensor addition and
dual inverse. The associated-bundle equivalence and the precise Stacks03AJ
bijection upgrade the constructed class map to an additive equivalence.
The only retained mathematical inputs are EtaleLineBundleDescent (actual
rank-one module-sheaf descent, Stacks 023T/05B2) and, for bijectivity only,
Stacks03AJ (the constructed torsor/Ext class bijection, Stacks 03AJ).
The Ext realization is explicitly parameterized by HasExt. All statements
apply to arbitrary schemes; there are no curve or characteristic hypotheses.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.FrameTensor
open EtaleDescent FrameTorsor PowerPullback TrivializedPower
open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.GroupCohomology.Kummer.Coefficients
universe u

/-- Literal tensor of actual frames, using the canonical pullback comparison. -/
def tensorFrame {X Y : Scheme.{u}} (p : Y ⟶ X) (L M : LineBundle X)
    (s : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (t : (Scheme.Modules.pullback p).obj M.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback p).obj (tensorLineBundle X L M).val ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  Scheme.Modules.Invertible.PullbackTensor.Local.pullbackLineBundleTensorIso p L M ≪≫
    tensorSheafIso Y s t ≪≫ tensorSheafLeftUnit Y (SheafOfModules.unit Y.ringCatSheaf)

@[simp] theorem tensorFrame_hom {X Y : Scheme.{u}} (p : Y ⟶ X) (L M : LineBundle X)
    (s : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (t : (Scheme.Modules.pullback p).obj M.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (tensorFrame p L M s t).hom = pullbackTensorMap p L.val M.val ≫
      tensorSheafMap Y s.hom t.hom ≫
      (tensorSheafLeftUnit Y (SheafOfModules.unit Y.ringCatSheaf)).hom := rfl

/-- Multiplication of the structure module commutes with actual pullback. -/
theorem unitMultiplication_pullback {Y Z : Scheme.{u}} (f : Z ⟶ Y) :
    pullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) ≫
      tensorSheafMap Z (pullbackUnitIso f).hom (pullbackUnitIso f).hom ≫
      (tensorSheafLeftUnit Z (SheafOfModules.unit Z.ringCatSheaf)).hom =
    (Scheme.Modules.pullback f).map
      (tensorSheafLeftUnit Y (SheafOfModules.unit Y.ringCatSheaf)).hom ≫
      (pullbackUnitIso f).hom := by
  have ht := tensorSheafMap_comp Z (pullbackUnitIso f).hom
    (𝟙 ((Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf)))
    (𝟙 (SheafOfModules.unit Z.ringCatSheaf)) (pullbackUnitIso f).hom
  simp only [Category.comp_id, Category.id_comp] at ht
  rw [← ht, Category.assoc,
      AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.tensorSheafLeftUnit_naturality]
  have hu := congrArg (fun k => k ≫ (pullbackUnitIso f).hom)
    (pullbackTensorMap_leftUnit f (SheafOfModules.unit Y.ringCatSheaf))
  simpa only [Category.assoc] using hu

/-- The native frame pullback, with the actual composite and unit comparisons. -/
def pullFrame {X Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (s : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback q).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr w).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackComp f p).app L.val).symm ≪≫
    (Scheme.Modules.pullback f).mapIso s ≪≫ pullbackUnitIso f

/-- Tensor frames commute with the native composite pullback. -/
theorem tensorFrame_pullback {X Y Z : Scheme.{u}} (L M : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (s : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (t : (Scheme.Modules.pullback p).obj M.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    pullFrame (tensorLineBundle X L M) p q f w (tensorFrame p L M s t) =
      tensorFrame q L M (pullFrame L p q f w s) (pullFrame M p q f w t) := by
  subst q
  apply Iso.ext
  change 𝟙 _ ≫ (Scheme.Modules.pullbackComp f p).inv.app (tensorLineBundle X L M).val ≫
    (Scheme.Modules.pullback f).map (tensorFrame p L M s t).hom ≫ (pullbackUnitIso f).hom =
    pullbackTensorMap (f ≫ p) L.val M.val ≫
      tensorSheafMap Z
        (𝟙 _ ≫ (Scheme.Modules.pullbackComp f p).inv.app L.val ≫
          (Scheme.Modules.pullback f).map s.hom ≫ (pullbackUnitIso f).hom)
        (𝟙 _ ≫ (Scheme.Modules.pullbackComp f p).inv.app M.val ≫
          (Scheme.Modules.pullback f).map t.hom ≫ (pullbackUnitIso f).hom) ≫
      (tensorSheafLeftUnit Z (SheafOfModules.unit Z.ringCatSheaf)).hom
  simp only [Category.id_comp, tensorFrame_hom, Functor.map_comp, Category.assoc]
  rw [← unitMultiplication_pullback f]
  rw [Scheme.Modules.pullbackTensorMap_naturality_assoc f s.hom t.hom]
  have hc := congrArg (fun k => k ≫
    tensorSheafMap Z ((Scheme.Modules.pullback f).map s.hom) ((Scheme.Modules.pullback f).map
        t.hom) ≫
    tensorSheafMap Z (pullbackUnitIso f).hom (pullbackUnitIso f).hom ≫
    (tensorSheafLeftUnit Z (SheafOfModules.unit Z.ringCatSheaf)).hom)
    (pullbackTensorMap_comp f p L.val M.val)
  simp only [Category.assoc] at hc
  refine hc.trans ?_
  simp only [Scheme.Modules.tensorSheafMap_comp_assoc]

/-- Native restriction of a raw frame followed by the actual structure-module comparison. -/
theorem pullHom_frame_hom {X Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (s : (lineBundles.map p.op.toLoc).toFunctor.obj (ofLineBundle X L) ⟶
      (lineBundles.map p.op.toLoc).toFunctor.obj
          (AlgebraicGeometry.Scheme.Modules.Invertible.UnitDescent.unitObject X)) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom s f q q w w).hom ≫ (pullbackUnitIso q).hom =
      (Scheme.Modules.pullbackCongr w).inv.app L.val ≫
        (Scheme.Modules.pullbackComp f p).inv.app L.val ≫
        (Scheme.Modules.pullback f).map (s.hom ≫ (pullbackUnitIso p).hom) ≫ (pullbackUnitIso
            f).hom := by
  subst q
  change ((Scheme.Modules.pullbackComp f p).inv.app L.val ≫
    (Scheme.Modules.pullback f).map s.hom ≫
      (Scheme.Modules.pullbackComp f p).hom.app (SheafOfModules.unit X.ringCatSheaf)) ≫
    (pullbackUnitIso (f ≫ p)).hom = _
  have hu : (Scheme.Modules.pullbackComp f p).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackUnitIso (f ≫ p)).hom =
      (Scheme.Modules.pullback f).map (pullbackUnitIso p).hom ≫ (pullbackUnitIso f).hom := by
    exact Scheme.Modules.pullbackUnitIso_comp f p
  simp only [Category.assoc]
  rw [hu]
  change _ = 𝟙 _ ≫ (Scheme.Modules.pullbackComp f p).inv.app L.val ≫
    (Scheme.Modules.pullback f).map (s.hom ≫ (pullbackUnitIso p).hom) ≫ (pullbackUnitIso f).hom
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]

open EtaleDescent FrameTorsor in
private theorem frameSections_hom (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u})
    (L : LineBundle X) (U : X.Etaleᵒᵖ) (s : (frameSheaf h X L).obj.obj U) :
    (frameSectionsEquiv h X L U s).hom =
      (frameRawHom h X L U s).hom ≫ (pullbackUnitIso U.unop.hom).hom := rfl

open EtaleDescent Opposite Pseudofunctor.LocallyDiscreteOpToCat in
private theorem presheafHom_map_eq_pullHom {S : Scheme.{u}}
    {M N : lineBundles.obj (.mk (op S))} {U V : S.Etale} (f : V ⟶ U)
    (g : (lineBundles.map U.hom.op.toLoc).toFunctor.obj M ⟶
      (lineBundles.map U.hom.op.toLoc).toFunctor.obj N) :
    (lineBundles.presheafHom M N).map ((Scheme.Etale.forget S).map f).op g =
      pullHom g f.left V.hom V.hom
        (MorphismProperty.Over.w f) (MorphismProperty.Over.w f) := rfl

/-- The existing frame sheaf restriction is exactly the native frame pullback. -/
theorem frameSections_restriction (h : EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) (L : LineBundle X) {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s : (frameSheaf h X L).obj.obj U) :
    frameSectionsEquiv h X L V ((frameSheaf h X L).obj.map f s) =
      pullFrame L U.unop.hom V.unop.hom f.unop.left f.unop.w (frameSectionsEquiv h X L U s) := by
  apply Iso.ext
  simp only [pullFrame, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, frameSections_hom]
  rw [frameRawHom_naturality, presheafHom_map_eq_pullHom]
  exact pullHom_frame_hom L U.unop.hom V.unop.hom f.unop.left f.unop.w
    (frameRawHom h X L U s)

/-- Positive scalar postcomposition on tensor frames multiplies actual global units. -/
theorem tensorFrame_scalar {X Y : Scheme.{u}} (p : Y ⟶ X) (L M : LineBundle X)
    (s : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (t : (Scheme.Modules.pullback p).obj M.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (a b : Γ(Y, ⊤)ˣ) :
    tensorFrame p L M
      (s ≪≫ AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso Y
          (SheafOfModules.unit Y.ringCatSheaf) a)
      (t ≪≫ AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso Y
          (SheafOfModules.unit Y.ringCatSheaf) b) =
    tensorFrame p L M s t ≪≫
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso Y
          (SheafOfModules.unit Y.ringCatSheaf) (a * b) := by
  apply Iso.ext
  change pullbackTensorMap p L.val M.val ≫
    tensorSheafMap Y (s.hom ≫ scalarMap Y _ a) (t.hom ≫ scalarMap Y _ b) ≫
      (tensorSheafLeftUnit Y (SheafOfModules.unit Y.ringCatSheaf)).hom =
    (pullbackTensorMap p L.val M.val ≫ tensorSheafMap Y s.hom t.hom ≫
      (tensorSheafLeftUnit Y (SheafOfModules.unit Y.ringCatSheaf)).hom) ≫ scalarMap Y _ (a * b
          : Γ(Y, ⊤)ˣ)
  rw [← tensorSheafMap_comp,
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.tensorSheafMap_scalar]
  simp only [Category.assoc]
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarMap_naturality]
  rfl

variable (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (L M : LineBundle X)

/-- Tensor product on the actual sections of the frame sheaves. -/
def tensorSection (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) (t : (frameSheaf h X M).obj.obj U) :
    (frameSheaf h X (tensorLineBundle X L M)).obj.obj U :=
  (frameSectionsEquiv h X (tensorLineBundle X L M) U).symm
    (tensorFrame U.unop.hom L M (frameSectionsEquiv h X L U s) (frameSectionsEquiv h X M U t))

@[simp] theorem tensorSection_sections (U : X.Etaleᵒᵖ)
    (s : (frameSheaf h X L).obj.obj U) (t : (frameSheaf h X M).obj.obj U) :
    frameSectionsEquiv h X (tensorLineBundle X L M) U (tensorSection h X L M U s t) =
      tensorFrame U.unop.hom L M (frameSectionsEquiv h X L U s) (frameSectionsEquiv h X M U t) :=
  (frameSectionsEquiv h X (tensorLineBundle X L M) U).apply_symm_apply _

/-- Sheaf naturality follows from the proved canonical tensor/unit pullback coherences. -/
theorem tensorSection_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s : (frameSheaf h X L).obj.obj U) (t : (frameSheaf h X M).obj.obj U) :
    (frameSheaf h X (tensorLineBundle X L M)).obj.map f (tensorSection h X L M U s t) =
      tensorSection h X L M V ((frameSheaf h X L).obj.map f s) ((frameSheaf h X M).obj.map f t)
          := by
  apply (frameSectionsEquiv h X (tensorLineBundle X L M) V).injective
  rw [frameSections_restriction, tensorSection_sections, tensorSection_sections,
    frameSections_restriction, frameSections_restriction]
  exact tensorFrame_pullback L M U.unop.hom V.unop.hom f.unop.left f.unop.w _ _

/-- The coefficient-relative law is positive multiplication, equivalently addition in Gm. -/
theorem tensorSection_equivariant (U : X.Etaleᵒᵖ) (a b : (gm X).obj.obj U)
    (s : (frameSheaf h X L).obj.obj U) (t : (frameSheaf h X M).obj.obj U) :
    tensorSection h X L M U (frameAction h X L U a s) (frameAction h X M U b t) =
      frameAction h X (tensorLineBundle X L M) U (a + b) (tensorSection h X L M U s t) := by
  apply (frameSectionsEquiv h X (tensorLineBundle X L M) U).injective
  rw [tensorSection_sections, frameAction_sections, frameAction_sections,
    frameAction_sections, tensorSection_sections, map_add]
  exact tensorFrame_scalar U.unop.hom L M _ _ _ _

/-- The genuine tensor morphism of frame sheaves, relative to coefficient addition. -/
def tensorTorsorHom :
    Scheme.EtaleH1.Torsor.Hom (torsorCoefficientAdd (gm X))
      (torsorProduct (frameTorsor h X L) (frameTorsor h X M))
      (frameTorsor h X (tensorLineBundle X L M)) where
  map := ⟨{ app U := ↾(fun s => tensorSection h X L M U s.1 s.2)
            naturality {U V} f := by
              ext s
              exact (tensorSection_naturality h X L M f s.1 s.2).symm }⟩
  equivariant U a s := tensorSection_equivariant h X L M U a.1 a.2 s.1 s.2

section ExtClass
universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The literal tensor construction has the sum of the two canonical Ext classes.
No torsor/H1 classification premise is used. -/
theorem torsorExtClass_tensor :
    torsorExtClass (frameTorsor h X (tensorLineBundle X L M)) =
      torsorExtClass (frameTorsor h X L) + torsorExtClass (frameTorsor h X M) := by
  calc
    _ = coefficientMap (torsorCoefficientAdd (gm X))
        (torsorExtClass (torsorProduct (frameTorsor h X L) (frameTorsor h X M))) :=
      (torsorExtClass_naturality (tensorTorsorHom h X L M)).symm
    _ = torsorExtClass (torsorSum (frameTorsor h X L) (frameTorsor h X M)) :=
      (torsorExtClass_pushout _ _).symm
    _ = _ := torsorExtClass_sum _ _

/-- The canonical frame Ext class on the actual tensor/dual Picard quotient. -/
def classMap : PicardGroup X → H1Etale X (gm X) :=
  fun c => torsorClassToH1 (gm X)
      (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.bundleClassToTorsor h c)

@[simp] theorem classMap_classOf (L : LineBundle X) :
    classMap h X (classOf X L) = torsorExtClass (frameTorsor h X L) := rfl

/-- Additivity uses the actual quotient tensor law and the actual frame tensor morphism. -/
theorem classMap_add (a b : PicardGroup X) :
    classMap h X (a + b) = classMap h X a + classMap h X b := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun L M => torsorExtClass_tensor h X L M

@[simp] theorem classMap_zero : classMap h X 0 = 0 := by
  have hz : classMap h X 0 = classMap h X 0 + classMap h X 0 := by
    simpa only [zero_add] using classMap_add h X 0 0
  exact add_left_cancel (show classMap h X 0 + classMap h X 0 = classMap h X 0 + 0 by
    simpa only [add_zero] using hz.symm)

/-- The genuine Picard-to-H1 homomorphism, before assuming classification. -/
def toH1 : PicardGroup X →+ H1Etale X (gm X) where
  toFun := classMap h X
  map_zero' := classMap_zero h X
  map_add' := classMap_add h X

@[simp] theorem toH1_classOf (L : LineBundle X) :
    toH1 h X (classOf X L) = torsorExtClass (frameTorsor h X L) := rfl

/-- Bijectivity is the composition of the actual associated-bundle equivalence
and A's precisely parameterized torsor/Ext class equivalence. -/
theorem toH1_bijective (hAJ : Stacks03AJ.{u, w} X) : Function.Bijective (toH1 h X) :=
  (torsorClassEquiv hAJ (gm X)).bijective.comp
      (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.classEquiv h).bijective

/-- The actual additive Picard--Gm H1 equivalence. Only bijectivity uses
Stacks03AJ, and the group on Picard remains its fixed tensor/dual group. -/
def picardH1Equiv (hAJ : Stacks03AJ.{u, w} X) : PicardGroup X ≃+ H1Etale X (gm X) :=
  AddEquiv.ofBijective (toH1 h X) (toH1_bijective h X hAJ)

@[simp] theorem picardH1Equiv_classOf (hAJ : Stacks03AJ.{u, w} X) (L : LineBundle X) :
    picardH1Equiv h X hAJ (classOf X L) = torsorExtClass (frameTorsor h X L) := rfl

@[simp] theorem picardH1Equiv_apply (hAJ : Stacks03AJ.{u, w} X) (c : PicardGroup X) :
    picardH1Equiv h X hAJ c = classMap h X c := rfl

theorem picardH1Equiv_toAddMonoidHom (hAJ : Stacks03AJ.{u, w} X) :
    (picardH1Equiv h X hAJ).toAddMonoidHom = toH1 h X := rfl

theorem toH1_injective (hAJ : Stacks03AJ.{u, w} X) : Function.Injective (toH1 h X) :=
  (toH1_bijective h X hAJ).injective

end ExtClass

end AlgebraicGeometry.Scheme.Modules.Invertible.FrameTensor
