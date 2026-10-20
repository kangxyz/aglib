/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitInverse

public import Aglib.AlgebraicGeometry.Modules.Invertible.Power.UnitPower
public import Aglib.AlgebraicGeometry.Picard.FrameTorsor
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.PowerFiber
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.TrivializedPowerTorsor` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1d6a3ad7517e9dff89a399412fbb1702ed3c697023a049ebffea421cb99e695f`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle pullbackLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual positive power-compatible frame torsors

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

For an actual pair (L, tau), the frame sheaf consists of actual O-linear
isomorphisms L -> O. Its power value is the literal unit of the composite
tau^-1 followed by the nth tensor power of the frame and canonical O-power
multiplication. Actual scalar postcomposition multiplies this value by a^n.
The value is proved natural for the native pullback comparisons, including
arbitrary specified commuting structural squares, so it defines an actual
small-etale sheaf morphism to Gm. The generic PowerFiber construction then
supplies the genuine mu_n torsor at positive globally invertible n.

Its sections are proved to be exactly frames phi with phi^n = tau after
canonical unit normalization. The mu_n action is positive scalar
postcomposition. For a unit-pair trivialization multiplication by f, this
is the positive a^n=f convention; the specific root-torsor isomorphism is
constructed in PowerRoot. Normalized sections instead satisfy f*s^n=1
and require inversion. No sign identification is assumed here.

Only the existing precise all-rank-one EtaleLineBundleDescent is retained
to obtain the actual frame sheaf. Local nth roots use the proved generic
power-map epimorphism, not a retained03PL premise. No pair classification,
H1 comparison, generic divisor identity or target-shaped premise is input.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPowerTorsor
open TrivializedPower UnitPower PowerPullback
universe u

/-- The literal unit attached to a composite O-automorphism is the product. -/
theorem unitOfIso_trans (X : Scheme.{u})
    (e d : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    unitOfIso X (e ≪≫ d) = unitOfIso X e * unitOfIso X d := by
  apply Units.ext
  let x : Γ(X, ⊤) := e.hom.val.app (Opposite.op ⊤) (1 : Γ(X, ⊤))
  let y : Γ(X, ⊤) := d.hom.val.app (Opposite.op ⊤) (1 : Γ(X, ⊤))
  change d.hom.val.app (Opposite.op ⊤) x = x * y
  let ψ : Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) := (d.hom.val.app (Opposite.op ⊤)).hom
  have h := ψ.map_smul x (1 : Γ(X, ⊤))
  change ψ (x * 1) = x * y at h
  change ψ x = x * y
  simpa only [mul_one] using h

/-- An automorphism's actual unit pulls back by the actual ring homomorphism. -/
theorem unitOfIso_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    unitOfIso X ((pullbackUnitIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫
      pullbackUnitIso f) = Units.map f.appTop.hom.toMonoidHom (unitOfIso Y e) := by
  apply (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
      X).symm.injective
  change AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _
      (unitOfIso X _) =
    AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _ (Units.map
        f.appTop.hom.toMonoidHom (unitOfIso Y e))
  have hleft := (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
      X).left_inv
    ((pullbackUnitIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f)
  change AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _
      (unitOfIso X _) = _ at hleft
  rw [hleft]
  apply Iso.ext
  change (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map e.hom ≫
    (pullbackUnitIso f).hom = _
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitOfIso_hom Y e,
    AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.pullback_scalar_unit,
        Iso.inv_hom_id_assoc]
  rfl

/-- The positive power value of an actual frame relative to the chosen trivialization. -/
def powerValue (X : Scheme.{u}) {n : ℕ} (P : Pair X n)
    (φ : P.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf) : Γ(X, ⊤)ˣ :=
  unitOfIso X (P.trivialization.symm ≪≫
    powerIso X (M := unitLineBundle X) φ n ≪≫ unitPowerIso X n)

/-- The frame condition is literally φ^n=τ under canonical O-power multiplication. -/
theorem powerValue_eq_one_iff (X : Scheme.{u}) {n : ℕ} (P : Pair X n)
    (φ : P.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    powerValue X P φ = 1 ↔
      (powerIso X (M := unitLineBundle X) φ n).hom ≫ (unitPowerIso X n).hom =
        P.trivialization.hom := by
  constructor
  · intro h
    have he := congrArg (fun a =>
        (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X
      (SheafOfModules.unit X.ringCatSheaf) a).hom) h
    have hvalue := AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitOfIso_hom X
      (P.trivialization.symm ≪≫ powerIso X (M := unitLineBundle X) φ n ≪≫ unitPowerIso X n)
    change _ = scalarMap X _ (powerValue X P φ) at hvalue
    change scalarMap X _ (powerValue X P φ) = scalarMap X _ 1 at he
    rw [AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarMap_one] at he
    have ht : P.trivialization.inv ≫
        (powerIso X (M := unitLineBundle X) φ n).hom ≫ (unitPowerIso X n).hom = 𝟙 _ :=
      hvalue.trans he
    exact (P.trivialization.inv_comp_eq).mp ht |>.trans (Category.comp_id _)
  · intro h
    unfold powerValue
    have he : P.trivialization.symm ≪≫ powerIso X (M := unitLineBundle X) φ n ≪≫ unitPowerIso X n =
        Iso.refl _ := by
      apply Iso.ext
      change P.trivialization.inv ≫
        (powerIso X (M := unitLineBundle X) φ n).hom ≫ (unitPowerIso X n).hom = 𝟙 _
      rw [h, Iso.inv_hom_id]
    rw [he]
    apply Units.ext
    rfl

/-- Positive scalar postcomposition acts on the frame value by the nth power. -/
theorem powerValue_scalar (X : Scheme.{u}) {n : ℕ} (P : Pair X n)
    (φ : P.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf) (a : Γ(X, ⊤)ˣ) :
    powerValue X P (φ ≪≫
        AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _ a) =
      powerValue X P φ * a ^ n := by
  unfold powerValue
  have hpow := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_trans X (M :=
      unitLineBundle X) (N := unitLineBundle X)
    φ (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _ a) n
  erw [hpow]
  have he : P.trivialization.symm ≪≫
      (powerIso X (M := unitLineBundle X) φ n ≪≫
        powerIso X (L := unitLineBundle X) (M := unitLineBundle X)
          (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _ a) n)
              ≪≫ unitPowerIso X n =
    (P.trivialization.symm ≪≫ powerIso X (M := unitLineBundle X) φ n ≪≫ unitPowerIso X n) ≪≫
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _ (a ^ n) := by
    apply Iso.ext
    simp only [Iso.trans_hom, Category.assoc]
    erw [unitPowerIso_scalar X a n]
    rfl
  rw [he, unitOfIso_trans]
  exact congrArg (fun b => _ * b)
      ((AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
      X).right_inv (a ^ n))

/-- Pulling an actual framed pair back pulls its positive power value back literally. -/
theorem powerValue_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ} (P : Pair Y n)
    (φ : P.lineBundle.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    powerValue X (pullbackPair f P) ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f) =
      Units.map f.appTop.hom.toMonoidHom (powerValue Y P φ) := by
  unfold powerValue
  have hp := AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_trans X
    (L := pullbackLineBundle f P.lineBundle) (M := pullbackLineBundle f (unitLineBundle Y))
    (N := unitLineBundle X) ((Scheme.Modules.pullback f).mapIso φ) (pullbackUnitIso f) n
  rw [hp]
  have he : (pullbackPair f P).trivialization.symm ≪≫
      (powerIso X (M := pullbackLineBundle f (unitLineBundle Y))
        ((Scheme.Modules.pullback f).mapIso φ) n ≪≫
      powerIso X (L := pullbackLineBundle f (unitLineBundle Y)) (M := unitLineBundle X)
        (pullbackUnitIso f) n) ≪≫ unitPowerIso X n =
    (pullbackUnitIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso
      (P.trivialization.symm ≪≫ powerIso Y (M := unitLineBundle Y) φ n ≪≫ unitPowerIso Y n) ≪≫
      pullbackUnitIso f := by
    apply Iso.ext
    change ((pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map P.trivialization.inv ≫
      (pullbackPowerIso f P.lineBundle n).hom) ≫
      ((powerIso X (M := pullbackLineBundle f (unitLineBundle Y))
        ((Scheme.Modules.pullback f).mapIso φ) n).hom ≫
      (powerIso X (L := pullbackLineBundle f (unitLineBundle Y)) (M := unitLineBundle X)
        (pullbackUnitIso f) n).hom) ≫ (unitPowerIso X n).hom = _
    have hn := congrArg Iso.hom
        (PowerPullbackNaturality.pullbackPowerIso_naturality f
      (M := unitLineBundle Y) φ n)
    change (Scheme.Modules.pullback f).map (powerIso Y (M := unitLineBundle Y) φ n).hom ≫
      (pullbackPowerIso f (unitLineBundle Y) n).hom =
      (pullbackPowerIso f P.lineBundle n).hom ≫
        (powerIso X (M := pullbackLineBundle f (unitLineBundle Y))
          ((Scheme.Modules.pullback f).mapIso φ) n).hom at hn
    have hn' := congrArg (fun v => v ≫
      (powerIso X (L := pullbackLineBundle f (unitLineBundle Y)) (M := unitLineBundle X)
        (pullbackUnitIso f) n).hom ≫ (unitPowerIso X n).hom) hn
    simp only [Category.assoc] at hn' ⊢
    rw [← hn', unitPowerIso_pullback]
    simp only [CategoryTheory.Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
      CategoryTheory.Functor.map_comp, Category.assoc]
  rw [he]
  exact unitOfIso_pullback f _

/-- Actual pair isomorphisms preserve the power value of the transported frame. -/
theorem powerValue_pairIso (X : Scheme.{u}) {n : ℕ} (P Q : Pair X n)
    (e : P.lineBundle.val ≅ Q.lineBundle.val)
    (he : (powerIso X e n).hom ≫ Q.trivialization.hom = P.trivialization.hom)
    (φ : Q.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    powerValue X P (e ≪≫ φ) = powerValue X Q φ := by
  unfold powerValue
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_trans X (N :=
      unitLineBundle X)]
  have hc : P.trivialization.inv ≫ (powerIso X e n).hom = Q.trivialization.inv := by
    apply P.trivialization.inv_comp_eq.mpr
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  congr 1
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hc, Category.assoc]


open EtaleDescent in
/-- Native restriction of a raw frame, followed by the actual O comparison. -/
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
  simp only [Category.id_comp, CategoryTheory.Functor.map_comp, Category.assoc]

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

/-- Restriction of literal frames uses the native composite and unit comparisons. -/
theorem frameSections_restriction (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) (L : LineBundle X) {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s : (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSheaf h X L).obj.obj U) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X L V
        ((AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSheaf h X L).obj.map f
        s)).hom =
      (Scheme.Modules.pullbackCongr f.unop.w).inv.app L.val ≫
      (Scheme.Modules.pullbackComp f.unop.left U.unop.hom).inv.app L.val ≫
      (Scheme.Modules.pullback f.unop.left).map
          (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X L U
          s).hom ≫
      (pullbackUnitIso f.unop.left).hom := by
  simp only [frameSections_hom]
  rw [FrameTorsor.frameRawHom_naturality, presheafHom_map_eq_pullHom]
  exact pullHom_frame_hom L U.unop.hom V.unop.hom f.unop.left f.unop.w
    (FrameTorsor.frameRawHom h X L U s)

/-- The actual native composite pair isomorphism, with its exact compatibility equation. -/
theorem pullbackPair_comp_compatibility {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {n : ℕ} (P : Pair Z n) :
    (powerIso X (L := (pullbackPair (f ≫ g) P).lineBundle)
      (M := (pullbackPair f (pullbackPair g P)).lineBundle)
      ((Scheme.Modules.pullbackComp f g).app P.lineBundle.val).symm n).hom ≫
        (pullbackPair f (pullbackPair g P)).trivialization.hom =
      (pullbackPair (f ≫ g) P).trivialization.hom := by
  change (powerIso X ((Scheme.Modules.pullbackComp f g).app P.lineBundle.val).symm n).hom ≫
      ((pullbackPowerIso f (pullbackLineBundle g P.lineBundle) n).inv ≫
        (Scheme.Modules.pullback f).map
          ((pullbackPowerIso g P.lineBundle n).inv ≫
            (Scheme.Modules.pullback g).map P.trivialization.hom ≫ (pullbackUnitIso g).hom) ≫
        (pullbackUnitIso f).hom) =
    (pullbackPowerIso (f ≫ g) P.lineBundle n).inv ≫
      ((Scheme.Modules.pullback (f ≫ g)).map P.trivialization.hom ≫ (pullbackUnitIso (f ≫ g)).hom)
  apply (pullbackPowerIso (f ≫ g) P.lineBundle n).eq_inv_comp.mpr
  rw [← Category.assoc, ←
      AlgebraicGeometry.Scheme.Modules.Invertible.PowerPullbackNaturality.pullbackPowerIso_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, CategoryTheory.Functor.map_comp]
  have hcancel := Iso.hom_inv_id_assoc ((Scheme.Modules.pullback f).mapIso
    (pullbackPowerIso g P.lineBundle n))
    ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map P.trivialization.hom) ≫
      (Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫ (pullbackUnitIso f).hom)
  erw [hcancel]
  erw [← (Scheme.Modules.pullbackComp f g).inv.naturality_assoc P.trivialization.hom]
  rw [Scheme.Modules.pullbackUnitIso_comp_inv]

/-- Literal restriction of the positive power value under native composition. -/
theorem powerValue_compRestriction {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {n : ℕ} (P : Pair Z n)
    (φ : (pullbackPair g P).lineBundle.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    powerValue X (pullbackPair (f ≫ g) P)
      (((Scheme.Modules.pullbackComp f g).app P.lineBundle.val).symm ≪≫
        ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f)) =
      Units.map f.appTop.hom.toMonoidHom (powerValue Y (pullbackPair g P) φ) := by
  rw [powerValue_pairIso X (pullbackPair (f ≫ g) P) (pullbackPair f (pullbackPair g P))
    ((Scheme.Modules.pullbackComp f g).app P.lineBundle.val).symm
      (pullbackPair_comp_compatibility f g P)]
  exact powerValue_pullback f (pullbackPair g P) φ

/-- Native frame restriction along any specified commuting structural square. -/
def nativePullFrame {X Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback q).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr w).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackComp f p).app L.val).symm ≪≫
      ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f)

theorem powerValue_nativePullFrame {X Y Z : Scheme.{u}}
    (p : Y ⟶ X) (q : Z ⟶ X) (f : Z ⟶ Y) (w : f ≫ p = q)
    {n : ℕ} (P : Pair X n)
    (φ : (Scheme.Modules.pullback p).obj P.lineBundle.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    powerValue Z (pullbackPair q P) (nativePullFrame P.lineBundle p q f w φ) =
      Units.map f.appTop.hom.toMonoidHom (powerValue Y (pullbackPair p P) φ) := by
  subst q
  unfold nativePullFrame
  change powerValue Z (pullbackPair (f ≫ p) P)
    (Iso.refl _ ≪≫ (((Scheme.Modules.pullbackComp f p).app P.lineBundle.val).symm ≪≫
      ((Scheme.Modules.pullback f).mapIso φ ≪≫ pullbackUnitIso f))) = _
  rw [Iso.refl_trans]
  exact powerValue_compRestriction f p P φ

/-- The power value on actual frame sections is literally natural under restriction. -/
theorem framePowerValue_naturality (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) {n : ℕ} (P : Pair X n) {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s : (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSheaf h X
        P.lineBundle).obj.obj U) :
    powerValue V.unop.left (pullbackPair V.unop.hom P)
      (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X P.lineBundle V
        ((AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSheaf h X
            P.lineBundle).obj.map f s)) =
      Units.map f.unop.left.appTop.hom.toMonoidHom
        (powerValue U.unop.left (pullbackPair U.unop.hom P)
          (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
              P.lineBundle U s)) := by
  have he : AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
      P.lineBundle V
      ((AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSheaf h X
          P.lineBundle).obj.map f s) =
      nativePullFrame P.lineBundle U.unop.hom V.unop.hom f.unop.left f.unop.w
        (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
            P.lineBundle U s) := by
    apply Iso.ext
    exact frameSections_restriction h X P.lineBundle f s
  rw [he]
  exact powerValue_nativePullFrame U.unop.hom V.unop.hom f.unop.left f.unop.w P _

open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.GroupCohomology.Kummer.Coefficients

def framePowerSection (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    {n : ℕ} (P : Pair X n) (U : X.Etaleᵒᵖ)
    (s : (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSheaf h X
        P.lineBundle).obj.obj U) : (gm X).obj.obj U :=
  (unitsSections X U).symm (Additive.ofMul
    (powerValue U.unop.left (pullbackPair U.unop.hom P)
      (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
          P.lineBundle U s)))

@[simp] theorem framePowerSection_units (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) {n : ℕ} (P : Pair X n) (U : X.Etaleᵒᵖ)
    (s : (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSheaf h X
        P.lineBundle).obj.obj U) :
    (unitsSections X U (framePowerSection h X P U s)).toMul =
      powerValue U.unop.left (pullbackPair U.unop.hom P)
        (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
            P.lineBundle U s) :=
  congrArg Additive.toMul ((unitsSections X U).apply_symm_apply _)

/-- The actual frame-power value is a morphism of small-etale sheaves. -/
def framePowerMap (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    {n : ℕ} (P : Pair X n) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameTorsor h X
        P.lineBundle).carrier ⟶ underlyingSetSheaf (gm X) where
  hom := {
    app U := ↾(framePowerSection h X P U)
    naturality := by
      intro U V f
      ext s
      apply (unitsSections X V).injective
      apply Additive.toMul.injective
      change (unitsSections X V (framePowerSection h X P V
        ((AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSheaf h X
            P.lineBundle).obj.map f s))).toMul =
        (unitsSections X V ((gm X).obj.map f (framePowerSection h X P U s))).toMul
      rw [framePowerSection_units, unitsSections_naturality, framePowerSection_units]
      exact framePowerValue_naturality h X P f s }

theorem framePowerMap_equivariance (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) {n : ℕ} (P : Pair X n) (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U)
    (s : (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameTorsor h X
        P.lineBundle).carrier.obj.obj U) :
    GroupCohomology.Kummer.PowerFiber.value
        (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameTorsor h X P.lineBundle)
        (framePowerMap h X P) U
      ((AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameTorsor h X
          P.lineBundle).action U a s) =
    (power X n).hom.app U a +
      GroupCohomology.Kummer.PowerFiber.value
          (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameTorsor h X
          P.lineBundle) (framePowerMap h X P) U s := by
  apply (unitsSections X U).injective
  apply Additive.toMul.injective
  change (unitsSections X U (framePowerSection h X P U
      (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameAction h X P.lineBundle U a
      s))).toMul = _
  rw [framePowerSection_units, map_add]
  change powerValue U.unop.left (pullbackPair U.unop.hom P)
      (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
          P.lineBundle U (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameAction h
          X P.lineBundle U a s)) =
    (unitsSections X U ((power X n).hom.app U a)).toMul *
      (unitsSections X U (framePowerSection h X P U s)).toMul
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameAction_sections,
      powerValue_scalar, power_apply, framePowerSection_units, mul_comm]

/-- The genuine mu_n torsor of positive power-compatible O-linear frames. -/
def torsor (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n) : Torsor (mu X n) :=
  GroupCohomology.Kummer.PowerFiber.powerFiberTorsor n
      (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameTorsor h X P.lineBundle)
    (framePowerMap h X P) (framePowerMap_equivariance h X P) hn hinv

theorem framePowerSection_eq_zero_iff (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u})
    (X : Scheme.{u}) {n : ℕ} (P : Pair X n) (U : X.Etaleᵒᵖ)
    (s : (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSheaf h X
        P.lineBundle).obj.obj U) :
    framePowerSection h X P U s = 0 ↔
      (powerIso U.unop.left (M := unitLineBundle U.unop.left)
        (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
            P.lineBundle U s) n).hom ≫
        (unitPowerIso U.unop.left n).hom = (pullbackPair U.unop.hom P).trivialization.hom := by
  refine Iff.trans ?_ (powerValue_eq_one_iff U.unop.left (pullbackPair U.unop.hom P)
    (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
        P.lineBundle U s))
  constructor
  · intro hs
    have he := congrArg (fun a => (unitsSections X U a).toMul) hs
    rw [framePowerSection_units, map_zero] at he
    exact he
  · intro hs
    apply (unitsSections X U).injective
    apply Additive.toMul.injective
    rw [framePowerSection_units, map_zero, hs]
    rfl


/-- A positive power-compatible frame is an actual O-linear isomorphism
whose normalized nth tensor power is the specified trivialization. -/
def CompatibleFrame (X : Scheme.{u}) {n : ℕ} (P : Pair X n) :=
  {φ : P.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf //
    (powerIso X (M := unitLineBundle X) φ n).hom ≫ (unitPowerIso X n).hom =
      P.trivialization.hom}

/-- Sections of the constructed torsor are exactly the literal compatible frames. -/
def sectionsEquiv (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n)
    (U : X.Etaleᵒᵖ) :
    (torsor h X n hn hinv P).carrier.obj.obj U ≃
      CompatibleFrame U.unop.left (pullbackPair U.unop.hom P) where
  toFun s := ⟨FrameTorsor.frameSectionsEquiv h X P.lineBundle U s.val,
    (framePowerSection_eq_zero_iff h X P U s.val).mp s.property⟩
  invFun φ := ⟨(AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
      P.lineBundle U).symm φ.val, by
    apply (framePowerSection_eq_zero_iff h X P U _).mpr
    rw [Equiv.apply_symm_apply]
    exact φ.property⟩
  left_inv s := by
    apply Subtype.ext
    exact (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
        P.lineBundle U).symm_apply_apply _
  right_inv φ := by
    apply Subtype.ext
    exact (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
        P.lineBundle U).apply_symm_apply _

/-- The genuine root action is positive scalar postcomposition on frames. -/
theorem sectionsEquiv_action (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n)
    (U : X.Etaleᵒᵖ) (ζ : (mu X n).obj.obj U)
    (s : (torsor h X n hn hinv P).carrier.obj.obj U) :
    (sectionsEquiv h X n hn hinv P U ((torsor h X n hn hinv P).action U ζ s)).val =
      (sectionsEquiv h X n hn hinv P U s).val ≪≫
        AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso U.unop.left _
          ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ) := by
  change AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameSectionsEquiv h X
      P.lineBundle U
    (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameAction h X P.lineBundle U
        ((inclusion X n).hom.app U ζ) s.val) = _
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.FrameTorsor.frameAction_sections, inclusion_apply]
  rfl

/-- Actual section restriction is the native pullback of its O-linear frame. -/
theorem sectionsEquiv_naturality (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n)
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V)
    (s : (torsor h X n hn hinv P).carrier.obj.obj U) :
    (sectionsEquiv h X n hn hinv P V ((torsor h X n hn hinv P).carrier.obj.map f s)).val =
      nativePullFrame P.lineBundle U.unop.hom V.unop.hom f.unop.left f.unop.w
        (sectionsEquiv h X n hn hinv P U s).val := by
  apply Iso.ext
  exact frameSections_restriction h X P.lineBundle f s.val

end AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPowerTorsor
