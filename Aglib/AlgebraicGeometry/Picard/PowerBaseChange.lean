/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.TrivializedPowerTorsor
public import Aglib.AlgebraicGeometry.Picard.AssociatedBundle
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.CoefficientBaseChange
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.PowerBaseChange` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`920a03fd89441aec26aed514172a08cafac04a0d6ffd5895c9e75c573c260093`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle pullbackLineBundle )
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
# Actual base change of compatible-frame torsors

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`, C4/C5.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Lean 4.34.1; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

For an arbitrary actual scheme morphism and an actual power-trivialized line
bundle, native module pullback sends each positive compatible frame to the
specified pulled pair. Literal unit and power coherence proves compatibility,
restriction and equivariance. The arbitrary-pseudofunctor Hom-presheaf lemma
isolates the native restriction/over-base-change coherence before specialization.

These actual sections define an ordinary adjoint torsor morphism for the
literal roots coefficient unit. A's proved Ext adjunction theorem then yields
the actual H1 pullback equation. The finite-etale represented mu_n inverse-image
isomorphism is exactly CoefficientBaseChange.rootsPullbackIso. No arbitrary-base
Gm inverse-image isomorphism is asserted or used.

The sole retained mathematical family is the fixed general rank-one etale
stack theorem needed for frame sheaves. Positive n and its actual global
invertibility are explicit, as are source and target Ext sizes. The local-root
03PL boundary is discharged by actual root covers. No torsor classification,
Picard/H1 equation, field/root representative formula or desired naturality
square is assumed. This file imports no K-theory.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite Bicategory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PowerBaseChange
open EtaleDescent UnitDescent TrivializedPower UnitPower PowerPullback TrivializedPowerTorsor
open Pseudofunctor.LocallyDiscreteOpToCat
open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.GroupCohomology.Kummer.Coefficients
universe u

/-- The literal frame as a morphism in the native full rank-one subcategory. -/
def rawOfFrame {X Y : Scheme.{u}} (L : LineBundle X) (p : Y ⟶ X)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (lineBundles.map p.op.toLoc).toFunctor.obj (ofLineBundle X L) ⟶
      (lineBundles.map p.op.toLoc).toFunctor.obj (unitObject X) :=
  ObjectProperty.homMk (φ.hom ≫ (pullbackUnitIso p).inv)

theorem rawOfFrame_injective {X Y : Scheme.{u}} (L : LineBundle X) (p : Y ⟶ X) :
    Function.Injective (rawOfFrame L p) := by
  intro φ ψ h
  apply Iso.ext
  apply (cancel_mono (pullbackUnitIso p).inv).mp
  exact congrArg (fun α => α.hom) h

/-- Native frame restriction is exactly native pullHom on the actual raw morphism. -/
theorem rawOfFrame_nativePullFrame {X Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (g : Z ⟶ Y) (w : g ≫ p = q)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    rawOfFrame L q (nativePullFrame L p q g w φ) =
      pullHom (rawOfFrame L p φ) g q q w w := by
  apply ObjectProperty.hom_ext
  apply (cancel_mono (pullbackUnitIso q).hom).mp
  change ((nativePullFrame L p q g w φ).hom ≫ (pullbackUnitIso q).inv) ≫
    (pullbackUnitIso q).hom = (pullHom (rawOfFrame L p φ) g q q w w).hom ≫
      (pullbackUnitIso q).hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    pullHom_frame_hom L p q g w (rawOfFrame L p φ)]
  change (nativePullFrame L p q g w φ).hom =
    (Scheme.Modules.pullbackCongr w).inv.app L.val ≫
      (Scheme.Modules.pullbackComp g p).inv.app L.val ≫
        (Scheme.Modules.pullback g).map ((φ.hom ≫ (pullbackUnitIso p).inv) ≫
          (pullbackUnitIso p).hom) ≫ (pullbackUnitIso g).hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Literal normalized frame restriction composes by the native pseudofunctor law. -/
theorem nativePullFrame_comp {X Y Z W : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (r : W ⟶ X) (g : Z ⟶ Y) (k : W ⟶ Z)
    (w : g ≫ p = q) (v : k ≫ q = r)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    nativePullFrame L q r k v (nativePullFrame L p q g w φ) =
      nativePullFrame L p r (k ≫ g) (by rw [Category.assoc, w, v]) φ := by
  apply rawOfFrame_injective L r
  rw [rawOfFrame_nativePullFrame, rawOfFrame_nativePullFrame,
    rawOfFrame_nativePullFrame, pullHom_pullHom]

/-- Pull back an actual frame along an actual commuting square, with native composition transport.
-/
def pullbackFrame {X S U V : Scheme.{u}} (f : S ⟶ X) (L : LineBundle X)
    (p : U ⟶ X) (q : V ⟶ S) (g : V ⟶ U) (w : g ≫ p = q ≫ f)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit U.ringCatSheaf) :
    (Scheme.Modules.pullback q).obj (pullbackLineBundle f L).val ≅
      SheafOfModules.unit V.ringCatSheaf :=
  (Scheme.Modules.pullbackComp q f).app L.val ≪≫ nativePullFrame L p (q ≫ f) g w φ

/-- The canonical composed pair isomorphism in the forward direction preserves tau. -/
theorem pairComp_compatibility {X S V : Scheme.{u}} (f : S ⟶ X) (q : V ⟶ S)
    {n : ℕ} (P : Pair X n) :
    (powerIso V (L := (pullbackPair q (pullbackPair f P)).lineBundle)
      (M := (pullbackPair (q ≫ f) P).lineBundle)
      ((Scheme.Modules.pullbackComp q f).app P.lineBundle.val) n).hom ≫
        (pullbackPair (q ≫ f) P).trivialization.hom =
      (pullbackPair q (pullbackPair f P)).trivialization.hom := by
  rw [← pullbackPair_comp_compatibility q f P,
      AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_symm,
    Iso.symm_hom, ← Category.assoc]
  have hc := Iso.hom_inv_id_assoc
    (powerIso V (L := (pullbackPair q (pullbackPair f P)).lineBundle)
      (M := (pullbackPair (q ≫ f) P).lineBundle)
      ((Scheme.Modules.pullbackComp q f).app P.lineBundle.val) n)
    (pullbackPair q (pullbackPair f P)).trivialization.hom
  simpa only [Category.assoc] using hc

/-- The specified nth-power condition survives actual pullback along the square. -/
def pullbackCompatibleFrame {X S U V : Scheme.{u}} (f : S ⟶ X) {n : ℕ} (P : Pair X n)
    (p : U ⟶ X) (q : V ⟶ S) (g : V ⟶ U) (w : g ≫ p = q ≫ f)
    (φ : CompatibleFrame U (pullbackPair p P)) :
    CompatibleFrame V (pullbackPair q (pullbackPair f P)) :=
  ⟨pullbackFrame f P.lineBundle p q g w φ.val, by
    apply (powerValue_eq_one_iff V _ _).mp
    change powerValue V (pullbackPair q (pullbackPair f P))
      ((Scheme.Modules.pullbackComp q f).app P.lineBundle.val ≪≫
        nativePullFrame P.lineBundle p (q ≫ f) g w φ.val) = 1
    rw [powerValue_pairIso V _ _ _ (pairComp_compatibility f q P),
      powerValue_nativePullFrame, (powerValue_eq_one_iff U _ _).mpr φ.property, map_one]⟩


/-- Actual native frame pullback commutes with positive scalar postcomposition. -/
theorem nativePullFrame_scalar {X Y Z : Scheme.{u}} (L : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) (g : Z ⟶ Y) (w : g ≫ p = q)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit Y.ringCatSheaf)
    (a : Γ(Y, ⊤)ˣ) :
    nativePullFrame L p q g w (φ ≪≫
        AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso Y _ a) =
      nativePullFrame L p q g w φ ≪≫
        AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso Z _
            (Units.map g.appTop.hom.toMonoidHom a) := by
  apply Iso.ext
  change (Scheme.Modules.pullbackCongr w).inv.app L.val ≫
    (Scheme.Modules.pullbackComp g p).inv.app L.val ≫
      (Scheme.Modules.pullback g).map (φ.hom ≫
          AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower.scalarMap Y _ a) ≫
        (pullbackUnitIso g).hom = _
  simp only [CategoryTheory.Functor.map_comp, Iso.trans_hom, Category.assoc]
  erw [AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.pullback_scalar_unit g a.val]
  rfl

theorem pullbackFrame_scalar {X S U V : Scheme.{u}} (f : S ⟶ X) (L : LineBundle X)
    (p : U ⟶ X) (q : V ⟶ S) (g : V ⟶ U) (w : g ≫ p = q ≫ f)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit U.ringCatSheaf)
    (a : Γ(U, ⊤)ˣ) :
    pullbackFrame f L p q g w (φ ≪≫
        AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso U _ a) =
      pullbackFrame f L p q g w φ ≪≫
        AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso V _
            (Units.map g.appTop.hom.toMonoidHom a) := by
  unfold pullbackFrame
  rw [nativePullFrame_scalar, Iso.trans_assoc]

/-- Actual unit comparison in the native full subcategory. -/
def rawUnitComparison {X S : Scheme.{u}} (f : S ⟶ X) :
    (lineBundles.map f.op.toLoc).toFunctor.obj (unitObject X) ⟶ unitObject S :=
  ObjectProperty.homMk (pullbackUnitIso f).hom

/-- Native Hom-presheaf base change followed by the structural unit comparison. -/
def rawBaseChange {X S V : Scheme.{u}} (f : S ⟶ X) (L : LineBundle X)
    (q : V ⟶ S)
    (α : (lineBundles.map (q ≫ f).op.toLoc).toFunctor.obj (ofLineBundle X L) ⟶
      (lineBundles.map (q ≫ f).op.toLoc).toFunctor.obj (unitObject X)) :
    (lineBundles.map q.op.toLoc).toFunctor.obj
      ((lineBundles.map f.op.toLoc).toFunctor.obj (ofLineBundle X L)) ⟶
      (lineBundles.map q.op.toLoc).toFunctor.obj (unitObject S) :=
  (lineBundles.overMapCompPresheafHomIso (ofLineBundle X L) (unitObject X) f).hom.app
    (op (Over.mk q)) α ≫ (lineBundles.map q.op.toLoc).toFunctor.map (rawUnitComparison f)

/-- Literal normalized frames use exactly the canonical native Hom base-change map. -/
theorem rawOfFrame_composed {X S V : Scheme.{u}} (f : S ⟶ X) (L : LineBundle X)
    (q : V ⟶ S)
    (φ : (Scheme.Modules.pullback (q ≫ f)).obj L.val ≅ SheafOfModules.unit V.ringCatSheaf) :
    rawOfFrame (pullbackLineBundle f L) q ((Scheme.Modules.pullbackComp q f).app L.val ≪≫ φ) =
      rawBaseChange f L q (rawOfFrame L (q ≫ f) φ) := by
  apply ObjectProperty.hom_ext
  apply (cancel_mono (pullbackUnitIso q).hom).mp
  change (((Scheme.Modules.pullbackComp q f).hom.app L.val ≫ φ.hom) ≫
    (pullbackUnitIso q).inv) ≫ (pullbackUnitIso q).hom =
      (((Scheme.Modules.pullbackComp q f).hom.app L.val ≫
        (φ.hom ≫ (pullbackUnitIso (q ≫ f)).inv)) ≫
        (Scheme.Modules.pullbackComp q f).inv.app (SheafOfModules.unit X.ringCatSheaf)) ≫
          (Scheme.Modules.pullback q).map (pullbackUnitIso f).hom ≫ (pullbackUnitIso q).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [Scheme.Modules.pullbackUnitIso_comp_inv q f]
  simp only [Iso.inv_hom_id, Category.comp_id]

universe u₁ v₁ u₂ v₂

/-- Native Hom-presheaf base change commutes with restriction for every pseudofunctor. -/
theorem nativeHomBaseChange_naturality {C : Type u₁} [Category.{v₁} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₂, u₂})
    {X S V W : C} (f : S ⟶ X) (M N : F.obj (.mk (op X)))
    (q : V ⟶ S) (r : W ⟶ S) (k : W ⟶ V) (w : k ≫ q = r)
    (α : (F.map (q ≫ f).op.toLoc).toFunctor.obj M ⟶
      (F.map (q ≫ f).op.toLoc).toFunctor.obj N) :
    pullHom ((F.overMapCompPresheafHomIso M N f).hom.app (op (Over.mk q)) α) k r r w w =
      (F.overMapCompPresheafHomIso M N f).hom.app (op (Over.mk r))
        (pullHom α k (r ≫ f) (r ≫ f)
          (by rw [← Category.assoc, w]) (by rw [← Category.assoc, w])) := by
  let a : Over.mk r ⟶ Over.mk q := Over.homMk k w
  exact (ConcreteCategory.congr_hom
    ((F.overMapCompPresheafHomIso M N f).hom.naturality a.op) α).symm

/-- Composition of native Hom restrictions, for an arbitrary pseudofunctor. -/
theorem nativePullHom_comp {C : Type u₁} [Category.{v₁} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₂, u₂})
    {S V W : C} (M N P : F.obj (.mk (op S)))
    (q : V ⟶ S) (r : W ⟶ S) (k : W ⟶ V) (w : k ≫ q = r)
    (α : (F.map q.op.toLoc).toFunctor.obj M ⟶ (F.map q.op.toLoc).toFunctor.obj N)
    (β : (F.map q.op.toLoc).toFunctor.obj N ⟶ (F.map q.op.toLoc).toFunctor.obj P) :
    pullHom (α ≫ β) k r r w w = pullHom α k r r w w ≫ pullHom β k r r w w := by
  dsimp [pullHom]
  simp [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Native restriction of a pulled global morphism, for every pseudofunctor. -/
theorem nativePullHom_global {C : Type u₁} [Category.{v₁} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₂, u₂})
    {S V W : C} (q : V ⟶ S) (k : W ⟶ V) (r : W ⟶ S) (w : k ≫ q = r)
    {M N : F.obj (.mk (op S))} (β : M ⟶ N) :
    pullHom ((F.map q.op.toLoc).toFunctor.map β) k r r w w =
      (F.map r.op.toLoc).toFunctor.map β := by
  let e := Cat.Hom.toNatIso (F.mapComp' q.op.toLoc k.op.toLoc r.op.toLoc (by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp, w]))
  have hn := e.hom.naturality β
  change (F.map r.op.toLoc).toFunctor.map β ≫ (e.app N).hom =
    (e.app M).hom ≫
      (F.map k.op.toLoc).toFunctor.map ((F.map q.op.toLoc).toFunctor.map β) at hn
  change (e.app M).hom ≫
    (F.map k.op.toLoc).toFunctor.map ((F.map q.op.toLoc).toFunctor.map β) ≫
    (e.app N).inv = _
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Native Hom base change followed by any genuine global target map is natural. -/
theorem nativeHomBaseChange_postcomp_naturality {C : Type u₁} [Category.{v₁} C]
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₂, u₂})
    {X S V W : C} (f : S ⟶ X) (M N : F.obj (.mk (op X)))
    (P : F.obj (.mk (op S))) (β : (F.map f.op.toLoc).toFunctor.obj N ⟶ P)
    (q : V ⟶ S) (r : W ⟶ S) (k : W ⟶ V) (w : k ≫ q = r)
    (α : (F.map (q ≫ f).op.toLoc).toFunctor.obj M ⟶
      (F.map (q ≫ f).op.toLoc).toFunctor.obj N) :
    pullHom ((F.overMapCompPresheafHomIso M N f).hom.app (op (Over.mk q)) α ≫
      (F.map q.op.toLoc).toFunctor.map β) k r r w w =
      (F.overMapCompPresheafHomIso M N f).hom.app (op (Over.mk r))
        (pullHom α k (r ≫ f) (r ≫ f)
          (by rw [← Category.assoc, w]) (by rw [← Category.assoc, w])) ≫
        (F.map r.op.toLoc).toFunctor.map β := by
  rw [nativePullHom_comp F ((F.map f.op.toLoc).toFunctor.obj M)
    ((F.map f.op.toLoc).toFunctor.obj N) P q r k w,
    nativeHomBaseChange_naturality F f M N q r k w,
    nativePullHom_global F q k r w β]

/-- The canonical Hom base-change map is natural for the native restrictions. -/
theorem rawBaseChange_naturality {X S V W : Scheme.{u}} (f : S ⟶ X) (L : LineBundle X)
    (q : V ⟶ S) (r : W ⟶ S) (k : W ⟶ V) (w : k ≫ q = r)
    (α : (lineBundles.map (q ≫ f).op.toLoc).toFunctor.obj (ofLineBundle X L) ⟶
      (lineBundles.map (q ≫ f).op.toLoc).toFunctor.obj (unitObject X)) :
    pullHom (rawBaseChange f L q α) k r r w w =
      rawBaseChange f L r (pullHom α k (r ≫ f) (r ≫ f)
        (by rw [← Category.assoc, w]) (by rw [← Category.assoc, w])) :=
  nativeHomBaseChange_postcomp_naturality lineBundles f
    (ofLineBundle X L) (unitObject X) (unitObject S) (rawUnitComparison f) q r k w α

/-- Native restriction commutes with the literal pullback frame map. -/
theorem pullbackFrame_restriction {X S U V W : Scheme.{u}} (f : S ⟶ X) (L : LineBundle X)
    (p : U ⟶ X) (q : V ⟶ S) (r : W ⟶ S) (g : V ⟶ U) (k : W ⟶ V)
    (w : g ≫ p = q ≫ f) (v : k ≫ q = r)
    (φ : (Scheme.Modules.pullback p).obj L.val ≅ SheafOfModules.unit U.ringCatSheaf) :
    nativePullFrame (pullbackLineBundle f L) q r k v (pullbackFrame f L p q g w φ) =
      pullbackFrame f L p r (k ≫ g) (by rw [Category.assoc, w, ← Category.assoc, v]) φ := by
  apply rawOfFrame_injective (pullbackLineBundle f L) r
  rw [rawOfFrame_nativePullFrame]
  unfold pullbackFrame
  rw [rawOfFrame_composed, rawOfFrame_composed, rawBaseChange_naturality,
    rawOfFrame_nativePullFrame, rawOfFrame_nativePullFrame, pullHom_pullHom]

/-- Actual pullback of positive compatible-frame sections on the small-etale base-change objects. -/
def sectionMap (h : EtaleLineBundleDescent.{u}) {X S : Scheme.{u}} (f : S ⟶ X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n)
    (U : X.Etaleᵒᵖ) :
    (torsor h X n hn hinv P).carrier.obj.obj U →
      (torsor h S n hn
          (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
        (pullbackPair f P)).carrier.obj.obj ((siteBaseChange f).op.obj U) := fun s =>
  (sectionsEquiv h S n hn
      (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
    (pullbackPair f P) ((siteBaseChange f).op.obj U)).symm
    (pullbackCompatibleFrame f P U.unop.hom (Limits.pullback.snd U.unop.hom f)
      (Limits.pullback.fst U.unop.hom f) (Limits.pullback.condition)
      (sectionsEquiv h X n hn hinv P U s))

/-- The literal section map intertwines exactly the canonical root coefficient unit. -/
theorem sectionMap_equivariant (h : EtaleLineBundleDescent.{u}) {X S : Scheme.{u}} (f : S ⟶ X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n)
    (U : X.Etaleᵒᵖ) (ζ : (mu X n).obj.obj U)
    (s : (torsor h X n hn hinv P).carrier.obj.obj U) :
    sectionMap h f n hn hinv P U ((torsor h X n hn hinv P).action U ζ s) =
      (torsor h S n hn
          (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n
          hinv) (pullbackPair f P)).action
        ((siteBaseChange f).op.obj U)
            ((GroupCohomology.Kummer.CoefficientBaseChange.rootsUnit f
            n).hom.app U ζ)
          (sectionMap h f n hn hinv P U s) := by
  apply (sectionsEquiv h S n hn
      (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
    (pullbackPair f P) ((siteBaseChange f).op.obj U)).injective
  apply Subtype.ext
  rw [sectionsEquiv_action]
  change (sectionsEquiv h S n hn
      (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
    (pullbackPair f P) ((siteBaseChange f).op.obj U)
      ((sectionsEquiv h S n hn
          (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
        (pullbackPair f P) ((siteBaseChange f).op.obj U)).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  change pullbackFrame f P.lineBundle U.unop.hom (Limits.pullback.snd U.unop.hom f)
    (Limits.pullback.fst U.unop.hom f) (Limits.pullback.condition)
      (sectionsEquiv h X n hn hinv P U ((torsor h X n hn hinv P).action U ζ s)).val = _
  rw [sectionsEquiv_action]
  have hs := pullbackFrame_scalar f P.lineBundle U.unop.hom (Limits.pullback.snd U.unop.hom f)
    (Limits.pullback.fst U.unop.hom f) Limits.pullback.condition
    (sectionsEquiv h X n hn hinv P U s).val
    ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ)
  erw [hs]
  congr 1
  · simp only [sectionMap, Equiv.apply_symm_apply]
    rfl
  · congr 1
    exact (GroupCohomology.Kummer.CoefficientBaseChange.rootsUnit_sections f n
        U ζ).symm

/-- The literal base-change section map is natural on the actual small etale site. -/
theorem sectionMap_naturality (h : EtaleLineBundleDescent.{u}) {X S : Scheme.{u}} (f : S ⟶ X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n)
    {U V : X.Etaleᵒᵖ} (a : U ⟶ V)
    (s : (torsor h X n hn hinv P).carrier.obj.obj U) :
    (torsor h S n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
      (pullbackPair f P)).carrier.obj.map ((siteBaseChange f).op.map a)
        (sectionMap h f n hn hinv P U s) =
      sectionMap h f n hn hinv P V ((torsor h X n hn hinv P).carrier.obj.map a s) := by
  apply (sectionsEquiv h S n hn
      (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
    (pullbackPair f P) ((siteBaseChange f).op.obj V)).injective
  apply Subtype.ext
  rw [sectionsEquiv_naturality]
  change nativePullFrame (pullbackLineBundle f P.lineBundle)
    (Limits.pullback.snd U.unop.hom f) (Limits.pullback.snd V.unop.hom f)
    ((siteBaseChange f).map a.unop).left ((siteBaseChange f).map a.unop).w
    ((sectionsEquiv h S n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
      (pullbackPair f P) ((siteBaseChange f).op.obj U))
        ((sectionsEquiv h S n hn
            (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
          (pullbackPair f P) ((siteBaseChange f).op.obj U)).symm _)).val =
    ((sectionsEquiv h S n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
      (pullbackPair f P) ((siteBaseChange f).op.obj V))
        ((sectionsEquiv h S n hn
            (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
          (pullbackPair f P) ((siteBaseChange f).op.obj V)).symm _)).val
  simp only [Equiv.apply_symm_apply]
  change nativePullFrame (pullbackLineBundle f P.lineBundle)
    (Limits.pullback.snd U.unop.hom f) (Limits.pullback.snd V.unop.hom f)
    ((siteBaseChange f).map a.unop).left ((siteBaseChange f).map a.unop).w
      (pullbackFrame f P.lineBundle U.unop.hom (Limits.pullback.snd U.unop.hom f)
        (Limits.pullback.fst U.unop.hom f) Limits.pullback.condition
          (sectionsEquiv h X n hn hinv P U s).val) =
    pullbackFrame f P.lineBundle V.unop.hom (Limits.pullback.snd V.unop.hom f)
      (Limits.pullback.fst V.unop.hom f) Limits.pullback.condition
        (sectionsEquiv h X n hn hinv P V ((torsor h X n hn hinv P).carrier.obj.map a s)).val
  rw [sectionsEquiv_naturality, pullbackFrame_restriction]
  unfold pullbackFrame
  rw [nativePullFrame_comp]
  have hk : ((siteBaseChange f).map a.unop).left ≫ Limits.pullback.fst U.unop.hom f =
      Limits.pullback.fst V.unop.hom f ≫ a.unop.left :=
    Limits.pullback.lift_fst _ _ _
  congr 1
  congr 1

/-- Actual adjoint morphism of compatible-frame torsors, with the canonical root coefficient map. -/
def torsorAdjointHom (h : EtaleLineBundleDescent.{u}) {X S : Scheme.{u}} (f : S ⟶ X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n) :
    Scheme.EtaleH1.Torsor.AdjointHom f
        (GroupCohomology.Kummer.CoefficientBaseChange.rootsUnit f n)
      (torsor h X n hn hinv P)
      (torsor h S n hn
          (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
        (pullbackPair f P)) where
  map := ⟨{ app U := ↾(sectionMap h f n hn hinv P U)
            naturality {_ _} a := by
              ext s
              exact (sectionMap_naturality h f n hn hinv P a s).symm }⟩
  equivariant := sectionMap_equivariant h f n hn hinv P

universe w w'
/-- Genuine generic/scheme restriction of the canonical power-pair Ext class. -/
theorem h1Map_torsor (h : EtaleLineBundleDescent.{u}) {X S : Scheme.{u}} (f : S ⟶ X)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n) :
    GroupCohomology.Kummer.CoefficientBaseChange.h1Map f n hn hinv
      (torsorExtClass (torsor h X n hn hinv P)) =
    torsorExtClass (torsor h S n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
      (pullbackPair f P)) :=
  GroupCohomology.Kummer.CoefficientBaseChange.h1Map_torsor f n hn hinv
    (torsorAdjointHom h f n hn hinv P)


end AlgebraicGeometry.Scheme.Modules.Invertible.PowerBaseChange
