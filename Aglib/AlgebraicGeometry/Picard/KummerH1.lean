/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Points.Closed
public import Aglib.AlgebraicGeometry.Picard.PowerRoot
public import Aglib.AlgebraicGeometry.Picard.AssociatedBundle
public import Aglib.AlgebraicGeometry.Picard.FrameTensor
public import Aglib.AlgebraicGeometry.Picard.PowerDescent
public import Aglib.AlgebraicGeometry.Picard.PowerBaseChange
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.KummerH1` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`83b31121f19ff8c719e8e7d4b61fb9c22bf11487358f20219e833e991a487e17`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (classOf pullbackClass pullbackLineBundle tensorPowerLineBundle)
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
# Canonical Kummer classes of actual power-trivialized line bundles

Manuscript locators: `K2-018#lem:k2018-geometric-exact-order` and C3/C4 of
`EllipticIntegralK2/Delegation/PicardKummer.md`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Lean 4.34.1; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The forward map is the canonical Ext class of the actual small-etale torsor
of O-linear frames phi : L -> O satisfying phi^n = tau. Actual pair
isomorphisms induce actual equivariant sheaf maps, and forgetting the power
condition is equivariant for the literal mu_n inclusion into Gm.
The inverse application consumes PowerDescent's genuine transition functions,
descended line bundle, glued power trivialization and actual torsor recovery.
Neither a Picard/H1 classification nor the desired class equality is assumed.

For the fixed actual curve pair quotient, the forward map is bijective by
actual reciprocal descent recovery, without a global-unit root hypothesis.
When global units admit nth roots, additivity is proved using the actual frame
tensor construction and its Ext addition law, together with the proved
injectivity of the literal coefficient inclusion. This identifies actual
mu_n H1 with the n-torsion of the ordinary tensor/dual Picard group, including
level one. The integral/Noetherian/closed-DVR assumptions in that quotient
section match the accepted TrivializedPower API. The forward sheaf maps
before that section apply to arbitrary schemes. Positivity and invertibility
of n are explicit. Geometric proper constants supply the roots hypothesis
only in the higher curve adapter.

Retained general inputs are exactly the fixed rank-one etale stack theorem
EtaleLineBundleDescent (023T/05B2) and A's canonical torsor/Ext bijectivity
Stacks03AJ, with explicit Ext-size infrastructure. Local roots and the actual
03PL sheaf epimorphism have been proved through genuine finite-etale root
covers. No finite-fundamental-group, product-normalization, or K-theoretic
comparison is used in this reusable Picard module.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.KummerH1
open EtaleDescent UnitPower TrivializedPower PowerPullback TrivializedPowerTorsor FrameTorsor
open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.GroupCohomology.Kummer.Coefficients
universe u w

/-- The actual pullback of a specified pair isomorphism preserves the specified powers. -/
theorem pairIso_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {n : ℕ} {P Q : Pair X n}
    (e : P.lineBundle.val ≅ Q.lineBundle.val)
    (he : (powerIso X e n).hom ≫ Q.trivialization.hom = P.trivialization.hom) :
    (powerIso Y (L := (pullbackPair f P).lineBundle) (M := (pullbackPair f Q).lineBundle)
      ((Scheme.Modules.pullback f).mapIso e) n).hom ≫
        (pullbackPair f Q).trivialization.hom = (pullbackPair f P).trivialization.hom := by
  change (powerIso Y ((Scheme.Modules.pullback f).mapIso e) n).hom ≫
    ((pullbackPowerIso f Q.lineBundle n).inv ≫
      (Scheme.Modules.pullback f).map Q.trivialization.hom ≫ (pullbackUnitIso f).hom) =
    (pullbackPowerIso f P.lineBundle n).inv ≫
      (Scheme.Modules.pullback f).map P.trivialization.hom ≫ (pullbackUnitIso f).hom
  rw [← Category.assoc,
      PowerPullbackNaturality.pullbackPowerIso_inv_naturality,
    Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, he]

/-- A genuine pair isomorphism acts on the actual compatible-frame sections. -/
def pairSectionMap (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) {P Q : Pair X n}
    (e : P.lineBundle.val ≅ Q.lineBundle.val)
    (he : (powerIso X e n).hom ≫ Q.trivialization.hom = P.trivialization.hom)
    (U : X.Etaleᵒᵖ) (s : (torsor h X n hn hinv P).carrier.obj.obj U) :
    (torsor h X n hn hinv Q).carrier.obj.obj U :=
  ⟨AssociatedBundle.mapFrame h e U s.val, by
    apply (framePowerSection_eq_zero_iff h X Q U _).mpr
    have hc := (AlgebraicGeometry.Scheme.Modules.Invertible.PowerRoot.compatibleFrameEquiv
        U.unop.left
      (pullbackPair U.unop.hom P) (pullbackPair U.unop.hom Q)
      ((Scheme.Modules.pullback U.unop.hom).mapIso e)
      (pairIso_pullback U.unop.hom e he) (sectionsEquiv h X n hn hinv P U s)).property
    change (powerIso U.unop.left (L := (pullbackPair U.unop.hom Q).lineBundle)
      (M := unitLineBundle U.unop.left)
      (frameSectionsEquiv h X Q.lineBundle U
          (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.mapFrame h e U s.val))
          n).hom ≫
        (unitPowerIso U.unop.left n).hom = _
    simp only [AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.mapFrame,
        Equiv.apply_symm_apply]
    exact hc⟩

/-- The actual compatible-frame sheaf map is equivariant, hence a torsor isomorphism. -/
def pairTorsorIso (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) {P Q : Pair X n}
    (e : P.lineBundle.val ≅ Q.lineBundle.val)
    (he : (powerIso X e n).hom ≫ Q.trivialization.hom = P.trivialization.hom) :
    Scheme.EtaleH1.Torsor.Iso (torsor h X n hn hinv P) (torsor h X n
        hn hinv Q) :=
  (show Scheme.EtaleH1.Torsor.Hom (𝟙 (mu X n)) (torsor h X n hn hinv
      P) (torsor h X n hn hinv Q) from
    { map := ⟨{ app U := ↾(pairSectionMap h X n hn hinv e he U)
                naturality {_ _} a := by
                  ext s
                  apply Subtype.ext
                  exact (AssociatedBundle.mapFrame_naturality h e a s.val).symm }⟩
      equivariant U ζ s := by
        apply Subtype.ext
        exact AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.mapFrame_equivariant
            h e U ((inclusion X n).hom.app U ζ) s.val }).toIso

/-- Forgetting the actual nth-power condition is coefficient-equivariant. -/
def forgetCompatible (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n) :
    Scheme.EtaleH1.Torsor.Hom (inclusion X n) (torsor h X n hn hinv P)
        (frameTorsor h X P.lineBundle) where
  map := ⟨{ app _ := ↾Subtype.val
            naturality := by intros; rfl }⟩
  equivariant _ _ _ := rfl

/-- A morphism to the actual compatible-frame torsor gives an actual descended pair isomorphism. -/
def recoveredPairIso (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (R : Torsor (mu X n)) (Q : Pair X n)
    (a : Scheme.EtaleH1.Torsor.Hom (𝟙 (mu X n)) R (torsor h X n hn
        hinv Q)) :
    (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.pair R h).lineBundle.val ≅
        Q.lineBundle.val :=
  AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.lineBundleIsoOfFrameMap R h Q.lineBundle
    { map := a.map ≫ (forgetCompatible h X n hn hinv Q).map
      equivariant U ζ s := by
        change (a.map.hom.app U (R.action U ζ s)).val = _
        rw [a.equivariant]
        rfl }

/-- The recovered pair isomorphism preserves tau because every image section is power-compatible. -/
theorem recoveredPairIso_compatible (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (R : Torsor (mu X n)) (Q : Pair X n)
    (a : Scheme.EtaleH1.Torsor.Hom (𝟙 (mu X n)) R (torsor h X n hn
        hinv Q)) :
    (powerIso X (recoveredPairIso h X n hn hinv R Q a) n).hom ≫ Q.trivialization.hom =
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.pair R h).trivialization.hom := by
  let e := recoveredPairIso h X n hn hinv R Q a
  let r : Scheme.EtaleH1.Torsor.Hom (inclusion X n) R (frameTorsor h X
      Q.lineBundle) :=
    { map := a.map ≫ (forgetCompatible h X n hn hinv Q).map
      equivariant U ζ s := by
        change (a.map.hom.app U (R.action U ζ s)).val = _
        rw [a.equivariant]
        rfl }
  apply AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.moduleHom_ext R h
    (tensorPowerLineBundle X
        (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.lineBundle R h) n)
        (unitLineBundle X)
  intro i
  apply (cancel_mono (pullbackUnitIso
      (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i)).hom).mp
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  change (Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i)).map
      (powerIso X e n).hom ≫
    (Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i)).map
        Q.trivialization.hom ≫
      (pullbackUnitIso (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R
          i)).hom =
    (Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i)).map
        (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.trivialization R h).hom ≫
      (pullbackUnitIso (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R
          i)).hom
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.trivialization_chart]
  let t := a.map.hom.app (op i.1) i.2
  let φ := frameSectionsEquiv h X Q.lineBundle (op i.1) t.val
  have hφ := (framePowerSection_eq_zero_iff h X Q (op i.1) t.val).mp t.property
  have ht : (Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i)).map
      Q.trivialization.hom ≫
      (pullbackUnitIso (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R
          i)).hom =
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.powerFrame Q.lineBundle
          (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i) φ n).hom := by
    change (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.normalizedPower (L :=
        pullbackLineBundle
        (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i)
        Q.lineBundle) φ n).hom =
      (pullbackPowerIso (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap
          R i) Q.lineBundle n).inv ≫
        (Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i)).map
            Q.trivialization.hom ≫
          (pullbackUnitIso
              (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i)).hom at hφ
    unfold AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.powerFrame
    rw [Iso.trans_hom, hφ, Iso.hom_inv_id_assoc]
  rw [ht, AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.powerFrame_map (L :=
      AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.lineBundle R h) (M := Q.lineBundle)
    e (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i) φ n]
  have he : (Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.coverMap R i)).mapIso e ≪≫ φ =
      AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.chart R h i := by
    apply Iso.ext
    exact PowerDescent.lineBundleIsoOfFrameMap_chart R h Q.lineBundle r i
  rw [he]
  rfl

/-- Actual torsor isomorphisms recover actual pair isomorphisms, without any global-root
assumption. -/
theorem pairIsomorphic_of_torsorIso (h : EtaleLineBundleDescent.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P Q : Pair X n)
    (a : Scheme.EtaleH1.Torsor.Iso (torsor h X n hn hinv P) (torsor h
        X n hn hinv Q)) : Isomorphic X P Q := by
  let R := torsor h X n hn hinv P
  let r : Scheme.EtaleH1.Torsor.Hom (𝟙 (mu X n)) R (torsor h X n hn
      hinv Q) := ⟨a.carrierIso.hom, a.equivariant⟩
  let e := AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.pairBundleRecovery h hn hinv P
  let f := recoveredPairIso h X n hn hinv R Q r
  have he :=
      AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.pairBundleRecovery_compatible h
      hn hinv P
  have hf := recoveredPairIso_compatible h X n hn hinv R Q r
  refine ⟨e.symm ≪≫ f, ?_⟩
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_trans X e.symm f n,
      Iso.trans_hom, Category.assoc, hf]
  rw [← he, AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_symm X e n,
      Iso.symm_hom, Iso.inv_hom_id_assoc]

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : AlgebraicGeometry.Scheme.ClosedPoint X, IsDiscreteValuationRing
    (X.presheaf.stalk x.val)]
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Canonical Ext classes of the actual compatible-frame torsors descend to actual pair classes. -/
def pairClassToH1 (h : EtaleLineBundleDescent.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) : Classes X n → H1Etale X (mu X n) :=
  Quotient.lift (fun P => torsorExtClass (torsor h X n hn hinv P)) (by
    intro P Q hPQ
    obtain ⟨e, he⟩ := hPQ
    exact torsorExtClass_iso (pairTorsorIso h X n hn hinv e he))

omit [IsNoetherian X]
  [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
@[simp] theorem pairClassToH1_mk [IsNoetherian X]
    [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (h : EtaleLineBundleDescent.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Pair X n) :
    pairClassToH1 X h n hn hinv (Quotient.mk _ P) = torsorExtClass (torsor h X n hn hinv P) := rfl

omit [IsNoetherian X]
  [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
/-- The coefficient inclusion takes the actual power-frame class to the underlying frame class. -/
theorem pairClassToH1_forget [IsNoetherian X]
    [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (h : EtaleLineBundleDescent.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (P : Classes X n) :
    coefficientMap (inclusion X n) (pairClassToH1 X h n hn hinv P) =
      torsorClassToH1 (gm X)
          (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.classEquiv h
          (forgetClass X P)) := by
  refine Quotient.inductionOn P ?_
  intro P
  exact torsorExtClass_naturality (forgetCompatible h X n hn hinv P)

/-- Over nth-root-surjective global units, the canonical actual power-frame class map is
injective. -/
theorem pairClassToH1_injective_of_global_roots (h : EtaleLineBundleDescent.{u}) (h03AJ :
    Stacks03AJ.{u, w} X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) :
    Function.Injective (pairClassToH1 X h n hn hinv) := by
  intro P Q hPQ
  apply forgetClass_injective X hroot
  apply (AlgebraicGeometry.Scheme.Modules.Invertible.AssociatedBundle.classEquiv h).injective
  apply (h03AJ.bijective (gm X)).injective
  rw [← pairClassToH1_forget X h n hn hinv, ← pairClassToH1_forget X h n hn hinv, hPQ]

omit [IsNoetherian X]
  [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
/-- The canonical pair/H1 class map is injective by actual tau-preserving descent recovery. -/
theorem pairClassToH1_injective [IsNoetherian X]
    [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (h : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    Function.Injective (pairClassToH1 X h n hn hinv) := by
  intro P Q hPQ
  obtain ⟨P, rfl⟩ := Quotient.exists_rep P
  obtain ⟨Q, rfl⟩ := Quotient.exists_rep Q
  have ht : (Quotient.mk _ (torsor h X n hn hinv P) : TorsorClass (mu X n)) =
      Quotient.mk _ (torsor h X n hn hinv Q) := (h03AJ.bijective (mu X n)).injective hPQ
  obtain ⟨e⟩ := Quotient.exact ht
  exact Quotient.sound (pairIsomorphic_of_torsorIso h X n hn hinv P Q e)

omit [IsNoetherian X]
  [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
/-- Every actual mu torsor descends to an actual line bundle with a specified power
trivialization. -/
theorem pairClassToH1_surjective [IsNoetherian X]
    [∀ x : Scheme.ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (h : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    Function.Surjective (pairClassToH1 X h n hn hinv) := by
  intro x
  obtain ⟨c, hc⟩ := (h03AJ.bijective (mu X n)).surjective x
  obtain ⟨P, rfl⟩ := Quotient.exists_rep c
  refine ⟨Quotient.mk _ (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.pair P h), ?_⟩
  change torsorExtClass (torsor h X n hn hinv
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.pair P h)) = x
  exact (torsorExtClass_iso
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.torsorRecovery P h hn
      hinv)).symm.trans hc

/-- Actual power-pair classes classify mu-H1 without killing the global units/n term. -/
def pairH1ClassEquiv (h : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) : Classes X n ≃ H1Etale X (mu X n) :=
  Equiv.ofBijective (pairClassToH1 X h n hn hinv)
    ⟨pairClassToH1_injective X h h03AJ n hn hinv, pairClassToH1_surjective X h h03AJ n hn hinv⟩

/-- The actual mu-to-Gm coefficient map is injective when all global units have nth roots. -/
theorem inclusion_H1_injective (h : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) :
    Function.Injective (fun x : H1Etale X (mu X n) =>
      coefficientMap (X := X) (inclusion X n) x) := by
  intro x y hxy
  obtain ⟨P, rfl⟩ := pairClassToH1_surjective X h h03AJ n hn hinv x
  obtain ⟨Q, rfl⟩ := pairClassToH1_surjective X h h03AJ n hn hinv y
  have hpq : P = Q := by
    apply forgetClass_injective X hroot
    apply (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTensor.picardH1Equiv h X
        h03AJ).injective
    exact (pairClassToH1_forget X h n hn hinv P).symm.trans
      (hxy.trans (pairClassToH1_forget X h n hn hinv Q))
  rw [hpq]

/-- Actual tensor addition of pairs maps to Ext addition, through literal coefficient inclusion. -/
theorem pairClassToH1_add (h : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) :
    letI := classesAddCommGroup X n hroot
    ∀ P Q : Classes X n, pairClassToH1 X h n hn hinv (P + Q) =
      pairClassToH1 X h n hn hinv P + pairClassToH1 X h n hn hinv Q := by
  let := classesAddCommGroup X n hroot
  intro P Q
  apply inclusion_H1_injective X h h03AJ n hn hinv hroot
  change coefficientMap (X := X) (inclusion X n) (pairClassToH1 X h n hn hinv (P + Q)) =
    coefficientMap (X := X) (inclusion X n)
      (pairClassToH1 X h n hn hinv P + pairClassToH1 X h n hn hinv Q)
  rw [map_add, pairClassToH1_forget, pairClassToH1_forget, pairClassToH1_forget]
  change (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTensor.picardH1Equiv h X h03AJ)
      (forgetClass X (P + Q)) =
    (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTensor.picardH1Equiv h X h03AJ)
        (forgetClass X P) +
      (AlgebraicGeometry.Scheme.Modules.Invertible.FrameTensor.picardH1Equiv h X h03AJ)
          (forgetClass X Q)
  have hf : forgetClass X (P + Q) = forgetClass X P + forgetClass X Q :=
    congrArg Subtype.val ((picardTorsionAddEquiv X n hroot).map_add P Q)
  rw [hf, map_add]

/-- The actual geometric power-pair classification, with its proved tensor/additive law. -/
def pairH1Equiv (h : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) :
    letI := classesAddCommGroup X n hroot
    Classes X n ≃+ H1Etale X (mu X n) := by
  letI := classesAddCommGroup X n hroot
  exact { Equiv.ofBijective (pairClassToH1 X h n hn hinv)
      ⟨pairClassToH1_injective X h h03AJ n hn hinv,
        pairClassToH1_surjective X h h03AJ n hn hinv⟩ with
    map_add' := pairClassToH1_add X h h03AJ n hn hinv hroot }

/-- The actual geometric mu-H1 group is precisely the torsion of the ordinary Picard group. -/
def h1PicardTorsionEquiv (h : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) :
    H1Etale X (mu X n) ≃+ AlgebraicGeometry.Scheme.Modules.Invertible.Torsion.picardTorsion X n
        := by
  letI := classesAddCommGroup X n hroot
  exact (pairH1Equiv X h h03AJ n hn hinv hroot).symm.trans (picardTorsionAddEquiv X n hroot)

/-- The Picard image of a genuine power-frame torsor is its actual underlying line bundle. -/
theorem h1PicardTorsionEquiv_torsor (h : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (hroot : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n)) (P : Pair X n) :
    (h1PicardTorsionEquiv X h h03AJ n hn hinv hroot
      (torsorExtClass (torsor h X n hn hinv P))).val = classOf X P.lineBundle := by
  let := classesAddCommGroup X n hroot
  change (picardTorsionAddEquiv X n hroot
    ((pairH1Equiv X h h03AJ n hn hinv hroot).symm
      ((pairH1Equiv X h h03AJ n hn hinv hroot) (Quotient.mk _ P)))).val = _
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- The actual level-one cohomology group is trivial, including the accepted n=1 endpoint. -/
theorem h1_level_one_eq_zero (h : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (x : H1Etale X (mu X 1)) : x = 0 := by
  have hu : IsUnit ((1 : ℕ) : Γ(X, ⊤)) := by simp
  obtain ⟨P, hP⟩ := pairClassToH1_surjective X h h03AJ 1 (by decide) hu x
  obtain ⟨Q, hQ⟩ := pairClassToH1_surjective X h h03AJ 1 (by decide) hu 0
  exact hP.symm.trans ((congrArg (pairClassToH1 X h 1 (by decide) hu)
    (Subsingleton.elim P Q)).trans hQ)

universe w'
/-- The constructed H1/Picard map commutes with actual scheme pullback. -/
theorem h1PicardTorsionEquiv_pullback
    {Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
    [∀ y : AlgebraicGeometry.Scheme.ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (f : Y ⟶ X) (h : EtaleLineBundleDescent.{u})
    (hAX : Stacks03AJ.{u, w} X) (hAY : Stacks03AJ.{u, w'} Y)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (hrootX : Function.Surjective (fun a : Γ(X, ⊤)ˣ => a ^ n))
    (hrootY : Function.Surjective (fun a : Γ(Y, ⊤)ˣ => a ^ n))
    (x : H1Etale X (mu X n)) :
    (h1PicardTorsionEquiv Y h hAY n hn
      (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv)
          hrootY
      (GroupCohomology.Kummer.CoefficientBaseChange.h1Map f n hn hinv x)).val =
    pullbackClass f (h1PicardTorsionEquiv X h hAX n hn hinv hrootX x).val := by
  obtain ⟨c, rfl⟩ := pairClassToH1_surjective X h hAX n hn hinv x
  obtain ⟨P, rfl⟩ := Quotient.exists_rep c
  change (h1PicardTorsionEquiv Y h hAY n hn
    (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n hinv) hrootY
    (GroupCohomology.Kummer.CoefficientBaseChange.h1Map f n hn hinv
      (torsorExtClass (torsor h X n hn hinv P)))).val = _
  rw [AlgebraicGeometry.Scheme.Modules.Invertible.PowerBaseChange.h1Map_torsor,
      h1PicardTorsionEquiv_torsor,
    pairClassToH1_mk, h1PicardTorsionEquiv_torsor]
  rfl

end AlgebraicGeometry.Scheme.Modules.Invertible.KummerH1
