/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.TrivializedPowerTorsor
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.PowerRoot` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`52d0ea85887ad14b7697241c637393ed0ed904d95ba90d5acc52d036e965b272`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (pullbackLineBundle )
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
# Literal positive roots of unit power pairs

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The actual unit pair has underlying O and chosen nth-power trivialization
canonical multiplication followed by multiplication by f. Its actual
power-compatible frame torsor is identified, section by section and
naturally on the small-etale site, with the existing positive root torsor.
The literal O-linear frame coordinate a satisfies a^n=f; the root action
is positive multiplication by zeta. The sheaf isomorphism is proved
equivariant and therefore identifies the canonical Ext classes without03AJ.

The inverse coordinate is separately identified with normalized sections
f*s^n=1, and its root action is explicitly inverted. Native structural
pullback and the unit-pair trivialization are matched by actual canonical
power/unit comparison maps. This fixes the sign before any field comparison.
Only the fixed all-rank-one etale descent family is used for the frame sheaf;
local roots are provided by the proved power epimorphism. No H1 or Picard
classification, curve generic identity or new standard family is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PowerRoot
open TrivializedPower UnitPower PowerPullback TrivializedPowerTorsor
universe u

/-- The actual unit line bundle with nth-power trivialization multiplication by f. -/
def unitPair (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)ˣ) : Pair X n where
  lineBundle := unitLineBundle X
  trivialization := unitPowerIso X n ≪≫
      AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _ f

/-- The actual unit pullback isomorphism preserves the specified power trivialization. -/
theorem unitPair_pullback {X Y : Scheme.{u}} (q : X ⟶ Y) (n : ℕ) (f : Γ(Y, ⊤)ˣ) :
    (powerIso X (L := (pullbackPair q (unitPair Y n f)).lineBundle)
      (M := unitLineBundle X) (pullbackUnitIso q) n).hom ≫
        (unitPair X n (Units.map q.appTop.hom.toMonoidHom f)).trivialization.hom =
      (pullbackPair q (unitPair Y n f)).trivialization.hom := by
  change (powerIso X (L := pullbackLineBundle q (unitLineBundle Y)) (M := unitLineBundle X)
      (pullbackUnitIso q) n).hom ≫
        ((unitPowerIso X n).hom ≫ scalarMap X _ (Units.map q.appTop.hom.toMonoidHom f)) =
    (pullbackPowerIso q (unitLineBundle Y) n).inv ≫
      (Scheme.Modules.pullback q).map ((unitPowerIso Y n).hom ≫ scalarMap Y _ f) ≫
        (pullbackUnitIso q).hom
  apply (pullbackPowerIso q (unitLineBundle Y) n).eq_inv_comp.mpr
  have hu := congrArg (fun a => a ≫ scalarMap X (SheafOfModules.unit X.ringCatSheaf)
    (Units.map q.appTop.hom.toMonoidHom f : Γ(X, ⊤)ˣ)) (unitPowerIso_pullback q n)
  simp only [Category.assoc] at hu ⊢
  erw [hu]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.pullback_scalar_unit]
  rfl

/-- For the unit pair, compatible positive frames are exactly a^n=f. -/
theorem unitPair_compatible_iff (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)ˣ)
    (φ : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    (powerIso X (L := unitLineBundle X) (M := unitLineBundle X) φ n).hom ≫
        (unitPowerIso X n).hom = (unitPair X n f).trivialization.hom ↔
      unitOfIso X φ ^ n = f := by
  have hφ := (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
      X).left_inv φ
  change AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _
      (unitOfIso X φ) = φ at hφ
  conv_lhs => rw [← hφ]
  rw [unitPowerIso_scalar]
  change (unitPowerIso X n).hom ≫ scalarMap X _ (unitOfIso X φ ^ n : Γ(X, ⊤)ˣ) =
      (unitPowerIso X n).hom ≫ scalarMap X _ f ↔ _
  rw [cancel_epi]
  constructor
  · intro he
    have hi : AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _
        (unitOfIso X φ ^ n) =
        AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _ f :=
            Iso.ext he
    exact (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
        X).symm.injective hi
  · intro he
    rw [he]

/-- The root coordinate is the literal value at1 of the O-linear frame. -/
def unitCompatibleEquiv (X : Scheme.{u}) (n : ℕ) (f : Γ(X, ⊤)ˣ) :
    CompatibleFrame X (unitPair X n f) ≃ {a : Γ(X, ⊤)ˣ // a ^ n = f} where
  toFun φ := ⟨unitOfIso X φ.val, (unitPair_compatible_iff X n f φ.val).mp φ.property⟩
  invFun a := ⟨ScalarAutomorphisms.scalarIso X _ a.val, by
    apply (unitPair_compatible_iff X n f _).mpr
    have ha : unitOfIso X
        (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X
        (SheafOfModules.unit X.ringCatSheaf) a.val) = a.val :=
      (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
          X).right_inv a.val
    exact (congrArg (fun b => b ^ n) ha).trans a.property⟩
  left_inv φ := by
    apply Subtype.ext
    exact (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
        X).left_inv φ.val
  right_inv a := by
    apply Subtype.ext
    exact (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
        X).right_inv a.val


/-- Actual pair isomorphisms transport compatible frames contravariantly. -/
def compatibleFramePrecomp (X : Scheme.{u}) {n : ℕ} (P Q : Pair X n)
    (e : P.lineBundle.val ≅ Q.lineBundle.val)
    (he : (powerIso X e n).hom ≫ Q.trivialization.hom = P.trivialization.hom)
    (φ : CompatibleFrame X Q) : CompatibleFrame X P :=
  ⟨e ≪≫ φ.val, by
    rw [AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_trans X (N :=
        unitLineBundle X)]
    change (powerIso X e n).hom ≫ (powerIso X (M := unitLineBundle X) φ.val n).hom ≫
      (unitPowerIso X n).hom = P.trivialization.hom
    rw [φ.property, he]⟩

/-- Transport compatible frames along the specified line-bundle isomorphism that preserves
the chosen nth-power trivializations. -/
def compatibleFrameEquiv (X : Scheme.{u}) {n : ℕ} (P Q : Pair X n)
    (e : P.lineBundle.val ≅ Q.lineBundle.val)
    (he : (powerIso X e n).hom ≫ Q.trivialization.hom = P.trivialization.hom) :
    CompatibleFrame X P ≃ CompatibleFrame X Q where
  toFun := compatibleFramePrecomp X Q P e.symm (by
    rw [AlgebraicGeometry.Scheme.Modules.Invertible.UnitPower.powerIso_symm]
    exact (powerIso X e n).inv_comp_eq.mpr he.symm)
  invFun := compatibleFramePrecomp X P Q e he
  left_inv φ := by
    apply Subtype.ext
    apply Iso.ext
    change e.hom ≫ e.inv ≫ φ.val.hom = φ.val.hom
    rw [Iso.hom_inv_id_assoc]
  right_inv φ := by
    apply Subtype.ext
    apply Iso.ext
    change e.inv ≫ e.hom ≫ φ.val.hom = φ.val.hom
    rw [Iso.inv_hom_id_assoc]

open _root_.AlgebraicGeometry.Scheme.EtaleH1
open _root_.GroupCohomology.Kummer.Coefficients

/-- Literal root coordinates on the compatible frames of the pulled unit pair. -/
def rootSectionEquiv (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ)
    (U : X.Etaleᵒᵖ) :
    (torsor h X n hn hinv (unitPair X n f)).carrier.obj.obj U ≃
      {a : Γ(U.unop.left, ⊤)ˣ // a ^ n = Units.map U.unop.hom.appTop.hom.toMonoidHom f} :=
  (sectionsEquiv h X n hn hinv (unitPair X n f) U).trans
    ((compatibleFrameEquiv U.unop.left (pullbackPair U.unop.hom (unitPair X n f))
      (unitPair U.unop.left n (Units.map U.unop.hom.appTop.hom.toMonoidHom f))
      (pullbackUnitIso U.unop.hom) (unitPair_pullback U.unop.hom n f)).trans
        (unitCompatibleEquiv U.unop.left n (Units.map U.unop.hom.appTop.hom.toMonoidHom f)))

-- Keep the root-coordinate value rule; simpNF only normalizes implicit coefficient-map
-- coercions.
@[nolint simpNF, simp] theorem rootSectionEquiv_value (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ)
    (U : X.Etaleᵒᵖ) (s : (torsor h X n hn hinv (unitPair X n f)).carrier.obj.obj U) :
    (rootSectionEquiv h X n hn hinv f U s).val =
      unitOfIso U.unop.left ((pullbackUnitIso U.unop.hom).symm ≪≫
        (sectionsEquiv h X n hn hinv (unitPair X n f) U s).val) := rfl

/-- The O-linear root coordinate restricts by the actual ring map. -/
theorem unitFrameCoordinate_naturality {X Y Z : Scheme.{u}}
    (p : Y ⟶ X) (q : Z ⟶ X) (g : Z ⟶ Y) (w : g ≫ p = q)
    (φ : (Scheme.Modules.pullback p).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf) :
    unitOfIso Z ((pullbackUnitIso q).symm ≪≫
      nativePullFrame (unitLineBundle X) p q g w φ) =
      Units.map g.appTop.hom.toMonoidHom
        (unitOfIso Y ((pullbackUnitIso p).symm ≪≫ φ)) := by
  subst q
  have hi : (pullbackUnitIso (g ≫ p)).symm ≪≫
      nativePullFrame (unitLineBundle X) p (g ≫ p) g rfl φ =
    (pullbackUnitIso g).symm ≪≫ (Scheme.Modules.pullback g).mapIso
      ((pullbackUnitIso p).symm ≪≫ φ) ≪≫ pullbackUnitIso g := by
    apply Iso.ext
    change (pullbackUnitIso (g ≫ p)).inv ≫
      (Scheme.Modules.pullbackComp g p).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pullback g).map φ.hom ≫ (pullbackUnitIso g).hom = _
    have hu := congrArg Iso.inv (show pullbackUnitIso (g ≫ p) =
      ((Scheme.Modules.pullbackComp g p).app (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso (pullbackUnitIso p) ≪≫ pullbackUnitIso g from
      Iso.ext (Scheme.Modules.pullbackUnitIso_comp_inv g p).symm)
    simp only [Iso.trans_inv, Iso.symm_inv, CategoryTheory.Functor.mapIso_inv] at hu
    rw [hu]
    simp only [Category.assoc, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
      CategoryTheory.Functor.map_comp]
    have hcancel := Iso.hom_inv_id_assoc
      ((Scheme.Modules.pullbackComp g p).app (SheafOfModules.unit X.ringCatSheaf))
      ((Scheme.Modules.pullback g).map φ.hom ≫ (pullbackUnitIso g).hom)
    erw [hcancel]
  rw [hi]
  exact unitOfIso_pullback g _

/-- Literal roots restrict naturally on every small-etale test object. -/
theorem rootSectionEquiv_naturality (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ)
    {U V : X.Etaleᵒᵖ} (g : U ⟶ V)
    (s : (torsor h X n hn hinv (unitPair X n f)).carrier.obj.obj U) :
    (rootSectionEquiv h X n hn hinv f V
      ((torsor h X n hn hinv (unitPair X n f)).carrier.obj.map g s)).val =
      Units.map g.unop.left.appTop.hom.toMonoidHom (rootSectionEquiv h X n hn hinv f U s).val := by
  rw [rootSectionEquiv_value, sectionsEquiv_naturality, rootSectionEquiv_value]
  exact unitFrameCoordinate_naturality U.unop.hom V.unop.hom g.unop.left g.unop.w _

/-- The root coordinate has the positive mu_n action ζ*a. -/
theorem rootSectionEquiv_action (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ)
    (U : X.Etaleᵒᵖ) (ζ : (mu X n).obj.obj U)
    (s : (torsor h X n hn hinv (unitPair X n f)).carrier.obj.obj U) :
    (rootSectionEquiv h X n hn hinv f U ((torsor h X n hn hinv (unitPair X n f)).action U ζ
        s)).val =
      ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ) *
        (rootSectionEquiv h X n hn hinv f U s).val := by
  rw [rootSectionEquiv_value, sectionsEquiv_action, rootSectionEquiv_value]
  rw [← Iso.trans_assoc, unitOfIso_trans]
  have ha : unitOfIso U.unop.left
      (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso U.unop.left
      (SheafOfModules.unit U.unop.left.ringCatSheaf)
        ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ)) =
      ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ) :=
    (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv
        U.unop.left).right_inv _
  rw [ha, mul_comm]

/-- The sectionwise literal root coordinate identifies the actual sheaves. -/
def rootSheafIso (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ) :
    (torsor h X n hn hinv (unitPair X n f)).carrier ≅
      (GroupCohomology.Kummer.Torsor.rootTorsor
          GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv
          f).carrier :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U => ((rootSectionEquiv h X n hn hinv f U).trans
      (GroupCohomology.Kummer.Torsor.rootSectionsEquiv
          GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv
          f U).symm).toIso)
    (fun {U V} g => by
      ext s
      apply (GroupCohomology.Kummer.Torsor.rootSectionsEquiv
          GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv
          f V).injective
      apply Subtype.ext
      change (GroupCohomology.Kummer.Torsor.rootSectionsEquiv
          GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv f V
        ((GroupCohomology.Kummer.Torsor.rootSectionsEquiv
            GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn
            hinv f V).symm
          (rootSectionEquiv h X n hn hinv f V
            ((torsor h X n hn hinv (unitPair X n f)).carrier.obj.map g s)))).val = _
      rw [Equiv.apply_symm_apply]
      change (rootSectionEquiv h X n hn hinv f V
        ((torsor h X n hn hinv (unitPair X n f)).carrier.obj.map g s)).val =
        (GroupCohomology.Kummer.Torsor.rootSectionsEquiv
            GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv f V
          ((GroupCohomology.Kummer.Torsor.rootTorsor
              GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn
              hinv f).carrier.obj.map g
            ((GroupCohomology.Kummer.Torsor.rootSectionsEquiv
                GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn
                hinv f U).symm
              (rootSectionEquiv h X n hn hinv f U s)))).val
      rw [GroupCohomology.Kummer.Torsor.rootSections_naturality]
      rw [Equiv.apply_symm_apply]
      exact rootSectionEquiv_naturality h X n hn hinv f g s))

/-- The actual compatible-frame torsor is the existing positive root torsor. -/
def rootTorsorIso (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ) :
    Scheme.EtaleH1.Torsor.Iso (torsor h X n hn hinv (unitPair X n f))
      (GroupCohomology.Kummer.Torsor.rootTorsor
          GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv
          f) where
  carrierIso := rootSheafIso h X n hn hinv f
  equivariant U ζ s := by
    apply (GroupCohomology.Kummer.Torsor.rootSectionsEquiv
        GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv f
        U).injective
    apply Subtype.ext
    change (GroupCohomology.Kummer.Torsor.rootSectionsEquiv
        GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv f U
      ((GroupCohomology.Kummer.Torsor.rootSectionsEquiv
          GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv
          f U).symm
        (rootSectionEquiv h X n hn hinv f U ((torsor h X n hn hinv (unitPair X n f)).action U ζ
            s)))).val = _
    rw [Equiv.apply_symm_apply, GroupCohomology.Kummer.Torsor.rootSections_action]
    change (rootSectionEquiv h X n hn hinv f U ((torsor h X n hn hinv (unitPair X n f)).action
        U ζ s)).val =
      ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ) *
        (GroupCohomology.Kummer.Torsor.rootSectionsEquiv
            GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv f U
          ((GroupCohomology.Kummer.Torsor.rootSectionsEquiv
              GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn
              hinv f U).symm
            (rootSectionEquiv h X n hn hinv f U s))).val
    rw [Equiv.apply_symm_apply]
    exact rootSectionEquiv_action h X n hn hinv f U ζ s


/-- Normalized sections are inverses of positive frame coordinates. -/
def normalizedSectionEquiv (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ) (U : X.Etaleᵒᵖ) :
    (torsor h X n hn hinv (unitPair X n f)).carrier.obj.obj U ≃
      {s : Γ(U.unop.left, ⊤)ˣ // GroupCohomology.Kummer.Torsor.unitRestriction
          X f U * s ^ n = 1} :=
  (rootSectionEquiv h X n hn hinv f U).trans
    (GroupCohomology.Kummer.Torsor.inverseRootEquiv n
        (GroupCohomology.Kummer.Torsor.unitRestriction X f U))

/-- This inversion reverses the literal root action, as the normalized-section convention
requires. -/
theorem normalizedSectionEquiv_action (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ)
    (U : X.Etaleᵒᵖ) (ζ : (mu X n).obj.obj U)
    (s : (torsor h X n hn hinv (unitPair X n f)).carrier.obj.obj U) :
    (normalizedSectionEquiv h X n hn hinv f U
      ((torsor h X n hn hinv (unitPair X n f)).action U ζ s)).val =
      ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ)⁻¹ *
        (normalizedSectionEquiv h X n hn hinv f U s).val := by
  change (rootSectionEquiv h X n hn hinv f U
      ((torsor h X n hn hinv (unitPair X n f)).action U ζ s)).val⁻¹ = _
  rw [rootSectionEquiv_action, mul_inv]
  rfl

universe w

/-- The actual positive power-frame Ext class is the existing positive root class. -/
theorem torsorExtClass_unitPair (h :
    AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent.EtaleLineBundleDescent.{u}) (X :
    Scheme.{u})
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] :
    torsorExtClass (torsor h X n hn hinv (unitPair X n f)) =
      GroupCohomology.Kummer.Torsor.rootClass
          GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv f :=
  torsorExtClass_iso (rootTorsorIso h X n hn hinv f)

end AlgebraicGeometry.Scheme.Modules.Invertible.PowerRoot
