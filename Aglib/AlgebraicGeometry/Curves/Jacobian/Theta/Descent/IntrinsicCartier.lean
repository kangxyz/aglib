/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.PositiveAbelBaseChange
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IntrinsicCartier.Whole
public import Aglib.AlgebraicGeometry.Curves.Genus.BaseChange
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.QuasiCompactSeparated
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.SchematicImage
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Descent
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.LineBundleBaseChange
public import Aglib.CategoryTheory.Comma.Over.PullbackMap

/-!
# The original theta divisor over the ground field

The original positive ordered Abel map commutes with scalar extension.
Flat base change preserves its actual schematic image. The whole Picard
image is Cartier over the algebraic closure, so its original ideal is
Cartier over the ground field by fpqc descent. The line bundle is on the
original Picard scheme; translation to the Jacobian uses degree data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The original schematic image of the positive ordered Abel map commutes
with any field extension on the same Picard representatives. -/
theorem exists_isPullback_positiveAbelImage_fieldBaseChange
    (K : Type u) [Field K] [Algebra k K] (n : ℕ) :
    let b := Spec.algebraMap k K
    let XK := fieldBaseChange K X
    let PK := LocallyNoetherianOver.baseChange b P
    let RK := baseChangeRepresentableBy X.hom b P R
    let hXK := curveProperties_baseChange hX K b
    letI := hX.smooth
    letI := hX.proper
    letI := hXK.smooth
    letI := hXK.proper
    let f := (positiveAbelMorphism X P R n).hom.left
    let fK := (positiveAbelMorphism XK PK RK n).hom.left
    ∃ a, IsPullback a fK.imageι f.imageι (pullback.fst P.obj.hom b) := by
  let b : Spec (.of K) ⟶ Base k := Spec.algebraMap k K
  let XK : FScheme K := fieldBaseChange K X
  let PK := LocallyNoetherianOver.baseChange b P
  let RK := baseChangeRepresentableBy X.hom b P R
  let hXK := curveProperties_baseChange hX K b
  let := hX.smooth
  let := hX.proper
  let := hXK.smooth
  let := hXK.proper
  let Y := parameter X.hom n
  let YK := parameter XK.hom n
  let f : Y ⟶ P.obj := (positiveAbelMorphism X P R n).hom
  let fK : YK ⟶ PK.obj := (positiveAbelMorphism XK PK RK n).hom
  let e : YK ≅ (Over.pullback b).obj Y := parameterBaseChangeIso X.hom b n
  let p : ((Over.pullback b).obj Y).left ⟶ Y.left := pullback.fst Y.hom b
  let q : PK.obj.left ⟶ P.obj.left := pullback.fst P.obj.hom b
  let r : YK.left ⟶ ((Over.pullback b).obj Y).left := e.hom.left
  let v : ((Over.pullback b).obj Y).left ⟶ PK.obj.left := ((Over.pullback b).map f).left
  have hmap : e.hom ≫ (Over.pullback b).map f = fK :=
    positiveAbelMorphism_baseChange hX K P R n
  have hmapLeft : r ≫ v = fK.left :=
    congrArg Over.Hom.left hmap
  have H : IsPullback p v f.left q := Over.isPullback_map_left b f
  have : IsIso r := by
    change IsIso ((Over.forget (Base K)).map e.hom)
    infer_instance
  have He : IsPullback r fK.left v (𝟙 PK.obj.left) :=
    IsPullback.of_horiz_isIso_mono ⟨hmapLeft.trans (Category.comp_id fK.left).symm⟩
  have HK : IsPullback (r ≫ p) fK.left f.left q := by
    simpa only [Category.id_comp] using He.paste_horiz H
  let : IsProper f.left := isProper_positiveAbelMorphism X P R n
  let : Flat q := inferInstanceAs (Flat (pullback.fst P.obj.hom b))
  exact ⟨_, (Hom.isPullback_imageι_of_isPullback_of_flat f.left q HK).flip⟩

/-- The actual positive theta image is effective Cartier on the original
Picard scheme over every field, with no choice of a rational origin. -/
theorem isEffectiveCartier_positiveAbelImage_of_posGenus (hg : 0 < coherentGenus k X) :
    letI := hX.smooth
    letI := hX.proper
    Hom.IsEffectiveCartier
      (positiveAbelMorphism X P R (coherentGenus k X - 1)).hom.left.imageι := by
  let := hX.smooth
  let := hX.proper
  let n := coherentGenus k X - 1
  let K := AlgebraicClosure k
  let b : Spec (.of K) ⟶ Base k := Spec.algebraMap k K
  let XK : FScheme K := Over.mk (pullback.snd X.hom b)
  let PK := LocallyNoetherianOver.baseChange b P
  let RK := baseChangeRepresentableBy X.hom b P R
  let hXK := curveProperties_baseChange hX K b
  let := hXK.smooth
  let := hXK.proper
  let : LocallyOfFiniteType PK.obj.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd P.obj.hom b))
  let : IsSeparated PK.obj.hom := inferInstanceAs (IsSeparated (pullback.snd P.obj.hom b))
  let f := (positiveAbelMorphism X P R n).hom.left
  let fK := (positiveAbelMorphism XK PK RK n).hom.left
  let q : PK.obj.left ⟶ P.obj.left := pullback.fst P.obj.hom b
  obtain ⟨a, H⟩ := exists_isPullback_positiveAbelImage_fieldBaseChange hX P R K n
  have : Surjective b := ⟨Function.surjective_to_subsingleton b⟩
  have : Flat q := inferInstanceAs (Flat (pullback.fst P.obj.hom b))
  have : Surjective q := inferInstanceAs (Surjective (pullback.fst P.obj.hom b))
  have : QuasiCompact q := inferInstanceAs (QuasiCompact (pullback.fst P.obj.hom b))
  have hgen : coherentGenus K (Over.mk (pullback.snd X.hom b)) = coherentGenus k X :=
    coherentGenus_arbitraryBaseChange properStructureCohomologyBaseChange X hX K b
  have hThetaK : Hom.IsEffectiveCartier fK.imageι := by
    have h := isEffectiveCartier_positiveAbelImage_of_isAlgClosed hXK PK RK (hgen.symm ▸ hg)
    rw [hgen] at h
    exact h
  exact Hom.isEffectiveCartier_of_fpqc_pullback f.imageι fK.imageι a q H hThetaK

/-- The positive line bundle of the original theta divisor on the original
Picard scheme over the ground field. -/
def intrinsicThetaLineBundleOnPicard (hg : 0 < coherentGenus k X) : LineBundle P.obj.left :=
  dualLineBundle _ (isEffectiveCartier_positiveAbelImage_of_posGenus hX P R hg).idealLineBundle

/-- Pullback of the positive theta class along any extension of the ground
field, on the original whole Picard schemes. -/
theorem pullbackClass_intrinsicThetaLineBundleOnPicard_fieldBaseChange
    (K : Type u) [Field K] [Algebra k K] (hg : 0 < coherentGenus k X) :
    let b := Spec.algebraMap k K
    let XK := fieldBaseChange K X
    let PK := LocallyNoetherianOver.baseChange b P
    let RK := baseChangeRepresentableBy X.hom b P R
    let hXK := curveProperties_baseChange hX K b
    letI : LocallyOfFiniteType PK.obj.hom := inferInstanceAs
      (LocallyOfFiniteType (pullback.snd P.obj.hom b))
    letI : IsSeparated PK.obj.hom := inferInstanceAs (IsSeparated (pullback.snd P.obj.hom b))
    let hgK : 0 < coherentGenus K XK :=
      (coherentGenus_arbitraryBaseChange properStructureCohomologyBaseChange X hX K b).symm ▸ hg
    pullbackClass (pullback.fst P.obj.hom b)
        (classOf P.obj.left (intrinsicThetaLineBundleOnPicard hX P R hg)) =
      classOf PK.obj.left (intrinsicThetaLineBundleOnPicard hXK PK RK hgK) := by
  let b := Spec.algebraMap k K
  let XK := fieldBaseChange K X
  let PK := LocallyNoetherianOver.baseChange b P
  let RK := baseChangeRepresentableBy X.hom b P R
  let hXK := curveProperties_baseChange hX K b
  let q : PK.obj.left ⟶ P.obj.left := pullback.fst P.obj.hom b
  let : LocallyOfFiniteType PK.obj.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd P.obj.hom b))
  let : IsSeparated PK.obj.hom := inferInstanceAs (IsSeparated (pullback.snd P.obj.hom b))
  let : Flat q := inferInstanceAs (Flat (pullback.fst P.obj.hom b))
  let := hX.smooth
  let := hX.proper
  let := hXK.smooth
  let := hXK.proper
  have hgen : coherentGenus K XK = coherentGenus k X :=
    coherentGenus_arbitraryBaseChange properStructureCohomologyBaseChange X hX K b
  let hgK : 0 < coherentGenus K XK := hgen.symm ▸ hg
  let i := (positiveAbelMorphism X P R (coherentGenus k X - 1)).hom.left.imageι
  let j (n : ℕ) := (positiveAbelMorphism XK PK RK n).hom.left.imageι
  have hex : ∃ a, IsPullback a (j (coherentGenus K XK - 1)) i q := by
    rw [hgen]
    exact exists_isPullback_positiveAbelImage_fieldBaseChange hX P R K (coherentGenus k X - 1)
  obtain ⟨a, H⟩ := hex
  exact Hom.pullbackClass_positiveCartier_of_isPullback_of_flat i _ a q H
    (isEffectiveCartier_positiveAbelImage_of_posGenus hX P R hg)
    (isEffectiveCartier_positiveAbelImage_of_posGenus hXK PK RK hgK)

end AlgebraicGeometry.Scheme.OverField.Curve
