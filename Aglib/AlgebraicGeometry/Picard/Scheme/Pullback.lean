/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Presheaf.Pullback
public import Aglib.AlgebraicGeometry.Picard.BaseChangeGroupLaw
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Morphism
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Map
public import Aglib.AlgebraicGeometry.Picard.Comparison.SourcePullback
public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentBaseChangeMap

/-!
# Pullback on the supplied Picard representatives

An arbitrary morphism of schemes over the base induces a contravariant map
between the SAME supplied representatives of the fppf Picard sheaves. Its
formula is the already constructed whole presheaf/sheaf pullback. It preserves
the selected group laws and restricts to the original identity components
over a field. No flatness of the source morphism, rational origin or dual
geometry is used for these represented maps.

Classification remains restricted to locally Noetherian tests. The original
universal sheaf sections nevertheless satisfy a whole class equation on every
test scheme, obtained by naturality, without extending representability.

The actual universal-pair comparison additionally uses a locally Noetherian
base, proper flat geometrically integral source schemes, and the genuine
pointed equation. It uses the existing chosen universal pair for each supplied
representation and proves source, parameter and unit coherence on all tests.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

section Represented

variable {S : Scheme.{u}} {X Y Z : Over S}
  (PX : LocallyNoetherianOver S)
  (RX : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PX)
  (PY : LocallyNoetherianOver S)
  (RY : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf Y.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PY)
  (PZ : LocallyNoetherianOver S)
  (RZ : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf Z.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PZ)

/-- The actual contravariant map between the original supplied Picard
representatives, from the original whole fppf pullback morphism. -/
def picardPullback (f : X ⟶ Y) : PY.obj ⟶ PX.obj :=
  (LocallyNoetherianOver.representedMap (fppfPicardSheaf Y.hom).obj
    (fppfPicardSheaf X.hom).obj PY PX RY RX (fppfPicardPullback f).hom).hom

/-- The represented map has precisely the original source-pullback class
formula on the supplied locally Noetherian test category. -/
theorem homEquiv_comp_picardPullback (f : X ⟶ Y)
    {T : LocallyNoetherianOver S} (t : T.obj ⟶ PY.obj) :
    RX.homEquiv (ObjectProperty.homMk (t ≫ picardPullback PX RX PY RY f) : T ⟶ PX) =
      ((fppfPicardPullback f).hom.app (op T.obj)).hom
        (RY.homEquiv (ObjectProperty.homMk t : T ⟶ PY)) :=
  LocallyNoetherianOver.homEquiv_comp_representedMap (fppfPicardSheaf Y.hom).obj
    (fppfPicardSheaf X.hom).obj PY PX RY RX (fppfPicardPullback f).hom
    (ObjectProperty.homMk t)

/-- The original universal element determines the same represented map. -/
theorem homEquiv_picardPullback (f : X ⟶ Y) :
    RX.homEquiv (ObjectProperty.homMk (picardPullback PX RX PY RY f) : PY ⟶ PX) =
      ((fppfPicardPullback f).hom.app (op PY.obj)).hom (RY.homEquiv (𝟙 PY)) :=
  LocallyNoetherianOver.homEquiv_representedMap (fppfPicardSheaf Y.hom).obj
    (fppfPicardSheaf X.hom).obj PY PX RY RX (fppfPicardPullback f).hom

/-- The whole original universal-class equation on arbitrary test schemes,
including nonreduced and non-Noetherian ones. R is evaluated only at the two
original representing objects, which are locally Noetherian. -/
theorem universalFppfClass_picardPullback (f : X ⟶ Y) {T : Over S} (t : T ⟶ PY.obj) :
    ((fppfPicardSheaf X.hom).obj.map (t ≫ picardPullback PX RX PY RY f).op).hom
        (RX.homEquiv (𝟙 PX)) =
      ((fppfPicardPullback f).hom.app (op T)).hom
        (((fppfPicardSheaf Y.hom).obj.map t.op).hom (RY.homEquiv (𝟙 PY))) :=
  LocallyNoetherianOver.universalClass_comp_representedMap (fppfPicardSheaf Y.hom).obj
    (fppfPicardSheaf X.hom).obj PY PX RY RX (fppfPicardPullback f).hom t

/-- Uniqueness through the original supplied representation. -/
theorem picardPullback_unique (f : X ⟶ Y) (g : PY.obj ⟶ PX.obj)
    (hg : RX.homEquiv (ObjectProperty.homMk g : PY ⟶ PX) =
      ((fppfPicardPullback f).hom.app (op PY.obj)).hom (RY.homEquiv (𝟙 PY))) :
    g = picardPullback PX RX PY RY f := by
  have h := LocallyNoetherianOver.representedMap_unique (fppfPicardSheaf Y.hom).obj
    (fppfPicardSheaf X.hom).obj PY PX RY RX (fppfPicardPullback f).hom
    (ObjectProperty.homMk g) hg
  exact congrArg (fun q : PY ⟶ PX => q.hom) h

/-- Identity source pullback gives the original identity Picard map. -/
@[simp]
theorem picardPullback_id : picardPullback PX RX PX RX (𝟙 X) = 𝟙 PX.obj := by
  unfold picardPullback
  rw [fppfPicardPullback_id]
  exact congrArg (fun q : PX ⟶ PX => q.hom)
    (LocallyNoetherianOver.representedMap_id (fppfPicardSheaf X.hom).obj PX RX)

/-- Contravariant composition on the original representatives. -/
theorem picardPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    picardPullback PX RX PZ RZ (f ≫ g) =
      picardPullback PY RY PZ RZ g ≫ picardPullback PX RX PY RY f := by
  unfold picardPullback
  rw [fppfPicardPullback_comp]
  exact congrArg (fun q : PZ ⟶ PX => q.hom)
    (LocallyNoetherianOver.representedMap_comp (fppfPicardSheaf Z.hom).obj
      (fppfPicardSheaf Y.hom).obj (fppfPicardSheaf X.hom).obj PZ PY PX RZ RY RX
      (fppfPicardPullback g).hom (fppfPicardPullback f).hom)

section BaseChange

variable {S' : Scheme.{u}} [IsLocallyNoetherian S']
  [LocallyOfFiniteType PX.obj.hom] [LocallyOfFiniteType PY.obj.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole represented pullback map commutes with the original
base-change representatives and representations. The new base is merely
locally Noetherian and may be nonreduced; no flatness of f or of the base
change is required. -/
theorem picardPullback_baseChange (f : X ⟶ Y) (b : S' ⟶ S) :
    picardPullback (X := (Over.pullback b).obj X) (Y := (Over.pullback b).obj Y)
        (LocallyNoetherianOver.baseChange b PX)
        (baseChangeRepresentableBy X.hom b PX RX)
        (LocallyNoetherianOver.baseChange b PY)
        (baseChangeRepresentableBy Y.hom b PY RY) ((Over.pullback b).map f) =
      (Over.pullback b).map (picardPullback PX RX PY RY f) := by
  let PX' := LocallyNoetherianOver.baseChange b PX
  let PY' := LocallyNoetherianOver.baseChange b PY
  let RX' := baseChangeRepresentableBy X.hom b PX RX
  let RY' := baseChangeRepresentableBy Y.hom b PY RY
  let f' := (Over.pullback b).map f
  let m : PY.obj ⟶ PX.obj := picardPullback PX RX PY RY f
  let m' : PY'.obj ⟶ PX'.obj := picardPullback
    (X := (Over.pullback b).obj X) (Y := (Over.pullback b).obj Y) PX' RX' PY' RY' f'
  change m' = (Over.pullback b).map m
  let q : (Over.map b).obj PY'.obj ⟶ PY.obj :=
    ((Over.mapPullbackAdj b).homEquiv PY'.obj PY.obj).symm (𝟙 PY'.obj)
  let v := RY.homEquiv
    (ObjectProperty.homMk q : (LocallyNoetherianOver.map b).obj PY' ⟶ PY)
  have hq : ((Over.mapPullbackAdj b).homEquiv PY'.obj PX.obj).symm
      ((Over.pullback b).map m) = q ≫ m := by
    simpa only [Category.id_comp] using
      (Over.mapPullbackAdj b).homEquiv_naturality_right_symm (𝟙 PY'.obj) m
  have hy : RY'.homEquiv (𝟙 PY') =
      ((fppfPicardSheafBaseChangeIso Y.hom b).inv.app (op PY'.obj)).hom v :=
    baseChangeRepresentableBy_homEquiv Y.hom b PY RY (𝟙 PY')
  have hl : RX'.homEquiv (ObjectProperty.homMk m' : PY' ⟶ PX') =
      ((fppfPicardSheafBaseChangeIso X.hom b).inv.app (op PY'.obj)).hom
        (((fppfPicardPullback f).hom.app (op ((Over.map b).obj PY'.obj))).hom v) := by
    calc
      _ = ((fppfPicardPullback f').hom.app (op PY'.obj)).hom (RY'.homEquiv (𝟙 PY')) :=
        homEquiv_picardPullback (X := (Over.pullback b).obj X) (Y := (Over.pullback b).obj Y)
          PX' RX' PY' RY' f'
      _ = ((fppfPicardPullback f').hom.app (op PY'.obj)).hom
          (((fppfPicardSheafBaseChangeIso Y.hom b).inv.app (op PY'.obj)).hom v) :=
        congrArg ((fppfPicardPullback f').hom.app (op PY'.obj)).hom hy
      _ = _ := congrArg (fun a => (a.app (op PY'.obj)).hom v)
        (fppfPicardPullback_baseChange_inv f b)
  have hbase (n : PY.obj ⟶ PX.obj) :
      RX'.homEquiv (ObjectProperty.homMk ((Over.pullback b).map n) : PY' ⟶ PX') =
        ((fppfPicardSheafBaseChangeIso X.hom b).inv.app (op PY'.obj)).hom
          (RX.homEquiv (ObjectProperty.homMk
            (((Over.mapPullbackAdj b).homEquiv PY'.obj PX.obj).symm
              ((Over.pullback b).map n)) : (LocallyNoetherianOver.map b).obj PY' ⟶ PX)) := by
    exact baseChangeRepresentableBy_homEquiv X.hom b PX RX (T := PY')
      (ObjectProperty.homMk ((Over.pullback b).map n) : PY' ⟶ PX')
  have hr : RX'.homEquiv (ObjectProperty.homMk ((Over.pullback b).map m) : PY' ⟶ PX') =
      ((fppfPicardSheafBaseChangeIso X.hom b).inv.app (op PY'.obj)).hom
        (((fppfPicardPullback f).hom.app (op ((Over.map b).obj PY'.obj))).hom v) := by
    calc
      _ = ((fppfPicardSheafBaseChangeIso X.hom b).inv.app (op PY'.obj)).hom
          (RX.homEquiv (ObjectProperty.homMk
            (((Over.mapPullbackAdj b).homEquiv PY'.obj PX.obj).symm
              ((Over.pullback b).map m)) : (LocallyNoetherianOver.map b).obj PY' ⟶ PX)) :=
        hbase m
      _ = ((fppfPicardSheafBaseChangeIso X.hom b).inv.app (op PY'.obj)).hom
          (RX.homEquiv (ObjectProperty.homMk (q ≫ m) :
            (LocallyNoetherianOver.map b).obj PY' ⟶ PX)) := by rw [hq]
      _ = _ := congrArg ((fppfPicardSheafBaseChangeIso X.hom b).inv.app (op PY'.obj)).hom
        (homEquiv_comp_picardPullback PX RX PY RY f
          (T := (LocallyNoetherianOver.map b).obj PY') q)
  have h : (ObjectProperty.homMk m' : PY' ⟶ PX') =
      ObjectProperty.homMk ((Over.pullback b).map m) :=
    RX'.homEquiv.injective (hl.trans hr.symm)
  have hfinal := congrArg (fun a : PY' ⟶ PX' => a.hom) h
  exact hfinal

end BaseChange

section GroupLaw

variable [IsLocallyNoetherian S]
  [LocallyOfFiniteType PX.obj.hom] [LocallyOfFiniteType PY.obj.hom]

/-- The same Picard map preserves the original represented group structures.
The general transport supplies the unit and product equations, with their
actual locally finite-type tests. -/
theorem isMonHom_picardPullback (f : X ⟶ Y) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    IsMonHom (picardPullback PX RX PY RY f) :=
  LocallyNoetherianOver.isMonHom_representedMap (fppfPicardSheaf Y.hom).obj
    (fppfPicardSheaf X.hom).obj PY PX RY RX (fppfPicardPullback f).hom

/-- Bundle the same underlying Picard map in the existing group category. -/
def picardPullbackGroupHom (f : X ⟶ Y) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    Grp.mk PY.obj ⟶ Grp.mk PX.obj :=
  letI := picardCommGrpObj X.hom PX RX
  letI := picardCommGrpObj Y.hom PY RY
  letI := isMonHom_picardPullback PX RX PY RY f
  Grp.ofHom (picardPullback PX RX PY RY f)

/-- Bundling retains the original underlying morphism. -/
@[simp]
theorem picardPullbackGroupHom_hom_hom (f : X ⟶ Y) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    (picardPullbackGroupHom PX RX PY RY f).hom.hom = picardPullback PX RX PY RY f := rfl

/-- Identity coherence for the actual bundled group map. -/
@[simp]
theorem picardPullbackGroupHom_id :
    letI := picardCommGrpObj X.hom PX RX
    picardPullbackGroupHom PX RX PX RX (𝟙 X) = 𝟙 (Grp.mk PX.obj) := by
  let := picardCommGrpObj X.hom PX RX
  apply Grp.hom_ext
  exact picardPullback_id PX RX

variable [LocallyOfFiniteType PZ.obj.hom]

/-- Composition coherence for the same bundled group maps. -/
theorem picardPullbackGroupHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    letI := picardCommGrpObj Z.hom PZ RZ
    picardPullbackGroupHom PX RX PZ RZ (f ≫ g) =
      picardPullbackGroupHom PY RY PZ RZ g ≫ picardPullbackGroupHom PX RX PY RY f := by
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  let := picardCommGrpObj Z.hom PZ RZ
  apply Grp.hom_ext
  exact picardPullback_comp PX RX PY RY PZ RZ f g

end GroupLaw

section UniversalComparison

open Scheme.Modules.Invertible

variable [IsLocallyNoetherian S]
  [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
  [IsProper Y.hom] [Flat Y.hom] [GeometricallyIntegral Y.hom]
  (oX : 𝟙_ (Over S) ⟶ X) (oY : 𝟙_ (Over S) ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The universal comparison is a unique isomorphism between the actual
pullback of the ONE original pair on PX and source pullback of the ONE
original pair on PY. Classification is used only at the LN test PY. -/
theorem existsUnique_picardPullbackUniversalIso (f : X ⟶ Y) (hf : oX ≫ f = oY) :
    ∃! _e : RigidifiedPair.Iso
      (RigidifiedPair.map (picardPullback PX RX PY RY f)
        (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX))
      (RigidifiedPair.sourcePullback oX oY f hf
        (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY)), True := by
  let UY := fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY
  let Q := RigidifiedPair.sourcePullback oX oY f hf UY
  let m : PY ⟶ PX := ObjectProperty.homMk (picardPullback PX RX PY RY f)
  let Rr := rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral
    X.hom oX.left (Over.w oX) RX
  let E := rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral
    X.hom oX.left (Over.w oX)
  have hc : ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op PY.obj)).hom
      (classOf _ Q.bundle) = RX.homEquiv m := by
    calc
      _ = ((fppfPicardPullback f).hom.app (op PY.obj)).hom
          (((quotientProjection Y.hom ≫ toFppfPicardSheaf Y.hom).app (op PY.obj)).hom
            (classOf _ UY.bundle)) := sourcePullback_fppfClass oX oY f hf UY
      _ = ((fppfPicardPullback f).hom.app (op PY.obj)).hom (RY.homEquiv (𝟙 PY)) :=
        congrArg ((fppfPicardPullback f).hom.app (op PY.obj)).hom
          (fppfUniversalRigidifiedPair_fppfClass Y.hom oY.left (Over.w oY) RY)
      _ = _ := (homEquiv_picardPullback PX RX PY RY f).symm
  have hr : Rr.homEquiv m = Quotient.mk _ Q := by
    change E.inv.app (op PY.obj) (RX.homEquiv m) = Quotient.mk _ Q
    apply (E.app (op PY.obj)).toEquiv.injective
    calc
      _ = RX.homEquiv m := (E.app (op PY.obj)).toEquiv.apply_symm_apply _
      _ = _ := hc.symm.trans
        (rigidifiedPair_fppfClass X.hom oX.left (Over.w oX) Q).symm
  obtain ⟨e⟩ := (nonempty_universalRigidifiedPullbackIso_iff
    X.hom oX.left (Over.w oX) Rr m Q).mpr hr
  refine ⟨e, trivial, ?_⟩
  intro e' _
  exact RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    X.hom oX.left (Over.w oX) e' e

/-- The unique whole comparison at the original parameter scheme PY. -/
def picardPullbackUniversalIso (f : X ⟶ Y) (hf : oX ≫ f = oY) :
    RigidifiedPair.Iso
      (RigidifiedPair.map (picardPullback PX RX PY RY f)
        (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX))
      (RigidifiedPair.sourcePullback oX oY f hf
        (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY)) :=
  Classical.choose (existsUnique_picardPullbackUniversalIso PX RX PY RY oX oY f hf).exists

/-- The canonical universal-family comparison on every test scheme is the
actual pullback of the established universal comparison, with the original
source/parameter interchange. It makes no all-test representability claim. -/
def picardPullbackUniversalPullbackIso (f : X ⟶ Y) (hf : oX ≫ f = oY)
    {T : Over S} (t : T ⟶ PY.obj) :
    RigidifiedPair.Iso
      (RigidifiedPair.map (t ≫ picardPullback PX RX PY RY f)
        (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX))
      (RigidifiedPair.sourcePullback oX oY f hf (RigidifiedPair.map t
        (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY))) :=
  (RigidifiedPair.mapCompIso t (picardPullback PX RX PY RY f)
    (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX)).trans
      ((RigidifiedPair.Iso.map t (picardPullbackUniversalIso PX RX PY RY oX oY f hf)).trans
        (RigidifiedPair.sourcePullbackParameterIso oX oY f hf t
          (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY)))

/-- The all-test universal comparison is unique under the ACTUAL proper,
flat, geometrically integral source data. No additional O-connectedness or
comparison premise is left to the native consumer. -/
theorem picardPullbackUniversalPullbackIso_unique (f : X ⟶ Y) (hf : oX ≫ f = oY)
    {T : Over S} (t : T ⟶ PY.obj)
    (e : RigidifiedPair.Iso
      (RigidifiedPair.map (t ≫ picardPullback PX RX PY RY f)
        (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX))
      (RigidifiedPair.sourcePullback oX oY f hf (RigidifiedPair.map t
        (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY)))) :
    e = picardPullbackUniversalPullbackIso PX RX PY RY oX oY f hf t :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    X.hom oX.left (Over.w oX) _ _

/-- Naturality of the actual universal comparison on arbitrary parameter
schemes, with all original pullback comparison arrows displayed. -/
theorem picardPullbackUniversalPullbackIso_naturality
    (f : X ⟶ Y) (hf : oX ≫ f = oY) {T T' : Over S} (a : T' ⟶ T) (t : T ⟶ PY.obj) :
    (picardPullbackUniversalPullbackIso PX RX PY RY oX oY f hf (a ≫ t)).trans
        (RigidifiedPair.Iso.sourcePullback oX oY f hf
          (RigidifiedPair.mapCompIso a t
            (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY))) =
      (RigidifiedPair.mapCongrIso (Category.assoc a t (picardPullback PX RX PY RY f))
        (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX)).trans
        ((RigidifiedPair.mapCompIso a (t ≫ picardPullback PX RX PY RY f)
          (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX)).trans
          ((RigidifiedPair.Iso.map a
            (picardPullbackUniversalPullbackIso PX RX PY RY oX oY f hf t)).trans
            (RigidifiedPair.sourcePullbackParameterIso oX oY f hf a
              (RigidifiedPair.map t
                (fppfUniversalRigidifiedPair Y.hom oY.left (Over.w oY) RY))))) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    X.hom oX.left (Over.w oX) _ _

/-- Source identity coherence uses the existing identity comparison and
the proved identity of the same represented map. -/
theorem picardPullbackUniversalPullbackIso_id {T : Over S} (t : T ⟶ PX.obj) :
    picardPullbackUniversalPullbackIso PX RX PX RX oX oX (𝟙 X) (Category.comp_id oX) t =
      (RigidifiedPair.mapCongrIso
        (show t ≫ picardPullback PX RX PX RX (𝟙 X) = t by
          rw [picardPullback_id, Category.comp_id])
        (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX)).trans
        (RigidifiedPair.sourcePullbackIdIso oX
          (RigidifiedPair.map t
            (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX))).symm :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    X.hom oX.left (Over.w oX) _ _

section UnitNormalization

variable [LocallyOfFiniteType PX.obj.hom] [LocallyOfFiniteType PY.obj.hom]

/-- The actual universal comparison preserves the original parameter-unit
normalizations, including the original source pullback of the trivial pair.
Every condition follows from the original source geometry and represented
group laws; no additional coherence hypothesis is supplied by the consumer. -/
theorem picardPullbackUniversalPullbackIso_unit (f : X ⟶ Y) (hf : oX ≫ f = oY)
    (T : Over S) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    letI := isMonHom_picardPullback PX RX PY RY f
    (picardPullbackUniversalPullbackIso PX RX PY RY oX oY f hf (1 : T ⟶ PY.obj)).trans
        ((RigidifiedPair.Iso.sourcePullback oX oY f hf
          (fppfUniversalRigidifiedUnitIso Y.hom oY.left (Over.w oY) RY T)).trans
          (RigidifiedPair.sourcePullbackTrivialIso oX oY f hf T)) =
      (RigidifiedPair.mapCongrIso (MonObj.one_comp (picardPullback PX RX PY RY f))
        (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX)).trans
          (fppfUniversalRigidifiedUnitIso X.hom oX.left (Over.w oX) RX T) := by
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  let := isMonHom_picardPullback PX RX PY RY f
  exact RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    X.hom oX.left (Over.w oX) _ _

end UnitNormalization

variable [IsProper Z.hom] [Flat Z.hom] [GeometricallyIntegral Z.hom]
  (oZ : 𝟙_ (Over S) ⟶ Z)

/-- Source composition coherence for the same three universal pairs and
the same three supplied representations. -/
theorem picardPullbackUniversalPullbackIso_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : oX ≫ f = oY) (hg : oY ≫ g = oZ)
    {T : Over S} (t : T ⟶ PZ.obj) :
    (picardPullbackUniversalPullbackIso PX RX PZ RZ oX oZ (f ≫ g)
      (by rw [← Category.assoc, hf, hg]) t).trans
      (RigidifiedPair.sourcePullbackCompIso oX oY oZ f g hf hg
        (RigidifiedPair.map t (fppfUniversalRigidifiedPair Z.hom oZ.left (Over.w oZ) RZ))) =
      (RigidifiedPair.mapCongrIso
        (show t ≫ picardPullback PX RX PZ RZ (f ≫ g) =
            (t ≫ picardPullback PY RY PZ RZ g) ≫ picardPullback PX RX PY RY f by
          rw [picardPullback_comp PX RX PY RY PZ RZ f g, Category.assoc])
        (fppfUniversalRigidifiedPair X.hom oX.left (Over.w oX) RX)).trans
        ((picardPullbackUniversalPullbackIso PX RX PY RY oX oY f hf
          (t ≫ picardPullback PY RY PZ RZ g)).trans
          (RigidifiedPair.Iso.sourcePullback oX oY f hf
            (picardPullbackUniversalPullbackIso PY RY PZ RZ oY oZ g hg t))) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    X.hom oX.left (Over.w oX) _ _

end UniversalComparison

end Represented

section IdentityComponents

open Scheme.Group

variable {k : Type u} [Field k] {X Y Z : Over (Spec (.of k))}
  (PX : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PX.obj.hom]
  (RX : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PX)
  (PY : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PY.obj.hom]
  (RY : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf Y.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PY)
  (PZ : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType PZ.obj.hom]
  (RZ : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf Z.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy PZ)

/-- The original Picard pullback restricted to the actual original identity
components. It needs no origin on X or Y and no properness or smoothness of
either Picard component. -/
def picardIdentityComponentPullback (f : X ⟶ Y) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    identityComponentOver PY.obj ⟶ identityComponentOver PX.obj :=
  letI := picardCommGrpObj X.hom PX RX
  letI := picardCommGrpObj Y.hom PY RY
  letI := isMonHom_picardPullback PX RX PY RY f
  identityComponentMap (picardPullback PX RX PY RY f) (IsMonHom.one_hom _)

/-- The whole inclusion equation retains the original representative map. -/
@[reassoc (attr := simp)]
theorem picardIdentityComponentPullback_ι (f : X ⟶ Y) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    picardIdentityComponentPullback PX RX PY RY f ≫ identityComponentι PX.obj =
      identityComponentι PY.obj ≫ picardPullback PX RX PY RY f := by
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  let := isMonHom_picardPullback PX RX PY RY f
  exact identityComponentMap_ι _ _

/-- The restricted original map preserves the original component group laws. -/
theorem isMonHom_picardIdentityComponentPullback (f : X ⟶ Y) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    IsMonHom (picardIdentityComponentPullback PX RX PY RY f) := by
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  let := isMonHom_picardPullback PX RX PY RY f
  change IsMonHom (identityComponentMap (picardPullback PX RX PY RY f) (IsMonHom.one_hom _))
  infer_instance

/-- The actual unit section is preserved, as a whole scheme-map equation. -/
@[reassoc]
theorem picardIdentityComponentPullback_pointed (f : X ⟶ Y) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    η[identityComponentOver PY.obj] ≫ picardIdentityComponentPullback PX RX PY RY f =
      η[identityComponentOver PX.obj] := by
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  let := isMonHom_picardIdentityComponentPullback PX RX PY RY f
  exact IsMonHom.one_hom _

/-- Identity coherence on the same original Picard component. -/
@[simp]
theorem picardIdentityComponentPullback_id :
    letI := picardCommGrpObj X.hom PX RX
    picardIdentityComponentPullback PX RX PX RX (𝟙 X) = 𝟙 (identityComponentOver PX.obj) := by
  let := picardCommGrpObj X.hom PX RX
  apply (cancel_mono (identityComponentι PX.obj)).mp
  rw [picardIdentityComponentPullback_ι, picardPullback_id, Category.comp_id, Category.id_comp]

/-- Contravariant composition on the actual original components. -/
theorem picardIdentityComponentPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    letI := picardCommGrpObj Z.hom PZ RZ
    picardIdentityComponentPullback PX RX PZ RZ (f ≫ g) =
      picardIdentityComponentPullback PY RY PZ RZ g ≫
        picardIdentityComponentPullback PX RX PY RY f := by
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  let := picardCommGrpObj Z.hom PZ RZ
  apply (cancel_mono (identityComponentι PX.obj)).mp
  rw [picardIdentityComponentPullback_ι, Category.assoc,
    picardIdentityComponentPullback_ι, picardIdentityComponentPullback_ι_assoc,
    picardPullback_comp PX RX PY RY PZ RZ f g]

/-- The same original represented class formula for points of Pic0 on
locally Noetherian tests. No representative for a new Pic0 model is introduced. -/
theorem homEquiv_comp_picardIdentityComponentPullback (f : X ⟶ Y)
    {T : LocallyNoetherianOver (Spec (.of k))} :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    ∀ t : T.obj ⟶ identityComponentOver PY.obj,
      RX.homEquiv (ObjectProperty.homMk
        ((t ≫ picardIdentityComponentPullback PX RX PY RY f) ≫ identityComponentι PX.obj) :
          T ⟶ PX) =
        ((fppfPicardPullback f).hom.app (op T.obj)).hom
          (RY.homEquiv (ObjectProperty.homMk (t ≫ identityComponentι PY.obj) : T ⟶ PY)) := by
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  intro t
  rw [Category.assoc, picardIdentityComponentPullback_ι, ← Category.assoc]
  exact homEquiv_comp_picardPullback PX RX PY RY f (t ≫ identityComponentι PY.obj)

/-- The original universal-class equation for Pic0 maps on every test
scheme. Only the original universal sections use the representation data. -/
theorem universalFppfClass_picardIdentityComponentPullback (f : X ⟶ Y)
    {T : Over (Spec (.of k))} :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    ∀ t : T ⟶ identityComponentOver PY.obj,
      ((fppfPicardSheaf X.hom).obj.map
        ((t ≫ picardIdentityComponentPullback PX RX PY RY f) ≫
          identityComponentι PX.obj).op).hom (RX.homEquiv (𝟙 PX)) =
        ((fppfPicardPullback f).hom.app (op T)).hom
          (((fppfPicardSheaf Y.hom).obj.map (t ≫ identityComponentι PY.obj).op).hom
            (RY.homEquiv (𝟙 PY))) := by
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  intro t
  rw [Category.assoc, picardIdentityComponentPullback_ι, ← Category.assoc]
  exact universalFppfClass_picardPullback PX RX PY RY f (t ≫ identityComponentι PY.obj)

/-- Bundle the same restricted map in the existing category of group schemes. -/
def picardIdentityComponentPullbackGroupHom (f : X ⟶ Y) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    Grp.mk (identityComponentOver PY.obj) ⟶ Grp.mk (identityComponentOver PX.obj) :=
  letI := picardCommGrpObj X.hom PX RX
  letI := picardCommGrpObj Y.hom PY RY
  letI := isMonHom_picardIdentityComponentPullback PX RX PY RY f
  Grp.ofHom (picardIdentityComponentPullback PX RX PY RY f)

/-- The bundled component map has the unchanged underlying morphism. -/
@[simp]
theorem picardIdentityComponentPullbackGroupHom_hom_hom (f : X ⟶ Y) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    (picardIdentityComponentPullbackGroupHom PX RX PY RY f).hom.hom =
      picardIdentityComponentPullback PX RX PY RY f := rfl

/-- Identity coherence for the same bundled component group. -/
@[simp]
theorem picardIdentityComponentPullbackGroupHom_id :
    letI := picardCommGrpObj X.hom PX RX
    picardIdentityComponentPullbackGroupHom PX RX PX RX (𝟙 X) =
      𝟙 (Grp.mk (identityComponentOver PX.obj)) := by
  let := picardCommGrpObj X.hom PX RX
  apply Grp.hom_ext
  exact picardIdentityComponentPullback_id PX RX

/-- Composition coherence for the actual bundled Pic0 maps. -/
theorem picardIdentityComponentPullbackGroupHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    letI := picardCommGrpObj Z.hom PZ RZ
    picardIdentityComponentPullbackGroupHom PX RX PZ RZ (f ≫ g) =
      picardIdentityComponentPullbackGroupHom PY RY PZ RZ g ≫
        picardIdentityComponentPullbackGroupHom PX RX PY RY f := by
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  let := picardCommGrpObj Z.hom PZ RZ
  apply Grp.hom_ext
  exact picardIdentityComponentPullback_comp PX RX PY RY PZ RZ f g

variable (K : Type u) [Field K] [Algebra k K]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The existing canonical component base-change isomorphism has the
original inclusion triangle, in addition to its structure-map triangle.
No new component or comparison isomorphism is chosen. -/
@[reassoc]
theorem picardIdentityComponentBaseChangeIso_hom_ι :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj (pullback.snd X.hom b)
      (LocallyNoetherianOver.baseChange b PX) (baseChangeRepresentableBy X.hom b PX RX)
    (picardIdentityComponentBaseChangeIso X.hom PX RX K).hom ≫
        (identityComponentι (LocallyNoetherianOver.baseChange b PX).obj).left =
      ((Over.pullback b).map (identityComponentι PX.obj)).left := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj (pullback.snd X.hom b)
    (LocallyNoetherianOver.baseChange b PX) (baseChangeRepresentableBy X.hom b PX RX)
  change
    (((isPullback_preimage_identityComponent PX.obj K).isoPullback.inv ≫
        (Scheme.isoOfEq (pullback PX.obj.hom b)
          (identityComponent_pullback PX.obj K).symm).hom) ≫
      (Scheme.isoOfEq ((Over.pullback b).obj PX.obj).left
        ((picardIdentityComponent_pullback X.hom PX RX K).trans
          (identityComponent_baseChangeRepresentableBy X.hom PX RX K).symm)).hom) ≫
      (identityComponent (LocallyNoetherianOver.baseChange b PX).obj).ι =
        ((Over.pullback b).map (identityComponentι PX.obj)).left
  have h₂ := Scheme.isoOfEq_hom_ι ((Over.pullback b).obj PX.obj).left
    ((picardIdentityComponent_pullback X.hom PX RX K).trans
      (identityComponent_baseChangeRepresentableBy X.hom PX RX K).symm)
  have h₁ := Scheme.isoOfEq_hom_ι (pullback PX.obj.hom b)
    (identityComponent_pullback PX.obj K).symm
  simp only [Category.assoc]
  rw [h₂, h₁]
  apply pullback.hom_ext
  · rw [Category.assoc, ← morphismRestrict_ι]
    rw [← Category.assoc, (isPullback_preimage_identityComponent PX.obj K).isoPullback_inv_fst]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc]
    exact (isPullback_preimage_identityComponent PX.obj K).isoPullback_inv_snd.trans
      (pullback.lift_snd _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback on the actual Picard components commutes with field extension
through the EXISTING canonical component comparison isomorphisms. This is
a whole scheme-map square, with the same base-changed representatives/R. -/
theorem picardIdentityComponentPullback_baseChange (f : X ⟶ Y) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    letI := picardCommGrpObj X.hom PX RX
    letI := picardCommGrpObj Y.hom PY RY
    letI := picardCommGrpObj (pullback.snd X.hom b)
      (LocallyNoetherianOver.baseChange b PX) (baseChangeRepresentableBy X.hom b PX RX)
    letI := picardCommGrpObj (pullback.snd Y.hom b)
      (LocallyNoetherianOver.baseChange b PY) (baseChangeRepresentableBy Y.hom b PY RY)
    ((Over.pullback b).map (picardIdentityComponentPullback PX RX PY RY f)).left ≫
        (picardIdentityComponentBaseChangeIso X.hom PX RX K).hom =
      (picardIdentityComponentBaseChangeIso Y.hom PY RY K).hom ≫
        (picardIdentityComponentPullback
          (X := (Over.pullback b).obj X) (Y := (Over.pullback b).obj Y)
          (LocallyNoetherianOver.baseChange b PX) (baseChangeRepresentableBy X.hom b PX RX)
          (LocallyNoetherianOver.baseChange b PY) (baseChangeRepresentableBy Y.hom b PY RY)
          ((Over.pullback b).map f)).left := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let PX' := LocallyNoetherianOver.baseChange b PX
  let PY' := LocallyNoetherianOver.baseChange b PY
  let RX' := baseChangeRepresentableBy X.hom b PX RX
  let RY' := baseChangeRepresentableBy Y.hom b PY RY
  let := picardCommGrpObj X.hom PX RX
  let := picardCommGrpObj Y.hom PY RY
  let := picardCommGrpObj (pullback.snd X.hom b) PX' RX'
  let := picardCommGrpObj (pullback.snd Y.hom b) PY' RY'
  have hmap : ((Over.pullback b).map (picardIdentityComponentPullback PX RX PY RY f)).left ≫
        ((Over.pullback b).map (identityComponentι PX.obj)).left =
      ((Over.pullback b).map (identityComponentι PY.obj)).left ≫
        ((Over.pullback b).map (picardPullback PX RX PY RY f)).left := by
    have h := congrArg (fun a => (Over.pullback b).map a)
      (picardIdentityComponentPullback_ι PX RX PY RY f)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact congrArg (fun a => a.left) h
  have hfactor := congrArg (fun a => a.left)
    (picardIdentityComponentPullback_ι
      (X := (Over.pullback b).obj X) (Y := (Over.pullback b).obj Y)
      PX' RX' PY' RY' ((Over.pullback b).map f))
  have hbase := congrArg (fun a => a.left) (picardPullback_baseChange PX RX PY RY f b)
  apply (cancel_mono (identityComponentι PX'.obj).left).mp
  calc
    _ = ((Over.pullback b).map (picardIdentityComponentPullback PX RX PY RY f)).left ≫
        ((Over.pullback b).map (identityComponentι PX.obj)).left := by
      rw [Category.assoc, picardIdentityComponentBaseChangeIso_hom_ι PX RX K]
    _ = ((Over.pullback b).map (identityComponentι PY.obj)).left ≫
        ((Over.pullback b).map (picardPullback PX RX PY RY f)).left := hmap
    _ = ((picardIdentityComponentBaseChangeIso Y.hom PY RY K).hom ≫
          (identityComponentι PY'.obj).left) ≫
        (picardPullback (X := (Over.pullback b).obj X) (Y := (Over.pullback b).obj Y)
          PX' RX' PY' RY' ((Over.pullback b).map f)).left := by
      rw [picardIdentityComponentBaseChangeIso_hom_ι PY RY K, hbase]
    _ = _ := by
      simp only [Over.comp_left] at hfactor
      simp only [Category.assoc]
      rw [hfactor]

end IdentityComponents

end AlgebraicGeometry.Scheme.RelativePicard
