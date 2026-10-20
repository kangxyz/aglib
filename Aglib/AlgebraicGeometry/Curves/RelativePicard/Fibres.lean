/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RelativePicard.DegreeZero
public import Aglib.AlgebraicGeometry.Curves.Genus.BaseChange
public import Aglib.AlgebraicGeometry.Curves.LineBundleDegree.Isomorphism
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# Actual iterated geometric fibres of the curve family

The pinned pullback-pasting isomorphism identifies (X × T) ×_T Spec K with
X × Spec K for every test scheme T and every structural map Spec K → T.
The actual family-map square is proved, then genuine curve properties,
coherent genus and C's actual line-bundle degree are transported through it.
No point-set or numerical substitute and no new theorem family are used.
Degree transport has the existing explicit norm/order family; genus transport
has the existing explicit proper structure-cohomology base-change family.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen SmoothClosedPointDimension SmoothFieldDimension SmoothFieldNormality
    SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
variable {F : Type u} [Field F]
theorem curveProperties_iso {X Y : FScheme F} (e : X ≅ Y) (hY : Properties Y) :
    Properties X := by
  letI := hY.smooth
  letI := hY.proper
  letI := hY.connected
  letI := SmoothOfRelativeDimension.smooth 1 Y.hom
  constructor
  · rw [← Over.w e.hom]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (e.hom.left ≫ Y.hom))
  · rw [← Over.w e.hom]
    infer_instance
  · rw [← Over.w e.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)
      e.hom.left Y.hom).mpr hY.connected
end AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.RelativePicard
universe u
open AlgebraicGeometry.Scheme.Hom
variable {F : Type u} [Field F] (X : FScheme F) (T : FScheme F)
variable (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left)
def familyFibreIso :
    Over.mk (pullback.snd (pullback.snd X.hom T.hom) t) ≅
      Over.mk (pullback.snd X.hom (t ≫ T.hom)) :=
  Over.isoMk (pullbackLeftPullbackSndIso X.hom T.hom t)
    (pullbackLeftPullbackSndIso_hom_snd X.hom T.hom t)

@[reassoc] theorem familyFibreIso_familyMap :
    (familyFibreIso X T K t).hom.left ≫ familyMap X.hom T.hom (t ≫ T.hom) t rfl =
      pullback.fst (pullback.snd X.hom T.hom) t := by
  dsimp only [familyFibreIso, Over.isoMk_hom_left]
  apply pullback.hom_ext
  · simp only [Category.assoc, familyMap_fst,
      pullbackLeftPullbackSndIso_hom_fst]
  · simp only [Category.assoc, familyMap_snd,
      pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

theorem familyFibre_curveProperties (hX : Properties X) :
    Properties (Over.mk (pullback.snd (pullback.snd X.hom T.hom) t)) :=
  curveProperties_iso (familyFibreIso X T K t)
    (curveProperties_baseChange hX K (t ≫ T.hom))

theorem familyFibre_genus (hbase : Scheme.Cohomology.ProperStructureCohomologyBaseChange.{u})
    (hX : Properties X) :
    coherentGenus K (Over.mk (pullback.snd (pullback.snd X.hom T.hom) t)) = coherentGenus F X := by
  rw [coherentGenus_iso (familyFibreIso X T K t)]
  exact coherentGenus_arbitraryBaseChange hbase X hX K (t ≫ T.hom)

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (htensor : AlgebraicGeometry.Scheme.Modules.Invertible.ModuleTensorPullback.{u})
include hnorm in
theorem familyFibre_degree (hX : Properties X)
    (a : Invertible.PicardGroup (pullback X.hom T.hom)) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod
      (Over.mk (pullback.snd (pullback.snd X.hom T.hom) t))
      (familyFibre_curveProperties X T K t hX)
      (Invertible.pullbackClass (pullback.fst (pullback.snd X.hom T.hom) t) a) =
    fibreDegree hnormal hcomp hreg hclosed hdim hprod htensor X hX T K
      (t ≫ T.hom) (Over.homMk t rfl) a := by
  dsimp only [fibreDegree, AddMonoidHom.comp_apply,
    AlgebraicGeometry.Scheme.Modules.Invertible.pullbackHom_apply]
  rw [← familyFibreIso_familyMap X T K t, Invertible.pullbackClass_comp]
  exact curveDegree_pullback_iso hnormal hcomp hreg hclosed hdim hprod hnorm
    (familyFibreIso X T K t) (familyFibre_curveProperties X T K t hX)
    (curveProperties_baseChange hX K (t ≫ T.hom)) _
end AlgebraicGeometry.Scheme.OverField.Curve.RelativePicard
