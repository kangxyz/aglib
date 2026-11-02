/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.Global
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.OpenCentre
public import Aglib.AlgebraicGeometry.Blowup.Differentials.PairIdeal.RawGluing
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Scheme
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenSquare
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.DualMapToPullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.RightInsertion
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Section.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# AlgebraicGeometry / Blowup / Differentials / PairIdeal / OpenTransport

Source: `IntegralTrace/PairIdealRawOpenTransport.lean`.
Incoming SHA256: `95a01181178bff0fe417dcf0273c622e1a9a48b0b95d8ca1912cde6b78e160ae`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Blowup.RegularPoint

universe u vK


open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.PairIdeal

section Transport

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R]
  [Field K] [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (I : Ideal R) (x y : R) (hI : Ideal.span {x, y} = I)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (hproper : I ≠ ⊤) (X : Scheme.{u}) (p : X) (hp : IsClosed ({p} : Set X))
  (a : X ⟶ Spec (.of Λ)) (j : Spec (.of R) ⟶ X) [IsOpenImmersion j]
  (ha : j ≫ a = Spec.map (CommRingCat.ofHom (algebraMap Λ R)))
  (hcentre : (X.fromSpecResidueField p).ker.comap j = Blowup.affineCenter R I)
  (n : ℕ) (L : LineBundle X)
  (φ : moduleExteriorPower X (relativeDifferentialSheaf a) n ⟶ L.val)

local notation "Y" => pointBlowup X p
local notation "Z" => canonicalBlowup I
local notation "b" => pointBlowdown X p
local notation "d" => blowdown I
local notation "q" => pairIdeal_openComparison R I X p j hcentre
local notation "α" => Spec.map (CommRingCat.ofHom (algebraMap Λ R))
local notation "M" => moduleExteriorPower X (relativeDifferentialSheaf a) n
local notation "MY" => moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n
local notation "IY" => pointIdealLine X p hp
local notation "QY" => Subtype.val (dualLineBundle Y IY)
local notation "QZ" => Subtype.val (dualLineBundle Z (centreIdealLine I))
local notation "P" => Functor.obj (pullback b) L.val
local notation "PZ" => Functor.obj (pullback d) (Functor.obj (pullback j) L.val)
local notation "TY" => tensorSheaf Y P QY
local notation "Fj" => rawOpenBaseIso a α j ha n
local notation "C" => pullbackComp q b ≪≫
  pullbackCongr (pairIdeal_openComparison_triangle R I X p j hcentre) ≪≫
    Iso.symm (pullbackComp d j)
local notation "θ" => pairIdeal_openDualMap R I X p j hcentre hp

/-- The actual P06 raw map, followed by the original forward coefficient transport. -/
def pairIdeal_rawOpenPullback : (pullback q).obj MY ⟶ (pullback q).obj TY := by
  let _ : IsOpenImmersion q := pairIdeal_openComparison_isOpenImmersion R I X p j hcentre
  let LR : LineBundle (Spec (.of R)) := pullbackLineBundle j L
  let φR : moduleExteriorPower (Spec (.of R)) (relativeDifferentialSheaf α) n ⟶ LR.val :=
    (Fj).inv ≫ (pullback j).map φ
  let S : (pullback q).obj MY ≅ moduleExteriorPower Z (relativeDifferentialSheaf (d ≫ α)) n :=
    rawOpenSourceIso a α j ha b d q
    (pairIdeal_openComparison_triangle R I X p j hcentre) n
  let η : (show (Z).Modules from tensorSheaf Z PZ QZ) ⟶ (pullback q).obj TY :=
    tensorSheafMap Z ((C).app L.val).inv θ ≫ (pullbackTensorMapIso q P QY).inv
  exact S.hom ≫ pairIdeal_onePoleRawMap Λ R K I x y hI hx hy hproper n LR φR ≫ η

/-- The same transported raw map in the original native restriction coordinates. -/
def pairIdeal_rawOpenRestriction :
    let _ : IsOpenImmersion q := pairIdeal_openComparison_isOpenImmersion R I X p j hcentre
    (MY).restrict q ⟶ (show (Y).Modules from TY).restrict q := by
  let _ : IsOpenImmersion q := pairIdeal_openComparison_isOpenImmersion R I X p j hcentre
  exact (Scheme.Modules.restrictFunctorIsoPullback q).hom.app MY ≫
    pairIdeal_rawOpenPullback Λ R K I x y hI hx hy hproper X p hp a j ha hcentre n L φ ≫
      (Scheme.Modules.restrictFunctorIsoPullback q).inv.app TY

/-- The local map has the original coefficient/positive-section equation in pullback coordinates. -/
theorem pairIdeal_rawOpenPullback_unit :
    (pullback q).map (rawFormsPullback a b n) ≫
        pairIdeal_rawOpenPullback Λ R K I x y hI hx hy hproper X p hp a j ha hcentre n L φ =
      (pullback q).map ((pullback b).map φ ≫
        (positiveCartierTensorSection Y QY
          (cartierDualIdealSection (pointExceptionalι X p))).app P ≫
            (tensorSheafBraiding Y QY P).hom) := by
  let _ : IsOpenImmersion q := pairIdeal_openComparison_isOpenImmersion R I X p j hcentre
  let LR : LineBundle (Spec (.of R)) := pullbackLineBundle j L
  let φR : moduleExteriorPower (Spec (.of R)) (relativeDifferentialSheaf α) n ⟶ LR.val :=
    (Fj).inv ≫ (pullback j).map φ
  let S : (pullback q).obj MY ≅ moduleExteriorPower Z (relativeDifferentialSheaf (d ≫ α)) n :=
    rawOpenSourceIso a α j ha b d q
    (pairIdeal_openComparison_triangle R I X p j hcentre) n
  let sY := cartierDualIdealSection (pointExceptionalι X p)
  let sZ := cartierDualIdealSection
    (((Blowup.affineCenter R I).comap d).subschemeι)
  let iY : P ⟶ TY := (ρ_ P).inv ≫ tensorSheafMap Y (𝟙 P) sY
  let iZ : PZ ⟶ (show (Z).Modules from tensorSheaf Z PZ QZ) :=
    (ρ_ PZ).inv ≫ tensorSheafMap Z (𝟙 PZ) sZ
  let η : (show (Z).Modules from tensorSheaf Z PZ QZ) ⟶ (pullback q).obj TY :=
    tensorSheafMap Z ((C).app L.val).inv θ ≫ (pullbackTensorMapIso q P QY).inv
  have hs := rawOpenSourceIso_pullback a α j ha b d q
    (pairIdeal_openComparison_triangle R I X p j hcentre) n
  have hr := pairIdeal_onePoleRawMap_unit Λ R K I x y hI hx hy hproper n LR φR
  have hφ : (pullback d).map (Fj).hom ≫ (pullback d).map φR =
      (pullback d).map ((pullback j).map φ) := by
    let A₀ : (Spec (.of R)).Modules := (pullback j).obj M
    let B₀ : (Spec (.of R)).Modules :=
      moduleExteriorPower (Spec (.of R)) (relativeDifferentialSheaf α) n
    let N₀ : (Spec (.of R)).Modules := (pullback j).obj L.val
    let F : (Spec (.of R)).Modules ⥤ (Z).Modules := pullback d
    let eJ : A₀ ≅ B₀ := Fj
    let f : A₀ ⟶ N₀ := (pullback j).map φ
    have he : eJ.hom ≫ φR = f :=
      (Category.assoc eJ.hom eJ.inv f).symm.trans
        ((congrArg (fun z : A₀ ⟶ A₀ => z ≫ f) eJ.hom_inv_id).trans
          (Category.id_comp f))
    exact (F.map_comp eJ.hom φR).symm.trans
      (congrArg (fun z : A₀ ⟶ N₀ => F.map z) he)
  have ht : iZ ≫ η = ((C).app L.val).inv ≫ (pullback q).map iY := by
    let D₀ : (Z).Modules := tensorSheaf Z PZ QZ
    let E₀ : (Z).Modules := tensorSheaf Z ((pullback q).obj P) ((pullback q).obj QY)
    let T₀ : (Z).Modules := (pullback q).obj TY
    let eT : T₀ ≅ E₀ := pullbackTensorMapIso q P QY
    let c : PZ ⟶ (pullback q).obj P := ((C).app L.val).inv
    let k : D₀ ⟶ E₀ := tensorSheafMap Z c θ
    have h := rightInsertion_pullback_transport q P QY PZ QZ c θ sY sZ
      (pairIdeal_openDualMap_section R I X p j hcentre hp)
    have h₀ : iZ ≫ k = (c ≫ (pullback q).map iY) ≫ eT.hom := by
      calc
        (show PZ ⟶ E₀ from iZ ≫ k) =
            (show PZ ⟶ E₀ from (ρ_ PZ).inv ≫ tensorSheafMap Z (𝟙 PZ) sZ ≫ k) :=
          Category.assoc _ _ _
        _ = (show PZ ⟶ E₀ from c ≫ (pullback q).map iY ≫ pullbackTensorMap q P QY) := h
        _ = (show PZ ⟶ E₀ from c ≫ (pullback q).map iY ≫ eT.hom) :=
          congrArg (fun z : T₀ ⟶ E₀ => c ≫ (pullback q).map iY ≫ z)
            (pullbackTensorMapIso_hom q P QY).symm
        _ = (show PZ ⟶ E₀ from (c ≫ (pullback q).map iY) ≫ eT.hom) :=
          (Category.assoc _ _ _).symm
    exact (Category.assoc iZ k eT.inv).symm.trans ((Iso.comp_inv_eq eT).mpr h₀)
  have hn : (C).hom.app M ≫ (pullback d).map ((pullback j).map φ) ≫
      ((C).app L.val).inv = (pullback q).map ((pullback b).map φ) := by
    let F : X.Modules ⥤ (Z).Modules := pullback b ⋙ pullback q
    let G : X.Modules ⥤ (Z).Modules := pullback j ⋙ pullback d
    let E : F ≅ G := C
    let eL : F.obj L.val ≅ G.obj L.val := E.app L.val
    have hn₀ : E.hom.app M ≫ G.map φ = F.map φ ≫ eL.hom :=
      (E.hom.naturality φ).symm
    have hn₁ : E.hom.app M ≫ (pullback d).map ((pullback j).map φ) =
        (pullback q).map ((pullback b).map φ) ≫ eL.hom :=
      (congrArg (fun z : G.obj M ⟶ G.obj L.val => E.hom.app M ≫ z)
        (Functor.comp_map (pullback j) (pullback d) φ).symm).trans
          (hn₀.trans (congrArg (fun z : F.obj M ⟶ F.obj L.val => z ≫ eL.hom)
            (Functor.comp_map (pullback b) (pullback q) φ)))
    exact (Category.assoc (E.hom.app M)
      ((pullback d).map ((pullback j).map φ)) eL.inv).symm.trans
        ((Iso.comp_inv_eq eL).mpr hn₁)
  have hr' : rawFormsPullback α d n ≫
      pairIdeal_onePoleRawMap Λ R K I x y hI hx hy hproper n LR φR =
        (pullback d).map φR ≫ iZ := by
    exact hr.trans (congrArg (fun z => (pullback d).map φR ≫ z)
      (positiveSection_eq_rightInsertion Z PZ QZ sZ))
  have hiY : (positiveCartierTensorSection Y QY sY).app P ≫
      (tensorSheafBraiding Y QY P).hom = iY :=
    positiveSection_eq_rightInsertion Y P QY sY
  calc
    _ = (C).hom.app M ≫ (pullback d).map (Fj).hom ≫ rawFormsPullback α d n ≫
        pairIdeal_onePoleRawMap Λ R K I x y hI hx hy hproper n LR φR ≫ η := by
      change (pullback q).map (rawFormsPullback a b n) ≫
        (S.hom ≫ pairIdeal_onePoleRawMap Λ R K I x y hI hx hy hproper n LR φR ≫ η) = _
      simpa only [Category.assoc] using congrArg (fun z => z ≫
        pairIdeal_onePoleRawMap Λ R K I x y hI hx hy hproper n LR φR ≫ η) hs
    _ = (C).hom.app M ≫ (pullback d).map (Fj).hom ≫ (pullback d).map φR ≫ iZ ≫ η := by
      let A₀ : (Z).Modules := (pullback d).obj
        (moduleExteriorPower (Spec (.of R)) (relativeDifferentialSheaf α) n)
      let B₀ : (Z).Modules := moduleExteriorPower Z (relativeDifferentialSheaf (d ≫ α)) n
      let T₀ : (Z).Modules := tensorSheaf Z PZ QZ
      let V₀ : (Z).Modules := (pullback q).obj TY
      let k : B₀ ⟶ T₀ := pairIdeal_onePoleRawMap Λ R K I x y hI hx hy hproper n LR φR
      have hstep : rawFormsPullback α d n ≫ k ≫ η = (pullback d).map φR ≫ iZ ≫ η :=
        (Category.assoc (rawFormsPullback α d n) k η).symm.trans
          ((congrArg (fun z : A₀ ⟶ T₀ => z ≫ η) hr').trans
            (Category.assoc ((pullback d).map φR) iZ η))
      exact congrArg (fun z : A₀ ⟶ V₀ =>
        (C).hom.app M ≫ (pullback d).map (Fj).hom ≫ z) hstep
    _ = (C).hom.app M ≫ (pullback d).map ((pullback j).map φ) ≫ iZ ≫ η := by
      let A₀ : (Z).Modules := (pullback d).obj ((pullback j).obj M)
      let N₀ : (Z).Modules := PZ
      let V₀ : (Z).Modules := (pullback q).obj TY
      have hstep : (pullback d).map (Fj).hom ≫ (pullback d).map φR ≫ (iZ ≫ η) =
          (pullback d).map ((pullback j).map φ) ≫ (iZ ≫ η) :=
        (Category.assoc ((pullback d).map (Fj).hom) ((pullback d).map φR) (iZ ≫ η)).symm.trans
          (congrArg (fun z : A₀ ⟶ N₀ => z ≫ iZ ≫ η) hφ)
      exact congrArg (fun z : A₀ ⟶ V₀ => (C).hom.app M ≫ z) hstep
    _ = (C).hom.app M ≫ (pullback d).map ((pullback j).map φ) ≫
        ((C).app L.val).inv ≫ (pullback q).map iY :=
      congrArg (fun z => (C).hom.app M ≫ (pullback d).map ((pullback j).map φ) ≫ z) ht
    _ = (pullback q).map ((pullback b).map φ) ≫ (pullback q).map iY := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ (pullback q).map iY) hn
    _ = (pullback q).map ((pullback b).map φ ≫ iY) :=
      ((pullback q).map_comp ((pullback b).map φ) iY).symm
    _ = _ := congrArg (fun z => (pullback q).map ((pullback b).map φ ≫ z)) hiY.symm

/-- The original native restriction has the proved local unit equation required by cover gluing. -/
theorem pairIdeal_rawOpenRestriction_unit :
    let _ : IsOpenImmersion q := pairIdeal_openComparison_isOpenImmersion R I X p j hcentre
    (Scheme.Modules.restrictFunctor q).map (rawFormsPullback a b n) ≫
        pairIdeal_rawOpenRestriction Λ R K I x y hI hx hy hproper X p hp a j ha hcentre n L φ =
      (Scheme.Modules.restrictFunctor q).map ((pullback b).map φ ≫
        (positiveCartierTensorSection Y QY
          (cartierDualIdealSection (pointExceptionalι X p))).app P ≫
            (tensorSheafBraiding Y QY P).hom) := by
  let _ : IsOpenImmersion q := pairIdeal_openComparison_isOpenImmersion R I X p j hcentre
  let e := Scheme.Modules.restrictFunctorIsoPullback q
  have h := pairIdeal_rawOpenPullback_unit Λ R K I x y hI hx hy hproper X p hp
    a j ha hcentre n L φ
  let β := rawFormsPullback a b n
  let t := (pullback b).map φ ≫
    (positiveCartierTensorSection Y QY
      (cartierDualIdealSection (pointExceptionalι X p))).app P ≫
        (tensorSheafBraiding Y QY P).hom
  let r := pairIdeal_rawOpenPullback Λ R K I x y hI hx hy hproper X p hp
    a j ha hcentre n L φ
  calc
    _ = e.hom.app ((pullback b).obj M) ≫ (pullback q).map β ≫ r ≫ e.inv.app TY := by
      simpa only [pairIdeal_rawOpenRestriction, e, β, r, Category.assoc] using
        congrArg (fun z => z ≫ r ≫ e.inv.app TY) (e.hom.naturality β)
    _ = e.hom.app ((pullback b).obj M) ≫ (pullback q).map t ≫ e.inv.app TY := by
      simpa only [β, r, t, Category.assoc] using
        congrArg (fun z => e.hom.app ((pullback b).obj M) ≫ z ≫ e.inv.app TY) h
    _ = _ := by
      let A₀ : (Y).Modules := (pullback b).obj M
      let N₀ : (Y).Modules := TY
      let F : (Y).Modules ⥤ (Z).Modules := Scheme.Modules.restrictFunctor q
      let G : (Y).Modules ⥤ (Z).Modules := pullback q
      let E : F ≅ G := e
      let eN : F.obj N₀ ≅ G.obj N₀ := E.app N₀
      have hn : E.hom.app A₀ ≫ G.map t = F.map t ≫ eN.hom :=
        (E.hom.naturality t).symm
      exact (Category.assoc (E.hom.app A₀) (G.map t) eN.inv).symm.trans
        ((Iso.comp_inv_eq eN).mpr hn)

end Transport

end AlgebraicGeometry.Scheme.Blowup.PairIdeal
