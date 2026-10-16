/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Free.Sections
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Actual relative differentials on original polynomial projective charts

The original coordinate-open polynomial isomorphism identifies the actual restricted relative
differential sheaf with the native polynomial Kähler sheaf. Its free frame retains the literal
original relative differential on every principal chart open. No differential object or map
is replaced and no field, finiteness, or nontriviality hypothesis is imposed.
The original homogeneous ratio agrees with the original inverse-chart image of its native
polynomial coordinate section on every chart open.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The actual polynomial spectrum chart, using the original coordinate-open isomorphism. -/
abbrev eulerPolynomialChart (i : ι) :
    Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)) ⟶ ProjectiveSpace R ι :=
  (coordinateOpenIsoSpecPolynomial R ι i).inv ≫ (coordinateOpen R ι i).ι

/-- The original polynomial chart preserves the original coefficient-ring structure map. -/
theorem eulerPolynomialChart_toSpec (i : ι) :
    eulerPolynomialChart R ι i ≫ toSpec R ι =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial {j : ι // j ≠ i} R)) := by
  change Spec.map (CommRingCat.ofHom (coordinateRingToPolynomial R ι i)) ≫
    (Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one) ≫ toSpec R ι = _
  rw [coordinateChart_toSpec, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact coordinateRingToPolynomial_coefficient R ι i r

/-- Original relative differentials restricted to a native polynomial chart are the actual
polynomial Kähler module sheaf, through the proved original open-square comparison. -/
def eulerPolynomialOmegaTildeIso (i : ι) :
    (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).restrict
        (eulerPolynomialChart R ι i) ≅
      tilde (CommRingCat.KaehlerDifferential (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial {j : ι // j ≠ i} R))) :=
  Scheme.Modules.Differentials.relativeDifferentialOpenSquareIso (toSpec R ι)
    (eulerPolynomialChart R ι i)
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : R →+* MvPolynomial {j : ι // j ≠ i} R))) (𝟙 _)
      (by simpa only [Category.comp_id] using eulerPolynomialChart_toSpec R ι i) ≪≫
    Scheme.Modules.Differentials.relativeDifferentialAffineIso _

/-- A native polynomial frame of the actual relative differential sheaf, with its original
principal-open differential values retained in the same construction. -/
def eulerPolynomialOmegaFrame (i : ι) :
    let S : CommRingCat.{u} := CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)
    {e : (Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)).restrict
        (eulerPolynomialChart R ι i) ≅
      SheafOfModules.free (R := (Spec S).ringCatSheaf) {j : ι // j ≠ i} //
      ∀ (r : S) (j : {j : ι // j ≠ i}),
        let U := PrimeSpectrum.basicOpen r
        e.hom.val.app (op U)
          ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
            (((eulerPolynomialChart R ι i).appIso U).inv
              (((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op)
                (MvPolynomial.X j)))) =
          (SheafOfModules.freeSection (R := (Spec S).ringCatSheaf) j).val (op U)} := by
  let P := MvPolynomial {j : ι // j ≠ i} R
  let S : CommRingCat.{u} := CommRingCat.of P
  let σ : CommRingCat.of R ⟶ S := CommRingCat.ofHom MvPolynomial.C
  let B (a : Algebra R P) : Type u :=
    letI := a
    {b : Module.Basis {j : ι // j ≠ i} P Ω[P⁄R] //
      ∀ j, b j = KaehlerDifferential.D R P (MvPolynomial.X j)}
  have hA : (MvPolynomial.C : R →+* P).toAlgebra = (inferInstance : Algebra R P) :=
    toAlgebra_algebraMap
  have hb₀ : B (inferInstance : Algebra R P) :=
    ⟨KaehlerDifferential.mvPolynomialBasis R {j : ι // j ≠ i},
      KaehlerDifferential.mvPolynomialBasis_apply R {j : ι // j ≠ i}⟩
  let b : {b : Module.Basis {j : ι // j ≠ i} P (CommRingCat.KaehlerDifferential σ) //
      ∀ j, b j = CommRingCat.KaehlerDifferential.d (MvPolynomial.X j)} :=
    (congrArg B hA).mpr hb₀
  let e := eulerPolynomialOmegaTildeIso R ι i ≪≫ Scheme.Modules.tildeBasisIso _ b.val
  refine ⟨e, ?_⟩
  intro r j
  let U := PrimeSpectrum.basicOpen (R := S) r
  let a : Γ(Spec S, U) :=
    ((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op) (MvPolynomial.X j)
  have hsq : eulerPolynomialChart R ι i ≫ toSpec R ι = Spec.map σ ≫ 𝟙 _ := by
    simpa only [Category.comp_id] using eulerPolynomialChart_toSpec R ι i
  let sq := Scheme.Modules.Differentials.relativeDifferentialOpenSquareIso (toSpec R ι)
    (eulerPolynomialChart R ι i) (Spec.map σ) (𝟙 _) hsq
  have hs : sq.hom.val.app (op U)
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (((eulerPolynomialChart R ι i).appIso U).inv a)) =
      (Scheme.Modules.Differentials.relativeDifferentialDerivation (Spec.map σ)).d a :=
    (Scheme.Modules.Differentials.relativeDifferentialOpenSquareIso_hom_d (toSpec R ι)
      (eulerPolynomialChart R ι i) (Spec.map σ) (𝟙 _) hsq U
      (((eulerPolynomialChart R ι i).appIso U).inv a)).trans
      (congrArg (Scheme.Modules.Differentials.relativeDifferentialDerivation (Spec.map σ)).d
        (Iso.inv_hom_id_apply ((eulerPolynomialChart R ι i).appIso U) a))
  have ha : (Scheme.Modules.Differentials.relativeDifferentialAffineIso σ).hom.val.app (op U)
      ((Scheme.Modules.Differentials.relativeDifferentialDerivation (Spec.map σ)).d a) =
      tilde.toOpen (CommRingCat.KaehlerDifferential σ) U
        (CommRingCat.KaehlerDifferential.d (MvPolynomial.X j)) :=
    Scheme.Modules.Differentials.relativeDifferentialAffineIso_hom_d σ r (MvPolynomial.X j)
  have hf := Scheme.Modules.tildeBasisIso_hom_toOpen
    (CommRingCat.KaehlerDifferential σ) b.val j U
  have hf' : (Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app
        (op U) (tilde.toOpen (CommRingCat.KaehlerDifferential σ) U
          (CommRingCat.KaehlerDifferential.d (MvPolynomial.X j))) =
      (SheafOfModules.freeSection (R := (Spec S).ringCatSheaf) j).val
        (op U) :=
    (congrArg (fun z =>
      (Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app
        (op U) (tilde.toOpen (CommRingCat.KaehlerDifferential σ) U z)) (b.property j)).symm.trans hf
  change (Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app
    (op U) ((Scheme.Modules.Differentials.relativeDifferentialAffineIso σ).hom.val.app (op U)
      (sq.hom.val.app (op U)
        ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
          (((eulerPolynomialChart R ι i).appIso U).inv a)))) = _
  exact (congrArg (fun z =>
    (Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app (op U)
      ((Scheme.Modules.Differentials.relativeDifferentialAffineIso σ).hom.val.app (op U) z))
        hs).trans
    ((congrArg ((Scheme.Modules.tildeBasisIso (CommRingCat.KaehlerDifferential σ) b.val).hom.val.app
      (op U)) ha).trans hf')

/-- The free isomorphism underlying the checked original polynomial differential frame. -/
def eulerPolynomialOmegaFreeIso (i : ι) := (eulerPolynomialOmegaFrame R ι i).val


/-- The constructed polynomial frame sends the original relative differential of every
localized chart coordinate to the corresponding original free section. -/
theorem eulerPolynomialOmegaFreeIso_hom_d (i : ι) :
    let S : CommRingCat.{u} := CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)
    ∀ (r : S) (j : {j : ι // j ≠ i}),
      let U := PrimeSpectrum.basicOpen r
      (eulerPolynomialOmegaFreeIso R ι i).hom.val.app (op U)
        ((Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
          (((eulerPolynomialChart R ι i).appIso U).inv
            (((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map U.leTop.op)
              (MvPolynomial.X j)))) =
        (SheafOfModules.freeSection (R := (Spec S).ringCatSheaf) j).val (op U) :=
  (eulerPolynomialOmegaFrame R ι i).property

/-- Every image subopen of the original polynomial chart lies in its original coordinate open. -/
theorem eulerPolynomialChart_image_le (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    eulerPolynomialChart R ι i ''ᵁ V ≤ coordinateOpen R ι i := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ((coordinateOpenIsoSpecPolynomial R ι i).inv y).property

/-- The native polynomial coordinate map retains the original projective-chart section map. -/
theorem eulerPolynomialChart_polynomialToSection (i : ι)
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    let S : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ i} R)
    let g := eulerPolynomialChart R ι i
    CommRingCat.ofHom (polynomialToCoordinateRing R ι i) ≫
      Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i) ≫
        g.appLE (coordinateOpen R ι i) V
          (by intro x _hx; exact ((coordinateOpenIsoSpecPolynomial R ι i).inv x).property) =
      (Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map V.leTop.op := by
  let S : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ i} R)
  let U := coordinateOpen R ι i
  let e := coordinateOpenIsoSpecPolynomial R ι i
  let a := Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
  let p := CommRingCat.ofHom (polynomialToCoordinateRing R ι i)
  have he : (Scheme.ΓSpecIso S).inv ≫ e.hom.appTop = p ≫ a ≫ U.topIso.inv := by
    change (Scheme.ΓSpecIso S).inv ≫
      (Spec.map p).appTop ≫
        (Proj.basicOpenToSpec (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)).appTop = _
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
    have hb := Proj.basicOpenToSpec_app_top
      (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
    exact (congrArg (fun f => p ≫
      (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing R ι i))).inv ≫ f) hb).trans
        (by
          simp only [Iso.inv_hom_id_assoc]
          rfl)
  have he' : e.hom.appTop ≫ e.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]
    simp
  have ht : p ≫ a ≫ U.topIso.inv ≫ e.inv.appTop = (Scheme.ΓSpecIso S).inv := by
    exact (congrArg (fun f => f ≫ e.inv.appTop) he).symm.trans
      (by rw [Category.assoc, he', Category.comp_id])
  have hu : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have hc := Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ V
    U.ι_preimage_self.ge (by simp only [Scheme.Hom.preimage_top]; exact le_top)
  rw [hu] at hc
  change U.topIso.inv ≫ (e.inv.appTop ≫ (Spec S).presheaf.map V.leTop.op) = _ at hc
  change p ≫ a ≫ _ = _
  rw [← hc]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ (Spec S).presheaf.map V.leTop.op) ht

/-- The actual chart structure-map isomorphism sends the original ratio to its native
polynomial coordinate section on every chart open. -/
theorem eulerPolynomialChart_coordinateRatio (i : ι) (j : {j : ι // j ≠ i})
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    let S : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ i} R)
    ((eulerPolynomialChart R ι i).appIso V).hom
      (eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V)) =
      ((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map V.leTop.op) (MvPolynomial.X j) := by
  let S : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ i} R)
  let g := eulerPolynomialChart R ι i
  let h : V ≤ g ⁻¹ᵁ coordinateOpen R ι i :=
    by intro x _hx; exact ((coordinateOpenIsoSpecPolynomial R ι i).inv x).property
  have hm : (ProjectiveSpace R ι).presheaf.map
      (homOfLE (eulerPolynomialChart_image_le R ι i V)).op ≫ (g.appIso V).hom =
        g.appLE (coordinateOpen R ι i) V h := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  have hp := ConcreteCategory.congr_hom (eulerPolynomialChart_polynomialToSection R ι i V)
    (MvPolynomial.X j)
  change g.appLE (coordinateOpen R ι i) V h
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
      (polynomialToCoordinateRing R ι i (MvPolynomial.X j))) = _ at hp
  rw [polynomialToCoordinateRing_X] at hp
  exact (congrArg (g.appIso V).hom
    (eulerCoordinateRatio_eq_fraction R ι i j.val (eulerPolynomialChart_image_le R ι i V))).trans
      ((ConcreteCategory.congr_hom hm _).trans hp)

/-- The original projective ratio is the original inverse-chart image of the native
polynomial coordinate section. -/
theorem eulerCoordinateRatio_eq_polynomialSection (i : ι) (j : {j : ι // j ≠ i})
    (V : (Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R))).Opens) :
    let S : CommRingCat.{u} := .of (MvPolynomial {j : ι // j ≠ i} R)
    eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V) =
      ((eulerPolynomialChart R ι i).appIso V).inv
        (((Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map V.leTop.op) (MvPolynomial.X j)) :=
  (Iso.hom_inv_id_apply ((eulerPolynomialChart R ι i).appIso V)
    (eulerCoordinateRatio R ι i j.val (eulerPolynomialChart_image_le R ι i V))).symm.trans
      (congrArg ((eulerPolynomialChart R ι i).appIso V).inv
        (eulerPolynomialChart_coordinateRatio R ι i j V))

end AlgebraicGeometry.ProjectiveSpace
