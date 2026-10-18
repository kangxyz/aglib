/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal.Determinant
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.OpenCoefficient

/-!
# The original ambient determinant with actual coefficient sheaves

The intrinsic determinant square and the original ambient coefficient bridge
compose to the original canonical determinant square. An actual coefficient
isomorphism transports this square by naturality of the same mixed pullback
comparison. The normal-first order and all original arrows are retained.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem isoHom_composite {C : Type*} [Category C] {X Y Z : C}
    (D : X ≅ Z) (Δ : X ≅ Y) (e : Y ≅ Z) (h : D = Δ ≪≫ e) :
    D.hom = Δ.hom ≫ e.hom := congrArg Iso.hom h

private theorem determinantCoefficientSquare
    {X X' : Scheme.{u}} (j : X' ⟶ X) [IsOpenImmersion j]
    {C Q M P : X.Modules} {C' Q' M' P' : X'.Modules}
    (Δ : tensorSheaf X C Q ≅ M) (Δ' : tensorSheaf X' C' Q' ≅ M')
    (D : tensorSheaf X C Q ≅ P) (D' : tensorSheaf X' C' Q' ≅ P')
    (e : M ≅ P) (e' : M' ≅ P')
    (aC : (restrictFunctor j).obj C ⟶ C') (aQ : (restrictFunctor j).obj Q ⟶ Q')
    (aM : (restrictFunctor j).obj M ⟶ M') (aP : (restrictFunctor j).obj P ⟶ P')
    (hD : D.hom = Δ.hom ≫ e.hom) (hD' : D'.hom = Δ'.hom ≫ e'.hom)
    (hΔ : CanonicalDeterminantOpenSquare j C Q M C' Q' M' Δ Δ' aC aQ aM)
    (he : (restrictFunctor j).map e.hom ≫ aP = aM ≫ e'.hom) :
    CanonicalDeterminantOpenSquare j C Q P C' Q' P' D D' aC aQ aP := by
  apply (canonicalDeterminantOpenSquare_iff j C Q P C' Q' P' D D' aC aQ aP).2
  have hΔ' := (canonicalDeterminantOpenSquare_iff j C Q M C' Q' M'
    Δ Δ' aC aQ aM).1 hΔ
  rw [hD, hD', Functor.map_comp, Category.assoc, he, ← Category.assoc, hΔ', Category.assoc]

private theorem pasteHomSquares {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {X' Y' Z' : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (a : F.obj X ⟶ X') (b : F.obj Y ⟶ Y') (c : F.obj Z ⟶ Z')
    {k : X ⟶ Z} {k' : X' ⟶ Z'}
    (hk : k = f ≫ g) (hk' : k' = f' ≫ g')
    (hf : F.map f ≫ b = a ≫ f') (hg : F.map g ≫ c = b ≫ g') :
    F.map k ≫ c = a ≫ k' := by
  rw [hk, hk', F.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

private theorem coefficientTransport_naturality
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (P : C ⥤ D) (P' : C' ⥤ D') (J : C ⥤ C') (F : D ⥤ D')
    (S : P ⋙ F ≅ J ⋙ P') {L Ω : C} {Ω' : C'}
    (E : L ≅ Ω) (T : J.obj Ω ≅ Ω') :
    F.map ((P.mapIso E.symm).hom) ≫ S.hom.app L =
      (S.app Ω ≪≫ P'.mapIso T).hom ≫
        (P'.mapIso ((J.mapIso E ≪≫ T).symm)).hom := by
  change F.map (P.map E.inv) ≫ S.hom.app L =
    (S.hom.app Ω ≫ P'.map T.hom) ≫ P'.map (T.inv ≫ J.map E.inv)
  calc
    _ = S.hom.app Ω ≫ P'.map (J.map E.inv) := S.hom.naturality E.inv
    _ = _ := by
      rw [P'.map_comp, Category.assoc, ← Category.assoc (P'.map T.hom),
        ← P'.map_comp T.hom T.inv, T.hom_inv_id, P'.map_id, Category.id_comp]

private theorem canonicalDeterminantAt_hom
    {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) {c d : ℕ}
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
    (bA : Module.Basis (Fin (c + d)) A (CommRingCat.KaehlerDifferential α))
    (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
    (hc : s.length = c) :
    (regularListCanonicalDeterminantAt α (Ideal.ofList s) c d hA hB bA bQ s hs rfl hc).hom =
      (regularListConormalDeterminantAt α (Ideal.ofList s) c d hA hB bQ s hs rfl hc).hom ≫
        (affineConormalAmbientCoefficientIso α s (c + d) bA).hom := by
  subst c
  exact isoHom_composite _ _ _ (affineRegularListCanonicalDeterminant_eq α s hs hA hB bA bQ)

/-- The actual canonical determinant followed by the pullback of a chosen coefficient frame. -/
def regularListCanonicalCoefficientDeterminantAt
    {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (c d : ℕ)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
    (bA : Module.Basis (Fin (c + d)) A (CommRingCat.KaehlerDifferential α))
    (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
    (hc : s.length = c) {L : (Spec A).Modules}
    (E : L ≅ moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) (c + d)) :
    tensorSheaf (Spec (regularListQuotientRing s)) (regularListNormalAt (Ideal.ofList s) c)
      (regularListTangentTopAt α (Ideal.ofList s) d) ≅
        (pullback (Spec.map (regularListQuotientMap s))).obj L :=
  regularListCanonicalDeterminantAt α (Ideal.ofList s) c d hA hB bA bQ s hs rfl hc ≪≫
    (pullback (Spec.map (regularListQuotientMap s))).mapIso E.symm

private theorem canonicalCoefficientDeterminantAt_hom
    {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A)
    (hs : RingTheory.Sequence.IsWeaklyRegular A s) (c d : ℕ)
    (hA : α.hom.FormallySmooth)
    (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
    (bA : Module.Basis (Fin (c + d)) A (CommRingCat.KaehlerDifferential α))
    (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
      (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
    (hc : s.length = c) {L : (Spec A).Modules}
    (E : L ≅ moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) (c + d)) :
    (regularListCanonicalCoefficientDeterminantAt α s hs c d hA hB bA bQ hc E).hom =
      (regularListCanonicalDeterminantAt α (Ideal.ofList s) c d hA hB bA bQ s hs rfl hc).hom ≫
        ((pullback (Spec.map (regularListQuotientMap s))).mapIso E.symm).hom := rfl

/-- The original exterior restriction of the actual ambient differential isomorphism. -/
def canonicalAmbientTopOpenIso
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] (n : ℕ) :
    (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n).restrict
      (Spec.map φ) ≅
      moduleExteriorPower (Spec A') (relativeDifferentialSheaf (Spec.map (α ≫ φ))) n :=
  (moduleExteriorPowerRestrictionIso (Spec.map φ)
    (relativeDifferentialSheaf (Spec.map α)) n).symm ≪≫
      (moduleExteriorPowerFunctor (Spec A') n).mapIso (canonicalAmbientDifferentialOpenIso α φ)

/-- The original mixed square on the ambient top followed by its actual differential map. -/
def canonicalAmbientTopCoefficientOpenIso
    {R A A' B B' : CommRingCat.{u}} (α : R ⟶ A) (φ : A ⟶ A')
    (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ τ = σ ≫ ψ) (n : ℕ) :
    ((pullback (Spec.map σ)).obj
      (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n)).restrict
        (Spec.map ψ) ≅
      (pullback (Spec.map τ)).obj
        (moduleExteriorPower (Spec A') (relativeDifferentialSheaf (Spec.map (α ≫ φ))) n) :=
  (canonicalPullbackOpenSquareIso (Spec.map σ) (Spec.map τ) (Spec.map ψ) (Spec.map φ)
    (canonicalAmbientClosedSquare φ σ τ ψ h)).app
      (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) ≪≫
    (pullback (Spec.map τ)).mapIso (canonicalAmbientTopOpenIso α φ n)

private def coefficientFrame
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] (n : ℕ) {L : (Spec A).Modules}
    (E : L ≅ moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) :
    L.restrict (Spec.map φ) ≅
      moduleExteriorPower (Spec A') (relativeDifferentialSheaf (Spec.map (α ≫ φ))) n :=
  (restrictFunctor (Spec.map φ)).mapIso E ≪≫ canonicalAmbientTopOpenIso α φ n

private theorem coefficientFrame_eq
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (φ : A ⟶ A')
    [IsOpenImmersion (Spec.map φ)] (n : ℕ) {L : (Spec A).Modules}
    (E : L ≅ moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) :
    coefficientFrame α φ n E =
      (restrictFunctor (Spec.map φ)).mapIso E ≪≫ canonicalAmbientTopOpenIso α φ n := rfl

private def coefficientMap
    {A A' B B' : CommRingCat.{u}} (σ : A ⟶ B) (τ : A' ⟶ B')
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ τ = σ ≫ ψ) (L : (Spec A).Modules) :
    ((pullback (Spec.map σ)).obj L).restrict (Spec.map ψ) ⟶
      (pullback (Spec.map τ)).obj (L.restrict (Spec.map φ)) :=
  (canonicalPullbackOpenSquareIso (Spec.map σ) (Spec.map τ) (Spec.map ψ) (Spec.map φ)
    (canonicalAmbientClosedSquare φ σ τ ψ h)).hom.app L

private theorem coefficientMap_eq
    {A A' B B' : CommRingCat.{u}} (σ : A ⟶ B) (τ : A' ⟶ B')
    (φ : A ⟶ A') (ψ : B ⟶ B')
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ τ = σ ≫ ψ) (L : (Spec A).Modules) :
    coefficientMap σ τ φ ψ h L =
      (canonicalPullbackOpenSquareIso (Spec.map σ) (Spec.map τ) (Spec.map ψ) (Spec.map φ)
        (canonicalAmbientClosedSquare φ σ τ ψ h)).hom.app L := rfl

private theorem ambientCoefficient_bridge
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
    (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ) (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α))
    (bA' : Module.Basis (Fin n) A' (CommRingCat.KaehlerDifferential (α ≫ φ))) :
    (restrictFunctor (Spec.map ψ)).map (affineConormalAmbientCoefficientIso α s n bA).hom ≫
        (canonicalAmbientTopCoefficientOpenIso α φ (regularListQuotientMap s)
          (regularListQuotientMap t) ψ h n).hom =
      canonicalExteriorOpenMap (Spec.map ψ)
        ((pullback (Spec.map (regularListQuotientMap s))).obj
          (relativeDifferentialSheaf (Spec.map α)))
        ((pullback (Spec.map (regularListQuotientMap t))).obj
          (relativeDifferentialSheaf (Spec.map (α ≫ φ)))) n
        (canonicalAmbientConormalMiddleIso α φ (regularListQuotientMap s)
          (regularListQuotientMap t) ψ h).hom ≫
        (affineConormalAmbientCoefficientIso (α ≫ φ) t n bA').hom :=
  canonicalOpenAmbientCoefficient α (α ≫ φ) s t n bA bA' (Spec.map ψ) (Spec.map φ)
    (canonicalAmbientClosedSquare φ (regularListQuotientMap s) (regularListQuotientMap t) ψ h)
    (canonicalAmbientDifferentialOpenIso α φ)

private theorem ambientCoefficient_transport
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
    (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ) (n : ℕ)
    {L : (Spec A).Modules}
    (E : L ≅ moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) :
    (restrictFunctor (Spec.map ψ)).map
        (((pullback (Spec.map (regularListQuotientMap s))).mapIso E.symm).hom) ≫
        (canonicalPullbackOpenSquareIso (Spec.map (regularListQuotientMap s))
          (Spec.map (regularListQuotientMap t)) (Spec.map ψ) (Spec.map φ)
          (canonicalAmbientClosedSquare φ (regularListQuotientMap s)
            (regularListQuotientMap t) ψ h)).hom.app L =
      (canonicalAmbientTopCoefficientOpenIso α φ (regularListQuotientMap s)
        (regularListQuotientMap t) ψ h n).hom ≫
        ((pullback (Spec.map (regularListQuotientMap t))).mapIso
          (((restrictFunctor (Spec.map φ)).mapIso E ≪≫
            canonicalAmbientTopOpenIso α φ n).symm)).hom :=
  coefficientTransport_naturality (pullback (Spec.map (regularListQuotientMap s)))
    (pullback (Spec.map (regularListQuotientMap t)))
    (restrictFunctor (Spec.map φ)) (restrictFunctor (Spec.map ψ))
    (canonicalPullbackOpenSquareIso (Spec.map (regularListQuotientMap s))
      (Spec.map (regularListQuotientMap t)) (Spec.map ψ) (Spec.map φ)
      (canonicalAmbientClosedSquare φ (regularListQuotientMap s)
        (regularListQuotientMap t) ψ h)) E (canonicalAmbientTopOpenIso α φ n)

private theorem ambientCoefficient_transport_named
    {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
    (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
    (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ) (n : ℕ)
    {L : (Spec A).Modules}
    (E : L ≅ moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) :
    (restrictFunctor (Spec.map ψ)).map
        (((pullback (Spec.map (regularListQuotientMap s))).mapIso E.symm).hom) ≫
        coefficientMap (regularListQuotientMap s) (regularListQuotientMap t) φ ψ h L =
      (canonicalAmbientTopCoefficientOpenIso α φ (regularListQuotientMap s)
        (regularListQuotientMap t) ψ h n).hom ≫
        ((pullback (Spec.map (regularListQuotientMap t))).mapIso
          (coefficientFrame α φ n E).symm).hom := by
  have hSource := congrArg (fun f =>
    (restrictFunctor (Spec.map ψ)).map
      (((pullback (Spec.map (regularListQuotientMap s))).mapIso E.symm).hom) ≫ f)
    (coefficientMap_eq (regularListQuotientMap s) (regularListQuotientMap t) φ ψ h L)
  have hTarget := congrArg (fun e : L.restrict (Spec.map φ) ≅
      moduleExteriorPower (Spec A') (relativeDifferentialSheaf (Spec.map (α ≫ φ))) n =>
    (canonicalAmbientTopCoefficientOpenIso α φ (regularListQuotientMap s)
      (regularListQuotientMap t) ψ h n).hom ≫
      ((pullback (Spec.map (regularListQuotientMap t))).mapIso e.symm).hom)
    (coefficientFrame_eq α φ n E)
  exact hSource.trans ((ambientCoefficient_transport α s t φ ψ h n E).trans hTarget.symm)

section ActualSquare

variable {R A A' : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (t : List A')
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  (ht : RingTheory.Sequence.IsWeaklyRegular A' t)
  (φ : A ⟶ A') (ψ : regularListQuotientRing s ⟶ regularListQuotientRing t)
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  (h : φ ≫ regularListQuotientMap t = regularListQuotientMap s ≫ ψ)
  (hA : α.hom.FormallySmooth)
  (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
  (hA' : (α ≫ φ).hom.FormallySmooth)
  (hB' : ((α ≫ φ) ≫ regularListQuotientMap t).hom.FormallySmooth)
  {d : ℕ} (bA : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential α))
  (bA' : Module.Basis (Fin (s.length + d)) A' (CommRingCat.KaehlerDifferential (α ≫ φ)))
  (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
    (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
  (bQ' : Module.Basis (Fin d) (regularListQuotientRing t)
    (CommRingCat.KaehlerDifferential ((α ≫ φ) ≫ regularListQuotientMap t)))
  (hc : t.length = s.length)

local notation "q" => regularListQuotientMap s
local notation "q'" => regularListQuotientMap t
local notation "p" => Spec.map ψ
local notation "j" => Spec.map φ
local notation "n" => s.length + d
local notation "Ωtop" => moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n
local notation "Ωtop'" => moduleExteriorPower (Spec A')
  (relativeDifferentialSheaf (Spec.map (α ≫ φ))) n
local notation "Ctop" => regularListNormalAt (Ideal.ofList s) s.length
local notation "Ctop'" => regularListNormalAt (Ideal.ofList t) s.length
local notation "Qtop" => regularListTangentTopAt α (Ideal.ofList s) d
local notation "Qtop'" => regularListTangentTopAt (α ≫ φ) (Ideal.ofList t) d
local notation "Mtop" => regularListMiddleTopAt α (Ideal.ofList s) n
local notation "Mtop'" => regularListMiddleTopAt (α ≫ φ) (Ideal.ofList t) n
local notation "Ptop" => Functor.obj (pullback (Spec.map q)) Ωtop
local notation "Ptop'" => Functor.obj (pullback (Spec.map q')) Ωtop'
local notation "δ" => regularListConormalDeterminantAt α (Ideal.ofList s) s.length d
  hA hB bQ s hs rfl rfl
local notation "δ'" => regularListConormalDeterminantAt (α ≫ φ) (Ideal.ofList t) s.length d
  hA' hB' bQ' t ht rfl hc
local notation "D" => regularListCanonicalDeterminantAt α (Ideal.ofList s) s.length d
  hA hB bA bQ s hs rfl rfl
local notation "D'" => regularListCanonicalDeterminantAt (α ≫ φ) (Ideal.ofList t) s.length d
  hA' hB' bA' bQ' t ht rfl hc
local notation "aC" => canonicalExteriorOpenMap p
  (Functor.obj (pullback (Spec.map q)) (Hom.idealModule (Spec.map q)))
  (Functor.obj (pullback (Spec.map q')) (Hom.idealModule (Spec.map q'))) s.length
  (canonicalNormalOpenSquareMap (Spec.map q) (Spec.map q') j p
    (canonicalAmbientClosedSquare φ q q' ψ h))
local notation "aQ" => canonicalExteriorOpenMap p
  (relativeDifferentialSheaf (Spec.map (α ≫ q)))
  (relativeDifferentialSheaf (Spec.map ((α ≫ φ) ≫ q'))) d
  (Iso.hom (canonicalAmbientConormalTangentIso α φ q q' ψ h))
local notation "aM" => canonicalExteriorOpenMap p
  (Functor.obj (pullback (Spec.map q)) (relativeDifferentialSheaf (Spec.map α)))
  (Functor.obj (pullback (Spec.map q')) (relativeDifferentialSheaf (Spec.map (α ≫ φ)))) n
  (Iso.hom (canonicalAmbientConormalMiddleIso α φ q q' ψ h))
local notation "eC" => canonicalAmbientTopCoefficientOpenIso α φ q q' ψ h n
local notation "S" => canonicalPullbackOpenSquareIso (Spec.map q) (Spec.map q') p j
  (canonicalAmbientClosedSquare φ q q' ψ h)

local notation "aS" => canonicalTensorOpenMap p Ctop Qtop Ctop' Qtop' aC aQ

/-- The literal original canonical determinant square with the actual ambient-top coefficient. -/
def CanonicalAmbientDeterminantSquare : Prop :=
  CanonicalDeterminantOpenSquare p Ctop Qtop Ptop Ctop' Qtop' Ptop' D D' aC aQ (eC).hom

/-- The accepted intrinsic determinant and original ambient bridge give the whole
canonical square. -/
theorem canonicalAmbientDeterminant :
    CanonicalAmbientDeterminantSquare α s t hs ht φ ψ h hA hB hA' hB' bA bA' bQ bQ' hc := by
  exact determinantCoefficientSquare p
    (C := Ctop) (Q := Qtop) (M := Mtop) (P := Ptop)
    (C' := Ctop') (Q' := Qtop') (M' := Mtop') (P' := Ptop')
    δ δ' D D'
    (affineConormalAmbientCoefficientIso α s n bA)
    (affineConormalAmbientCoefficientIso (α ≫ φ) t n bA')
    aC aQ aM (eC).hom
    (canonicalDeterminantAt_hom α s hs hA hB bA bQ rfl)
    (canonicalDeterminantAt_hom (α ≫ φ) t ht hA' hB' bA' bQ' hc)
    (canonicalAmbientConormalDeterminant α s t hs ht φ ψ h hA hB hA' hB' bQ bQ' hc)
    (ambientCoefficient_bridge α s t φ ψ h n bA bA')

private theorem canonicalAmbientDeterminant_hom :
    (restrictFunctor p).map (D).hom ≫ (eC).hom = aS ≫ (D').hom :=
  (canonicalDeterminantOpenSquare_iff p Ctop Qtop Ptop Ctop' Qtop' Ptop'
    D D' aC aQ (eC).hom).1
    (canonicalAmbientDeterminant α s t hs ht φ ψ h hA hB hA' hB' bA bA' bQ bQ' hc)

private theorem coefficientDeterminant_of_transport
    {L : (Spec A).Modules} {L' : (Spec A').Modules}
    (E : L ≅ Ωtop) (E' : L' ≅ Ωtop')
    (aL : (restrictFunctor p).obj ((pullback (Spec.map q)).obj L) ⟶
      (pullback (Spec.map q')).obj L')
    (hE : (restrictFunctor p).map (((pullback (Spec.map q)).mapIso E.symm).hom) ≫ aL =
      (eC).hom ≫ ((pullback (Spec.map q')).mapIso E'.symm).hom) :
    (restrictFunctor p).map
        (regularListCanonicalCoefficientDeterminantAt α s hs s.length d
          hA hB bA bQ rfl (L := L) E).hom ≫
        aL =
      aS ≫ (regularListCanonicalCoefficientDeterminantAt (α ≫ φ) t ht s.length d
        hA' hB' bA' bQ' hc (L := L') E').hom := by
  exact pasteHomSquares (restrictFunctor p)
    (X := tensorSheaf (Spec (regularListQuotientRing s)) Ctop Qtop)
    (Y := Ptop) (Z := (pullback (Spec.map q)).obj L)
    (X' := tensorSheaf (Spec (regularListQuotientRing t)) Ctop' Qtop')
    (Y' := Ptop') (Z' := (pullback (Spec.map q')).obj L')
    (D).hom (((pullback (Spec.map q)).mapIso E.symm).hom)
    (D').hom (((pullback (Spec.map q')).mapIso E'.symm).hom)
    aS (eC).hom aL
    (k := (regularListCanonicalCoefficientDeterminantAt α s hs s.length d
      hA hB bA bQ rfl (L := L) E).hom)
    (k' := (regularListCanonicalCoefficientDeterminantAt (α ≫ φ) t ht s.length d
      hA' hB' bA' bQ' hc (L := L') E').hom)
    (canonicalCoefficientDeterminantAt_hom α s hs s.length d hA hB bA bQ rfl (L := L) E)
    (canonicalCoefficientDeterminantAt_hom (α ≫ φ) t ht s.length d hA' hB' bA' bQ' hc (L := L') E')
    (canonicalAmbientDeterminant_hom α s t hs ht φ ψ h hA hB hA' hB' bA bA' bQ bQ' hc)
    hE

private theorem coefficientDeterminant_named {L : (Spec A).Modules} (E : L ≅ Ωtop) :
    (restrictFunctor p).map
        (regularListCanonicalCoefficientDeterminantAt α s hs s.length d
          hA hB bA bQ rfl (L := L) E).hom ≫
        coefficientMap q q' φ ψ h L =
      aS ≫ (regularListCanonicalCoefficientDeterminantAt (α ≫ φ) t ht s.length d
        hA' hB' bA' bQ' hc (L := L.restrict j) (coefficientFrame α φ n E)).hom :=
  coefficientDeterminant_of_transport α s t hs ht φ ψ h
    hA hB hA' hB' bA bA' bQ bQ' hc (L := L) (L' := L.restrict j)
    E (coefficientFrame α φ n E) (coefficientMap q q' φ ψ h L)
    (ambientCoefficient_transport_named α s t φ ψ h n E)

private theorem coefficientDeterminant_sourceEq {L : (Spec A).Modules} (E : L ≅ Ωtop) :
    (restrictFunctor p).map
        (regularListCanonicalCoefficientDeterminantAt α s hs s.length d
          hA hB bA bQ rfl (L := L) E).hom ≫
        coefficientMap q q' φ ψ h L =
      (restrictFunctor p).map
        (regularListCanonicalCoefficientDeterminantAt α s hs s.length d
          hA hB bA bQ rfl (L := L) E).hom ≫
        (S).hom.app L :=
  congrArg (fun f : (restrictFunctor p).obj ((pullback (Spec.map q)).obj L) ⟶
      (pullback (Spec.map q')).obj (L.restrict j) =>
    (restrictFunctor p).map
      (regularListCanonicalCoefficientDeterminantAt α s hs s.length d
        hA hB bA bQ rfl (L := L) E).hom ≫ f)
    (coefficientMap_eq q q' φ ψ h L)

private theorem coefficientDeterminant_targetEq {L : (Spec A).Modules} (E : L ≅ Ωtop) :
    aS ≫ (regularListCanonicalCoefficientDeterminantAt (α ≫ φ) t ht s.length d
        hA' hB' bA' bQ' hc (L := L.restrict j) (coefficientFrame α φ n E)).hom =
      aS ≫ (regularListCanonicalCoefficientDeterminantAt (α ≫ φ) t ht s.length d
        hA' hB' bA' bQ' hc (L := L.restrict j)
        ((restrictFunctor j).mapIso E ≪≫ canonicalAmbientTopOpenIso α φ n)).hom :=
  congrArg (fun e : L.restrict j ≅ Ωtop' =>
    aS ≫ (regularListCanonicalCoefficientDeterminantAt (α ≫ φ) t ht s.length d
      hA' hB' bA' bQ' hc (L := L.restrict j) e).hom) (coefficientFrame_eq α φ n E)

/-- Any actual coefficient frame gives the literal original determinant square.
The target frame is its actual restriction followed by the ambient top isomorphism. -/
theorem canonicalAmbientCoefficientDeterminant
    {L : (Spec A).Modules} (E : L ≅ Ωtop) :
    (restrictFunctor p).map
        (regularListCanonicalCoefficientDeterminantAt α s hs s.length d
          hA hB bA bQ rfl (L := L) E).hom ≫ (S).hom.app L =
      aS ≫ (regularListCanonicalCoefficientDeterminantAt (α ≫ φ) t ht s.length d
        hA' hB' bA' bQ' hc (L := L.restrict j)
        ((restrictFunctor j).mapIso E ≪≫ canonicalAmbientTopOpenIso α φ n)).hom := by
  exact (coefficientDeterminant_sourceEq α s t hs φ ψ h hA hB bA bQ E).symm.trans
    ((coefficientDeterminant_named α s t hs ht φ ψ h hA hB hA' hB' bA bA' bQ bQ' hc E).trans
      (coefficientDeterminant_targetEq α s t ht φ ψ h hA' hB' bA' bQ' hc E))


end ActualSquare
end AlgebraicGeometry.Scheme.Modules
