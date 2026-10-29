/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.FieldTheory.Finite.Basic

/-! # Artin--Schreier coefficient maps for the original ring sections

The selected ring-valued presheaf and its original additive universe lift
carry Frobenius, residue constants and the literal power-minus-identity map.
Only the objectwise equation `p = 0` is required, including for zero rings.
The supplied additive sheaf proof and native sheafification adjunction are
reused; no local exactness assertion is made here.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf.ArtinSchreier

universe u v r w u₁ u₂ v₁ v₂

/-- Transport the whole original composite equation through a variable adjunction. -/
private theorem transpose_comp_eq_zero
    {D : Type u₁} [Category.{v₁} D] [Preadditive D]
    {E : Type u₂} [Category.{v₂} E] [Preadditive E]
    {L : D ⥤ E} {U : E ⥤ D} [U.Additive] (adj : L ⊣ U)
    (P : D) (A B : E) (i : P ⟶ U.obj A) (k : L.obj P ⟶ A) (g : A ⟶ B)
    (hk : (adj.homEquiv P A) k = i) (hz : i ≫ U.map g = 0) : k ≫ g = 0 := by
  let : L.Additive := adj.left_adjoint_additive
  apply (adj.homEquiv P B).injective
  exact (adj.homEquiv_naturality_right (X := P) (Y := A) (Y' := B) k g).trans
    ((congrArg (fun t : P ⟶ U.obj A => t ≫ U.map g) hk).trans
      (hz.trans (adj.homAddEquiv_zero P B).symm))


/-- The native prime-field additive coefficient group in the chosen value world. -/
def primeFieldCoefficient (p : ℕ) : AddCommGrpCat.{w} :=
  AddCommGrpCat.of (ULift.{w} (ZMod p))

/-- Original residue constants with the same single additive universe lift. -/
def primeFieldSectionHom {T : Type r} [CommRing T] (p : ℕ) (hT : (p : T) = 0) :
    ULift.{max r w} (ZMod p) →+ ULift.{w} T where
  toFun a := ULift.up (ZMod.castHom (ringChar.dvd hT) T a.down)
  map_zero' := by
    apply ULift.ext
    exact map_zero _
  map_add' a b := by
    apply ULift.ext
    exact map_add _ a.down b.down

/-- The same native single-lift additive presheaf, with the lift world explicit. -/
abbrev additivePresheaf.{w', r', v', u'} {C : Type u'} [Category.{v'} C]
    (R : Cᵒᵖ ⥤ CommRingCat.{r'}) : Cᵒᵖ ⥤ AddCommGrpCat.{max r' w'} :=
  R ⋙ forget₂ CommRingCat.{r'} RingCat.{r'} ⋙
    forget₂ RingCat.{r'} AddCommGrpCat.{r'} ⋙ AddCommGrpCat.uliftFunctor.{w', r'}

/-- The same native sheaf pair, retaining the supplied original sheaf proof. -/
abbrev additiveSheaf.{w', r', v', u'} {C : Type u'} [Category.{v'} C]
    (R : Cᵒᵖ ⥤ CommRingCat.{r'}) (J : GrothendieckTopology C)
    (hR : Presheaf.IsSheaf J (additivePresheaf.{w'} R)) :
    Sheaf J AddCommGrpCat.{max r' w'} :=
  ⟨additivePresheaf.{w'} R, hR⟩

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{r})

/-- The constant-presheaf map is the original residue scalar at each ring section. -/
def primeFieldPresheafMap (p : ℕ) (h : ∀ U : Cᵒᵖ, (p : R.obj U) = 0) :
    (Functor.const Cᵒᵖ).obj (primeFieldCoefficient.{max r w} p) ⟶ (additivePresheaf.{w} R) where
  app U := AddCommGrpCat.ofHom
    (primeFieldSectionHom (T := R.obj U) p (h U))
  naturality {U V} f := by
    ext a
    apply ULift.ext
    change ZMod.castHom (ringChar.dvd (h V)) (R.obj V) a.down =
      (R.map f).hom (ZMod.castHom (ringChar.dvd (h U)) (R.obj U) a.down)
    exact (RingHom.congr_fun (Subsingleton.elim
      ((R.map f).hom.comp (ZMod.castHom (ringChar.dvd (h U)) (R.obj U)))
      (ZMod.castHom (ringChar.dvd (h V)) (R.obj V))) a.down).symm

variable (J : GrothendieckTopology C) (hR : Presheaf.IsSheaf J (additivePresheaf.{w} R))

/-- Frobenius on the same original additive sheaf of ring sections. -/
def frobenius (p : ℕ) (hp : p.Prime) (h : ∀ U : Cᵒᵖ, (p : R.obj U) = 0) :
    (additiveSheaf.{w} R J hR) ⟶ (additiveSheaf.{w} R J hR) where
  hom := {
    app U := AddCommGrpCat.uliftFunctor.map (AddCommGrpCat.ofHom
      (RingHom.frobeniusOfPrimeCastEqZero p hp (h U)).toAddMonoidHom)
    naturality {U V} f := by
      ext x
      apply ULift.ext
      let a : R.obj U := x.down
      change (R.map f).hom a ^ p = (R.map f).hom (a ^ p)
      exact (map_pow (R.map f).hom a p).symm }

/-- The original power-minus-identity map on this selected additive sheaf. -/
def artinSchreierMap (p : ℕ) (hp : p.Prime) (h : ∀ U : Cᵒᵖ, (p : R.obj U) = 0) :
    (additiveSheaf.{w} R J hR) ⟶ (additiveSheaf.{w} R J hR) :=
  frobenius R J hR p hp h - 𝟙 _

/-- Its component retains the literal original ring value. -/
theorem artinSchreierMap_apply (p : ℕ) (hp : p.Prime)
    (h : ∀ U : Cᵒᵖ, (p : R.obj U) = 0) (U : Cᵒᵖ) (x : ULift.{w} (R.obj U)) :
    ((artinSchreierMap R J hR p hp h).hom.app U x).down = x.down ^ p - x.down := rfl

variable [HasWeakSheafify J AddCommGrpCat.{max r w}]

/-- Transpose the original residue map through the native sheafification adjunction. -/
def primeFieldToAdditive (p : ℕ) (h : ∀ U : Cᵒᵖ, (p : R.obj U) = 0) :
    (constantSheaf J AddCommGrpCat.{max r w}).obj (primeFieldCoefficient.{max r w} p) ⟶
      (additiveSheaf.{w} R J hR) :=
  ((sheafificationAdjunction J AddCommGrpCat.{max r w}).homEquiv
    ((Functor.const Cᵒᵖ).obj (primeFieldCoefficient.{max r w} p)) (additiveSheaf.{w} R J hR)).symm
      (primeFieldPresheafMap R p h)

/-- The whole original unit equation identifies the transposed residue map. -/
theorem toSheafify_primeFieldToAdditive (p : ℕ)
    (h : ∀ U : Cᵒᵖ, (p : R.obj U) = 0) :
    toSheafify J ((Functor.const Cᵒᵖ).obj (primeFieldCoefficient.{max r w} p)) ≫
      (primeFieldToAdditive R J hR p h).hom = primeFieldPresheafMap R p h := by
  exact ((sheafificationAdjunction J AddCommGrpCat.{max r w}).homEquiv _ _).apply_symm_apply _

/-- Original prime-field constants are annihilated by power-minus-identity. -/
theorem primeFieldToAdditive_artinSchreierMap (p : ℕ) (hp : p.Prime)
    (h : ∀ U : Cᵒᵖ, (p : R.obj U) = 0) :
    primeFieldToAdditive R J hR p h ≫ artinSchreierMap R J hR p hp h = 0 := by
  let P₀ : Cᵒᵖ ⥤ AddCommGrpCat.{max r w} :=
    (Functor.const Cᵒᵖ).obj (primeFieldCoefficient.{max r w} p)
  let A₀ : Sheaf J AddCommGrpCat.{max r w} := additiveSheaf.{w} R J hR
  let i₀ : P₀ ⟶ A₀.obj := primeFieldPresheafMap R p h
  let k₀ : (presheafToSheaf J AddCommGrpCat.{max r w}).obj P₀ ⟶ A₀ :=
    primeFieldToAdditive R J hR p h
  let g₀ : A₀ ⟶ A₀ := artinSchreierMap R J hR p hp h
  have hk₀ : (sheafificationAdjunction J AddCommGrpCat.{max r w}).homEquiv P₀ A₀ k₀ = i₀ :=
    toSheafify_primeFieldToAdditive R J hR p h
  have hz : i₀ ≫ (sheafToPresheaf J AddCommGrpCat.{max r w}).map g₀ = 0 := by
    ext U a
    apply ULift.ext
    change (ZMod.castHom (ringChar.dvd (h U)) (R.obj U) a.down) ^ p -
      ZMod.castHom (ringChar.dvd (h U)) (R.obj U) a.down = 0
    let : Fact p.Prime := ⟨hp⟩
    rw [← map_pow, ZMod.pow_card, sub_self]
  exact transpose_comp_eq_zero
    (L := presheafToSheaf J AddCommGrpCat.{max r w})
    (U := sheafToPresheaf J AddCommGrpCat.{max r w})
    (sheafificationAdjunction J AddCommGrpCat.{max r w}) P₀ A₀ A₀ i₀ k₀ g₀ hk₀ hz

end CategoryTheory.Sheaf.ArtinSchreier
