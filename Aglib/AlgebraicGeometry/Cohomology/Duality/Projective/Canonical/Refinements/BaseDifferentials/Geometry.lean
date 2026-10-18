/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.BaseDifferentials

/-!
# The actual affine differential map under an open change of base

The original relative derivation determines the identity/source-open map.
The native affine comparison and the tilde–global-sections adjunction then
identify this same arrow from its values on the original ring differentials.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem identityOpenSquare_d
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion j] (h : 𝟙 X ≫ f = g ≫ j) (V : X.Opens) (a : Γ(X, V)) :
    ((restrictFunctorId (X := X)).inv.app (relativeDifferentialSheaf f) ≫
      (relativeDifferentialOpenSquareIso f (𝟙 X) g j h).hom).val.app (op V)
        ((relativeDifferentialDerivation f).d a) =
      (relativeDifferentialDerivation g).d a := by
  change (relativeDifferentialOpenSquareIso f (𝟙 X) g j h).hom.val.app (op V)
    (((restrictFunctorId (X := X)).inv.app (relativeDifferentialSheaf f)).app V
      ((relativeDifferentialDerivation f).d a)) = _
  rw [restrictFunctorId_inv_app_app]
  let e : 𝟙 X ''ᵁ V = V := by simp
  have hr : (relativeDifferentialSheaf f).presheaf.map (eqToHom e).op
        ((relativeDifferentialDerivation f).d a) =
      (relativeDifferentialDerivation f).d (X.presheaf.map (eqToHom e).op a) :=
    (relativeDifferentialDerivation_restrict f (eqToHom e).op a).symm
  have hs : (Scheme.Hom.appIso (𝟙 X) V).hom
      (X.presheaf.map (eqToHom e).op a) = a := by
    simp [Scheme.Hom.id_appIso]
  exact (congrArg
    (fun z => (relativeDifferentialOpenSquareIso f (𝟙 X) g j h).hom.val.app (op V) z) hr).trans
    ((relativeDifferentialOpenSquareIso_hom_d f (𝟙 X) g j h V
      (X.presheaf.map (eqToHom e).op a)).trans
        (congrArg (relativeDifferentialDerivation g).d hs))

private theorem baseDifferentialTilde_toOpen {A : CommRingCat.{u}} {M N : ModuleCat.{u} A}
    (φ : M ⟶ N) (V : (Spec A).Opens) (m : M) :
    ((tilde.functor A).map φ).val.app (op V) (tilde.toOpen M V m) =
      tilde.toOpen N V (φ m) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app φ V) m

variable {R S A : CommRingCat.{u}} (ρ : R ⟶ S) (β : S ⟶ A)
  [IsOpenImmersion (Spec.map ρ)]

/-- The actual source-identity/base-open map between relative differential sheaves. -/
def canonicalBaseDifferentialSheafMap
    (h : 𝟙 (Spec A) ≫ Spec.map (ρ ≫ β) = Spec.map β ≫ Spec.map ρ) :
    relativeDifferentialSheaf (Spec.map (ρ ≫ β)) ⟶
      relativeDifferentialSheaf (Spec.map β) :=
  (restrictFunctorId (X := Spec A)).inv.app
      (relativeDifferentialSheaf (Spec.map (ρ ≫ β))) ≫
    (relativeDifferentialOpenSquareIso (Spec.map (ρ ≫ β)) (𝟙 (Spec A))
      (Spec.map β) (Spec.map ρ) h).hom

/-- The actual geometric base map carries every original differential to itself. -/
theorem canonicalBaseDifferentialSheafMap_d
    (h : 𝟙 (Spec A) ≫ Spec.map (ρ ≫ β) = Spec.map β ≫ Spec.map ρ)
    (V : (Spec A).Opens) (a : Γ(Spec A, V)) :
    (canonicalBaseDifferentialSheafMap ρ β h).val.app (op V)
        ((relativeDifferentialDerivation (Spec.map (ρ ≫ β))).d a) =
      (relativeDifferentialDerivation (Spec.map β)).d a :=
  identityOpenSquare_d (Spec.map (ρ ≫ β)) (Spec.map β) (Spec.map ρ) h V a

private theorem canonicalBaseDifferentialMap_geometry_of_d
    (h : 𝟙 (Spec A) ≫ Spec.map (ρ ≫ β) = Spec.map β ≫ Spec.map ρ)
    (φ : CommRingCat.KaehlerDifferential (ρ ≫ β) ⟶ CommRingCat.KaehlerDifferential β)
    (hφ : ∀ a : A, φ (CommRingCat.KaehlerDifferential.d (f := ρ ≫ β) a) =
      CommRingCat.KaehlerDifferential.d (f := β) a) :
    canonicalBaseDifferentialSheafMap ρ β h =
      (relativeDifferentialAffineIso (ρ ≫ β)).hom ≫ (tilde.functor A).map φ ≫
        (relativeDifferentialAffineIso β).inv := by
  apply (cancel_epi (relativeDifferentialAffineIso (ρ ≫ β)).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply ((tilde.adjunction (R := A)).homEquiv _ _).injective
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (canonicalBaseDifferentialSheafMap ρ β h).val.app (op ⊤)
      ((relativeDifferentialAffineIso (ρ ≫ β)).inv.val.app (op ⊤)
        (tilde.toOpen (CommRingCat.KaehlerDifferential (ρ ≫ β)) ⊤
          (CommRingCat.KaehlerDifferential.d (f := ρ ≫ β) a))) =
    (relativeDifferentialAffineIso β).inv.val.app (op ⊤)
      (((tilde.functor A).map φ).val.app (op ⊤)
        (tilde.toOpen (CommRingCat.KaehlerDifferential (ρ ≫ β)) ⊤
          (CommRingCat.KaehlerDifferential.d (f := ρ ≫ β) a)))
  have hα := relativeDifferentialAffineIso_inv_d (ρ ≫ β) (1 : A) a
  have hβ := relativeDifferentialAffineIso_inv_d β (1 : A) a
  rw! [PrimeSpectrum.basicOpen_one] at hα hβ
  rw [hα, canonicalBaseDifferentialSheafMap_d, baseDifferentialTilde_toOpen, hφ, hβ]

/-- The actual identity/source-open differential arrow is the tilde of the original
native algebraic base-differential map under the original affine comparisons. -/
theorem canonicalBaseDifferentialMap_geometry
    (h : 𝟙 (Spec A) ≫ Spec.map (ρ ≫ β) = Spec.map β ≫ Spec.map ρ) :
    (restrictFunctorId (X := Spec A)).inv.app
        (relativeDifferentialSheaf (Spec.map (ρ ≫ β))) ≫
      (relativeDifferentialOpenSquareIso (Spec.map (ρ ≫ β)) (𝟙 (Spec A))
        (Spec.map β) (Spec.map ρ) h).hom =
      (relativeDifferentialAffineIso (ρ ≫ β)).hom ≫
        (tilde.functor A).map (canonicalBaseDifferentialMap ρ β) ≫
        (relativeDifferentialAffineIso β).inv :=
  canonicalBaseDifferentialMap_geometry_of_d ρ β h (canonicalBaseDifferentialMap ρ β)
    (canonicalBaseDifferentialMap_d ρ β)

end AlgebraicGeometry.Scheme.Modules
