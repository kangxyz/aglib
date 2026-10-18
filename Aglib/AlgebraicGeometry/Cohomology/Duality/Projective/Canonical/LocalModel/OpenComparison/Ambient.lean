/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenComparison.Geometry

/-!
# The actual ambient-isomorphism canonical model square

The original ambient model map carries the original Koszul class to the
same mapped-list class. Actual ordered-normal, determinant and coefficient
transport therefore identify the original canonical model arrows.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials

universe u w z
namespace AlgebraicGeometry.Scheme.Modules

section Ambient
variable {R A A' : CommRingCat.{u}} (α : R ⟶ A) (a : A ≃+* A') (s : List A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  (ht : RingTheory.Sequence.IsWeaklyRegular A' (s.map a.toRingHom))

variable (hA : α.hom.FormallySmooth)
  (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
  (hA' : (α ≫ a.toCommRingCatIso.hom).hom.FormallySmooth)
  (hB' : ((α ≫ a.toCommRingCatIso.hom) ≫
    regularListQuotientMap (s.map a.toRingHom)).hom.FormallySmooth)
  {d : ℕ} (bA : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential α))
  (bA' : Module.Basis (Fin (s.length + d)) A'
    (CommRingCat.KaehlerDifferential (α ≫ a.toCommRingCatIso.hom)))
  (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
    (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
  (bQ' : Module.Basis (Fin d) (regularListQuotientRing (s.map a.toRingHom))
    (CommRingCat.KaehlerDifferential ((α ≫ a.toCommRingCatIso.hom) ≫
      regularListQuotientMap (s.map a.toRingHom))))
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (J : InjectiveResolution L) (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  (E : L ≅ moduleExteriorPower (Spec A)
    (relativeDifferentialSheaf (Spec.map α)) (s.length + d))
  [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} A')]

local notation "t" => List.map (RingEquiv.toRingHom a) s
local notation "φ" => Iso.hom (RingEquiv.toCommRingCatIso a)
local notation "ψ" => Iso.hom (RingEquiv.toCommRingCatIso (regularListAmbientQuotientEquiv a s))
local notation "h" => Eq.symm (regularListAmbientRingSquare a s)

local instance : IsClosedImmersion (Spec.map (regularListQuotientMap s)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
local instance : IsClosedImmersion (Spec.map (regularListQuotientMap t)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The actual original ambient homology map intertwines the original canonical model arrows.
All normal, determinant, coefficient and original class equations are discharged. -/
theorem regularListCanonicalModelTopHomologyIso_ambient :
    CanonicalRegularListModelOpenSquare (A' := A') α s t hs ht φ ψ h hA hB hA' hB'
      bA bA' bQ bQ' (List.length_map (as := s) a.toRingHom) J e E
      (canonicalAmbientSheafHomologyMap φ (regularListQuotientMap s)
        (regularListQuotientMap t) ψ (regularListAmbientSquare a s) J (s.length : ℤ)) := by
  let := a.toRingHom.toAlgebra
  let : Module.Flat A A' :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective a.bijective)
  refine regularListCanonicalModelTopHomologyIso_open_of_modelTopClass
    (A' := A') α s t hs ht φ ψ h hA hB hA' hB' bA bA' bQ bQ'
    (List.length_map (as := s) a.toRingHom) J e E ?_
    (canonicalAmbientSheafHomologyMap φ (regularListQuotientMap s)
      (regularListQuotientMap t) ψ (regularListAmbientSquare a s) J (s.length : ℤ)) ?_
  · intro i
    simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]
    rfl
  · have hClass := regularListAmbientSheafHomologyMap_modelTopClass a s hs e J (1 : A) ⊤
    dsimp only at hClass
    simpa only [regularListOpenCoefficientFrame_ambient, map_one] using hClass

end Ambient
end AlgebraicGeometry.Scheme.Modules
