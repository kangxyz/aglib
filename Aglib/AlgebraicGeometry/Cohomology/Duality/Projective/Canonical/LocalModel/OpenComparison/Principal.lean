/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenComparison.Geometry
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.Class.Principal.Quotient

/-!
# The actual principal-open canonical model square

The same original two-stage principal map, presented by its original
restriction-composition and congruence isomorphisms, carries class one to
the original localized-list class. All canonical determinant, normal and
coefficient comparisons are consequently the actual original arrows.
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

section Principal
variable {R A : CommRingCat.{u}} (α : R ⟶ A) (s : List A) (r : A)
  (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  (ht : RingTheory.Sequence.IsWeaklyRegular (Localization.Away r) (regularListPrincipalList s r))

variable (hA : α.hom.FormallySmooth)
  (hB : (α ≫ regularListQuotientMap s).hom.FormallySmooth)
  (hA' : (α ≫ (CommRingCat.ofHom (algebraMap A (Localization.Away r)) :
    A ⟶ CommRingCat.of (Localization.Away r))).hom.FormallySmooth)
  (hB' : ((α ≫ (CommRingCat.ofHom (algebraMap A (Localization.Away r)) :
    A ⟶ CommRingCat.of (Localization.Away r))) ≫
      regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
        (regularListPrincipalList s r)).hom.FormallySmooth)
  {d : ℕ} (bA : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential α))
  (bA' : Module.Basis (Fin (s.length + d)) (CommRingCat.of (Localization.Away r))
    (CommRingCat.KaehlerDifferential (α ≫
      (CommRingCat.ofHom (algebraMap A (Localization.Away r)) :
        A ⟶ CommRingCat.of (Localization.Away r)))))
  (bQ : Module.Basis (Fin d) (regularListQuotientRing s)
    (CommRingCat.KaehlerDifferential (α ≫ regularListQuotientMap s)))
  (bQ' : Module.Basis (Fin d)
    (regularListQuotientRing (A := CommRingCat.of (Localization.Away r))
      (regularListPrincipalList s r))
    (CommRingCat.KaehlerDifferential ((α ≫
      (CommRingCat.ofHom (algebraMap A (Localization.Away r)) :
        A ⟶ CommRingCat.of (Localization.Away r))) ≫
      regularListQuotientMap (A := CommRingCat.of (Localization.Away r))
        (regularListPrincipalList s r))))
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (J : InjectiveResolution L) (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  (E : L ≅ moduleExteriorPower (Spec A)
    (relativeDifferentialSheaf (Spec.map α)) (s.length + d))
  [HasExt.{w} (ModuleCat.{u} A)] [HasExt.{z} (ModuleCat.{u} (Localization.Away r))]

local notation "S" => CommRingCat.of (Localization.Away r)
local notation "t" => regularListPrincipalList s r
local notation "φ" => (CommRingCat.ofHom (algebraMap A (Localization.Away r)) : A ⟶ S)
local notation "ψ" => regularListPrincipalLiteralQuotientMap s r
local notation "h" => regularListPrincipalLiteralQuotientMap_square s r

/-- The same original principal homology arrow intertwines the original canonical model maps.
All original class, determinant, normal-frame and coefficient equations are discharged. -/
theorem regularListCanonicalModelTopHomologyIso_principal :
    CanonicalRegularListModelOpenSquare (A' := S) α s t hs ht φ ψ h hA hB hA' hB'
      bA bA' bQ bQ' (List.length_map (as := s) (algebraMap A (Localization.Away r))) J e E
      (regularListPrincipalLiteralSheafHomologyMap s r J (s.length : ℤ)) := by
  let : Module.Flat A (Localization.Away r) :=
    IsLocalization.flat (Localization.Away r) (Submonoid.powers r)
  refine regularListCanonicalModelTopHomologyIso_open_of_modelTopClass
    (A' := S) α s t hs ht φ ψ h hA hB hA' hB' bA bA' bQ bQ'
    (List.length_map (as := s) (algebraMap A (Localization.Away r))) J e E ?_
    (regularListPrincipalLiteralSheafHomologyMap s r J (s.length : ℤ)) ?_
  · intro i
    simp only [regularListPrincipalList, List.get_eq_getElem, List.getElem_map, Fin.val_cast]
    rfl
  · have hClass := regularListPrincipalLiteralSheafHomologyMap_modelTopClass s r J hs e ⊤
    dsimp only at hClass
    simpa only [regularListOpenCoefficientFrame_principal] using hClass

end Principal
end AlgebraicGeometry.Scheme.Modules
