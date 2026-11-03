/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.LocalImage
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.IsIso
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.BaseChange
public import Aglib.AlgebraicGeometry.Descent.LocalModification
public import Aglib.AlgebraicGeometry.Modules.Pullback.Triangle
public import Aglib.AlgebraicGeometry.Modules.Invertible.Stalk
public import Aglib.LinearAlgebra.FreeModule.TorsionQuotient

/-!
# The original local image and the own canonical stalk

The literal canonical pullback stalk map, when genuinely surjective,
factors through the SAME torsion-kernel image quotient. The own terminal
canonical stalk supplies torsion-freeness and nontriviality through the
actual localization projection. The exact factor equation gives its frame.
The original structure-unit and stalk surjectivity remain explicit inputs;
neither is inferred from principalization. Only points over the original
point are addressed, not untouched singularities elsewhere.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Modules.standardHasDerivedCategory
/-- The standard derived-category instance for modules over the original coefficient ring. -/
local instance localImageFrameModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- CONDITIONAL original-map comparison. The genuine inverse-trace pullback
surjection at the actual point factors through the SAME locally rank-one
image, with its exact factor equation and an OWN global canonical stalk frame.
No canonical frame, target rank, target torsion-freeness or target nontriviality
is assumed. The genuine structure-unit and stalk-surjectivity inputs remain
separate producer obligations. -/
theorem normalSurfaceCanonicalLocalImage_stalkFrame_of_pullback_surjective
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (ιX ιZ : Type u) {X Z T : Scheme.{u}}
    [IsIntegral X] [IsIntegral Z] [IsIntegral T]
    (iX : X ⟶ ProjectiveSpace R ιX) [IsClosedImmersion iX]
    [IsDominant (iX ≫ toSpec R ιX)]
    (iZ : Z ⟶ ProjectiveSpace R ιZ) [IsClosedImmersion iZ]
    [IsDominant (iZ ≫ toSpec R ιZ)]
    (hX : NormalStalks X) (hdX : topologicalKrullDim X ≤ 2)
    (hZ : NormalStalks Z) (hdZ : topologicalKrullDim Z ≤ 2)
    (nX nZ : ℕ) (eX : ιX ≃ Fin (nX + 1)) (eZ : ιZ ≃ Fin (nZ + 1))
    (hfinX : (genericImageBaseMap R ιX iX).Finite)
    (hfinZ : (genericImageBaseMap R ιZ iZ).Finite)
    (f : Z ⟶ X) [IsProper f]
    (hb : iZ ≫ toSpec R ιZ = f ≫ (iX ≫ toSpec R ιX))
    [IsIso (moduleDerivedPushforwardUnit X f)]
    (x : X) (p : T ⟶ Spec (X.presheaf.stalk x)) [IsDominant p]
    (a : T ⟶ Z) (H : IsPullback a p f (X.fromSpecStalk x))
    (hline : Invertible.IsLocallyRankOne T
      (Hom.idealModule ((affineCenter (X.presheaf.stalk x)
        (normalSurfaceCanonicalStalkFractionalImage
          R ιX iX hX hdX nX eX hfinX x).num).comap p).subschemeι))
    (t : T) (ht : p t = IsLocalRing.closedPoint (X.presheaf.stalk x)) :
    let WX := normalSurfaceCanonicalModule R ιX iX nX
    let WZ := normalSurfaceCanonicalModule R ιZ iZ nZ
    let L := Hom.idealModule ((affineCenter (X.presheaf.stalk x)
      (normalSurfaceCanonicalStalkFractionalImage
        R ιX iX hX hdX nX eX hfinX x).num).comap p).subschemeι
    let q := normalSurfaceCanonicalLocalImageQuotient R ιX iX hX hdX nX eX hfinX x p
    let τ := normalSurfaceProperCanonicalTrace R ιX ιZ f iX iZ hb
      hX hdX hZ hdZ nX nZ eX eZ hfinX hfinZ
    letI : IsIso τ := normalSurfaceProperCanonicalTrace_isIso_of_structureUnit
      R ιX ιZ f iX iZ hb hX hdX hZ hdZ nX nZ eX eZ hfinX hfinZ
    let v := (pullbackTriangleIso a f (p ≫ X.fromSpecStalk x) H.w).inv.app WX ≫
      (Modules.pullback a).map (ordinaryTracePullback f τ)
    Function.Surjective (((moduleStalk T t).map v).hom) →
      f (a t) = x ∧
        ∃ E : ((moduleStalk T t).obj L) ≃ₗ[T.presheaf.stalk t]
            ((moduleStalk T t).obj ((Modules.pullback a).obj WZ)),
          E.toLinearMap.comp (((moduleStalk T t).map q).hom) =
              ((moduleStalk T t).map v).hom ∧
            Nonempty (((moduleStalk Z (a t)).obj WZ) ≃ₗ[Z.presheaf.stalk (a t)]
              Z.presheaf.stalk (a t)) := by
  let WX := normalSurfaceCanonicalModule R ιX iX nX
  let WZ := normalSurfaceCanonicalModule R ιZ iZ nZ
  let L := Hom.idealModule ((affineCenter (X.presheaf.stalk x)
    (normalSurfaceCanonicalStalkFractionalImage
      R ιX iX hX hdX nX eX hfinX x).num).comap p).subschemeι
  let q := normalSurfaceCanonicalLocalImageQuotient R ιX iX hX hdX nX eX hfinX x p
  let τ := normalSurfaceProperCanonicalTrace R ιX ιZ f iX iZ hb
    hX hdX hZ hdZ nX nZ eX eZ hfinX hfinZ
  let : IsIso τ := normalSurfaceProperCanonicalTrace_isIso_of_structureUnit
    R ιX ιZ f iX iZ hb hX hdX hZ hdZ nX nZ eX eZ hfinX hfinZ
  let v := (pullbackTriangleIso a f (p ≫ X.fromSpecStalk x) H.w).inv.app WX ≫
    (Modules.pullback a).map (ordinaryTracePullback f τ)
  change Function.Surjective (((moduleStalk T t).map v).hom) → _
  intro hsurj
  let B := T.presheaf.stalk t
  let C := Z.presheaf.stalk (a t)
  let Q := (moduleStalk Z (a t)).obj WZ
  let N := (moduleStalk T t).obj ((Modules.pullback a).obj WZ)
  let : IsIso (a.stalkMap t) :=
    LocalModification.isIso_stalkMap_localization_projection x a p f H t
  let φ := (a.stalkMap t).hom
  let eR := (asIso (a.stalkMap t)).commRingCatIsoToRingEquiv
  let : (ModuleCat.restrictScalars φ).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eR
  let E0 : Q ≅ (ModuleCat.restrictScalars φ).obj N :=
    asIso ((ModuleCat.extendRestrictScalarsAdj φ).unit.app Q) ≪≫
      (ModuleCat.restrictScalars φ).mapIso ((pullbackModuleStalkIso a t).app WZ).symm
  let : Module.IsTorsionFree C Q :=
    normalSurfaceCanonicalStalk_isTorsionFree R ιZ iZ hZ hdZ nZ eZ hfinZ (a t)
  let : Nontrivial Q := normalSurfaceCanonicalStalk_nontrivial R ιZ iZ nZ eZ hfinZ (a t)
  let : Module.IsTorsionFree C ((ModuleCat.restrictScalars φ).obj N) :=
    Function.Injective.moduleIsTorsionFree E0.inv E0.toLinearEquiv.symm.injective
      E0.inv.hom.map_smul
  let : Module.IsTorsionFree B N := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro b n hbn
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · right
      have hr : eR.symm b ≠ 0 := by
        intro hr
        apply hb0
        exact (eR.apply_symm_apply b).symm.trans ((congrArg eR hr).trans eR.map_zero)
      have hz : eR.symm b • (show (ModuleCat.restrictScalars φ).obj N from n) = 0 := by
        change eR (eR.symm b) • n = 0
        rw [eR.apply_symm_apply]
        exact hbn
      exact (smul_eq_zero.mp hz).resolve_left hr
  let : Nontrivial N := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hN
    let : Subsingleton N := hN
    let : Subsingleton ((ModuleCat.restrictScalars φ).obj N) :=
      inferInstanceAs (Subsingleton N)
    have hQ : Subsingleton Q := E0.toLinearEquiv.injective.subsingleton
    exact not_subsingleton Q hQ
  let : Epi q :=
    normalSurfaceCanonicalLocalImageQuotient_epi R ιX iX hX hdX nX eX hfinX x p
  have hq : Function.Surjective (((moduleStalk T t).map q).hom) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨eL⟩ := Invertible.nonempty_stalkLinearEquiv_of_isLocallyRankOne L hline t
  have hk := normalSurfaceCanonicalLocalImageQuotient_stalk_ker_eq_torsion
    R ιX iX hX hdX nX eX hfinX x p t
  obtain ⟨E, hE⟩ := LinearMap.exists_linearEquiv_of_surjective_of_ker_le_torsion
    (((moduleStalk T t).map q).hom) hq hk.le eL
    (((moduleStalk T t).map v).hom) hsurj
  let F : Q ≅ ModuleCat.of C C := E0 ≪≫
    (ModuleCat.restrictScalars φ).mapIso (E.symm.trans eL).toModuleIso ≪≫
      ModuleCat.restrictScalarsIsoOfEquiv eR
  refine ⟨?_, E, hE, ⟨F.toLinearEquiv⟩⟩
  have hpoint : f (a t) = X.fromSpecStalk x (p t) :=
    congrArg (fun k : T ⟶ X => k t) H.w
  exact hpoint.trans ((congrArg (X.fromSpecStalk x) ht).trans
    (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)))

end AlgebraicGeometry.Scheme.Cohomology
