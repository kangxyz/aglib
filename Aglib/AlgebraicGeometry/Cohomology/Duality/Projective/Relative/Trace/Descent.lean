/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Sections
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.QuasiCoherent

/-!
# Affine descent of cohomologically normalized trace arrows

The entire ordinary trace square is proved before choosing a projective
model or a coefficient functor. The only trace inputs are their original
affine section formulas and the original open cohomology equation. The
coefficient map remains the supplied native restriction adjunct.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

private theorem moduleFunctor_triple_apply
    {B : Type u} [CommRing B] {D : Type*} [Category* D]
    (F : D ⥤ ModuleCat.{u} B) {K L M N : D}
    (r : K ⟶ L) (s : L ⟶ M) (t : M ⟶ N) (x : F.obj K) :
    ModuleCat.Hom.hom (F.map (r ≫ s ≫ t)) x = F.map t (F.map s (F.map r x)) := by
  rw [F.map_comp, F.map_comp]
  rfl

section
variable {R A : Type u} [CommRing R] [CommRing A]
  {X W : Scheme.{u}} (i : W ⟶ X) (q : W ⟶ Spec (.of A)) (p : X ⟶ Spec (.of R))
  (σ : R →+* A) [QuasiCompact p] [QuasiSeparated p]
  [QuasiCompact q] [QuasiSeparated q]
  [IsOpenImmersion i] [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
  (H : IsPullback i q p (Spec.map (CommRingCat.ofHom σ)))

/-- Original section normalizations and the original cohomological open
trace imply the full native sheaf trace square. No particular coefficient
functor or projective model occurs in the proof. -/
theorem affineTraceRestriction_of_sections
    (M : X.Modules) [M.IsQuasicoherent] (M' : W.Modules) [M'.IsQuasicoherent]
    (N : (Spec (.of R)).Modules) (n : ℕ)
    (C : (Modules.restrictFunctor i).obj M ⟶ M')
    (β : M ⟶ (Scheme.Modules.pushforward i).obj M')
    (hβ : β = (restrictAdjunction i).homEquiv M M' C)
    (tR : ((Scheme.Modules.pushforward p).rightDerived n).obj M ⟶ N)
    (tA : ((Scheme.Modules.pushforward q).rightDerived n).obj M' ⟶
      (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)
    (τR : Sheaf.H.{u + 1} (moduleAddSheaf X M) n → moduleSpecΓFunctor.obj N)
    (τA : Sheaf.H.{u + 1} (moduleAddSheaf W M') n →
      moduleSpecΓFunctor.obj
        ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N))
    (htR : ∀ x,
      moduleSpecΓFunctor.map tR x =
        τR (moduleHigherDirectImageAffineSectionsLinearEquiv p M (injectiveResolution M) n x))
    (htA : ∀ y,
      moduleSpecΓFunctor.map tA y =
        τA (moduleHigherDirectImageAffineSectionsLinearEquiv q M' (injectiveResolution M') n y))
    (hopen : ∀ c,
      τA (moduleCohomologyMapAlong i β n c) =
        affineUnitSections (Spec.map (CommRingCat.ofHom σ)) N (τR c)) :
    (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p
        (Spec.map (CommRingCat.ofHom σ)) H n).hom.app M ≫
      ((Scheme.Modules.pushforward q).rightDerived n).map C ≫ tA =
      (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).map tR := by
  let j := Spec.map (CommRingCat.ofHom σ)
  let L := ((Scheme.Modules.pushforward p).rightDerived n).obj M
  let r := (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p j H n).hom.app M
  let : L.IsQuasicoherent := moduleHigherDirectImage_isQuasicoherent p M n
  apply affineRestrictHom_ext j (M := L)
  intro x
  let u := affineUnitSections j L x
  let y := moduleSpecΓFunctor.map r u
  let c := moduleHigherDirectImageAffineSectionsLinearEquiv p M (injectiveResolution M) n x
  have hr := affineHigherOpenSections_unit i q p σ H M (injectiveResolution M)
    (injectiveResolution ((Modules.restrictFunctor i).obj M)) n x
  change moduleHigherDirectImageAffineSectionsLinearEquiv q
      ((Modules.restrictFunctor i).obj M) (injectiveResolution _) n y =
    moduleCohomologyMapAlong i ((restrictAdjunction i).unit.app M) n c at hr
  have hn := moduleHigherDirectImageAffineSectionsLinearEquiv_naturality q
    (injectiveResolution ((Modules.restrictFunctor i).obj M)) (injectiveResolution M')
    (v := C) n y
  have hco := moduleCohomologyMapAlong_homEquiv i M M' C n c
  have hb : moduleCohomologyMapAlong i β n c =
      Sheaf.H.map ((SheafOfModules.toSheaf W.ringCatSheaf).map C) n
        (moduleCohomologyMapAlong i ((restrictAdjunction i).unit.app M) n c) := by
    rw [hβ]
    exact hco
  calc
    _ = τA (moduleHigherDirectImageAffineSectionsLinearEquiv q M' (injectiveResolution M') n
        (moduleSpecΓFunctor.map (((Scheme.Modules.pushforward q).rightDerived n).map C) y)) := by
      exact (moduleFunctor_triple_apply moduleSpecΓFunctor r
        (((Scheme.Modules.pushforward q).rightDerived n).map C) tA u).trans
          (htA (moduleSpecΓFunctor.map (((Scheme.Modules.pushforward q).rightDerived n).map C) y))
    _ = τA (moduleCohomologyMapOfHom W
        (q.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) C n
        (moduleHigherDirectImageAffineSectionsLinearEquiv q
          ((Modules.restrictFunctor i).obj M) (injectiveResolution _) n y)) := congrArg τA hn
    _ = τA (Sheaf.H.map ((SheafOfModules.toSheaf W.ringCatSheaf).map C) n
        (moduleCohomologyMapAlong i ((restrictAdjunction i).unit.app M) n c)) := by
      have hm := moduleCohomologyMapOfHom_apply W
        (q.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) C n
        (moduleHigherDirectImageAffineSectionsLinearEquiv q
          ((Modules.restrictFunctor i).obj M) (injectiveResolution _) n y)
      exact congrArg τA (hm.trans
        (congrArg (Sheaf.H.map ((SheafOfModules.toSheaf W.ringCatSheaf).map C) n) hr))
    _ = τA (moduleCohomologyMapAlong i β n c) := congrArg τA hb.symm
    _ = affineUnitSections j N (τR c) := hopen c
    _ = affineUnitSections j N (moduleSpecΓFunctor.map tR x) :=
      congrArg (affineUnitSections j N) (htR x).symm
    _ = _ := affineUnitSections_naturality j tR x

end
end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
