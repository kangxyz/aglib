/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.LocalIdeal
public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.StalkKernel

/-!
# The original canonical coefficient onto its actual local image ideal

The native pullback-composition iso and SAME local numerator comparison
are followed by the existing ideal-image epi. The source is the literal
pullback of the original global coefficient. Its inclusion law and exact
stalk torsion kernel retain all original maps. No canonical target on the
new model, image invertibility or Gorensteinness is assumed or constructed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
  (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
  [IsDominant (i ≫ toSpec R ι)]
  (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι i).Finite)

variable (x : X) {T : Scheme.{u}} (beta : T ⟶ Spec (X.presheaf.stalk x))

/-- The literal pullback of the SAME global coefficient maps onto the actual
image of its SAME original numerator. No second image factorization is chosen. -/
def normalSurfaceCanonicalLocalImageQuotient :
    (pullback (beta ≫ X.fromSpecStalk x)).obj (normalSurfaceCanonicalModule R ι i n) ⟶
      Scheme.Hom.idealModule
        ((affineCenter (X.presheaf.stalk x)
          (normalSurfaceCanonicalStalkFractionalImage
            R ι i hX hXdim n e hfin x).num).comap beta).subschemeι :=
  ((pullbackComp beta (X.fromSpecStalk x)).inv.app
      (normalSurfaceCanonicalModule R ι i n) ≫
    (pullback beta).map (normalSurfaceCanonicalLocalIdealIso
      R ι i hX hXdim n e hfin x).hom) ≫
    ((affineCenter (X.presheaf.stalk x)
      (normalSurfaceCanonicalStalkFractionalImage
        R ι i hX hXdim n e hfin x).num).pullbackIdealMonoFactorisation beta).e

/-- The source comparison is an iso and the original image-factorization map
is epi; no flatness, dominance or source integrality is needed for this fact. -/
theorem normalSurfaceCanonicalLocalImageQuotient_epi :
    Epi (normalSurfaceCanonicalLocalImageQuotient R ι i hX hXdim n e hfin x beta) := by
  let I := affineCenter (X.presheaf.stalk x)
    (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).num
  let : Epi (I.pullbackIdealMonoFactorisation beta).e :=
    I.epi_idealPullbackMap beta _ _
  let P : (pullback (beta ≫ X.fromSpecStalk x)).obj
      (normalSurfaceCanonicalModule R ι i n) ≅
        (pullback beta).obj (Scheme.Hom.idealModule I.subschemeι) :=
    ((pullbackComp beta (X.fromSpecStalk x)).app
      (normalSurfaceCanonicalModule R ι i n)).symm ≪≫
      (pullback beta).mapIso
        (normalSurfaceCanonicalLocalIdealIso R ι i hX hXdim n e hfin x)
  change Epi (P.hom ≫ (I.pullbackIdealMonoFactorisation beta).e)
  infer_instance

/-- The quotient's actual inclusion is the pullback of the SAME original
scaled canonical inclusion, through the native composition and unit maps. -/
theorem normalSurfaceCanonicalLocalImageQuotient_inclusion :
    normalSurfaceCanonicalLocalImageQuotient R ι i hX hXdim n e hfin x beta ≫
      Scheme.Hom.idealInclusion
        ((affineCenter (X.presheaf.stalk x)
          (normalSurfaceCanonicalStalkFractionalImage
            R ι i hX hXdim n e hfin x).num).comap beta).subschemeι =
      (pullbackComp beta (X.fromSpecStalk x)).inv.app
          (normalSurfaceCanonicalModule R ι i n) ≫
        (pullback beta).map
          ((normalSurfaceCanonicalLocalIdealIso R ι i hX hXdim n e hfin x).hom ≫
            Scheme.Hom.idealInclusion
              (affineCenter (X.presheaf.stalk x)
                (normalSurfaceCanonicalStalkFractionalImage
                  R ι i hX hXdim n e hfin x).num).subschemeι) ≫
          (pullbackUnitIso beta).hom := by
  let W := normalSurfaceCanonicalModule R ι i n
  let I := affineCenter (X.presheaf.stalk x)
    (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).num
  let E := normalSurfaceCanonicalLocalIdealIso R ι i hX hXdim n e hfin x
  let F := pullback beta
  let a := (pullbackComp beta (X.fromSpecStalk x)).inv.app W
  let b := F.map E.hom
  let q := (I.pullbackIdealMonoFactorisation beta).e
  let j := Scheme.Hom.idealInclusion (I.comap beta).subschemeι
  let u := (pullbackUnitIso beta).hom
  have hfac : q ≫ j = F.map (Scheme.Hom.idealInclusion I.subschemeι) ≫ u :=
    (I.pullbackIdealMonoFactorisation beta).fac
  have hmap := F.map_comp E.hom (Scheme.Hom.idealInclusion I.subschemeι)
  change ((a ≫ b) ≫ q) ≫ j =
    a ≫ F.map (E.hom ≫ Scheme.Hom.idealInclusion I.subschemeι) ≫ u
  calc
    ((a ≫ b) ≫ q) ≫ j = a ≫ b ≫ q ≫ j :=
      (Category.assoc (a ≫ b) q j).trans (Category.assoc a b (q ≫ j))
    _ = a ≫ b ≫ F.map (Scheme.Hom.idealInclusion I.subschemeι) ≫ u :=
      congrArg (fun k => a ≫ b ≫ k) hfac
    _ = a ≫ (b ≫ F.map (Scheme.Hom.idealInclusion I.subschemeι)) ≫ u :=
      congrArg (fun k => a ≫ k)
        (Category.assoc b (F.map (Scheme.Hom.idealInclusion I.subschemeι)) u).symm
    _ = a ≫ F.map (E.hom ≫ Scheme.Hom.idealInclusion I.subschemeι) ≫ u :=
      congrArg (fun k => a ≫ k ≫ u) hmap.symm

/-- On an actual dominant integral model, the SAME quotient has precisely
the torsion kernel of the literal global-coefficient pullback stalk. -/
theorem normalSurfaceCanonicalLocalImageQuotient_stalk_ker_eq_torsion
    [IsIntegral T] [IsDominant beta] (y : T) :
    LinearMap.ker
        ((moduleStalk T y).map
          (normalSurfaceCanonicalLocalImageQuotient R ι i hX hXdim n e hfin x beta)).hom =
      Submodule.torsion (T.presheaf.stalk y)
        ((moduleStalk T y).obj
          ((pullback (beta ≫ X.fromSpecStalk x)).obj
            (normalSurfaceCanonicalModule R ι i n))) := by
  let W := normalSurfaceCanonicalModule R ι i n
  let J := (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).num
  let I := affineCenter (X.presheaf.stalk x) J
  let E := normalSurfaceCanonicalLocalIdealIso R ι i hX hXdim n e hfin x
  let P : (pullback (beta ≫ X.fromSpecStalk x)).obj W ≅
      (pullback beta).obj (Scheme.Hom.idealModule I.subschemeι) :=
    ((pullbackComp beta (X.fromSpecStalk x)).app W).symm ≪≫ (pullback beta).mapIso E
  let F := ((moduleStalk T y).mapIso P).toLinearEquiv
  have hJ : J ≠ ⊥ :=
    normalSurfaceCanonicalStalkFractionalImage_num_ne_bot R ι i hX hXdim n e hfin x
  have hk := affineCenter_pullbackImage_stalk_ker_eq_torsion J hJ beta y
  ext z
  change ((moduleStalk T y).map
    (normalSurfaceCanonicalLocalImageQuotient R ι i hX hXdim n e hfin x beta)) z = 0 ↔ _
  have hv := ConcreteCategory.congr_hom
    ((moduleStalk T y).map_comp P.hom (I.pullbackIdealMonoFactorisation beta).e) z
  change ((moduleStalk T y).map
      (normalSurfaceCanonicalLocalImageQuotient R ι i hX hXdim n e hfin x beta)) z =
    ((moduleStalk T y).map (I.pullbackIdealMonoFactorisation beta).e) (F z) at hv
  have hz : ((moduleStalk T y).map (I.pullbackIdealMonoFactorisation beta).e) (F z) = 0 ↔
      F z ∈ Submodule.torsion (T.presheaf.stalk y)
        ((moduleStalk T y).obj ((pullback beta).obj (Scheme.Hom.idealModule I.subschemeι))) :=
    Iff.of_eq (congrArg (fun K => F z ∈ K) hk)
  have ht : F z ∈ Submodule.torsion (T.presheaf.stalk y)
        ((moduleStalk T y).obj ((pullback beta).obj (Scheme.Hom.idealModule I.subschemeι))) ↔
      z ∈ Submodule.torsion (T.presheaf.stalk y)
        ((moduleStalk T y).obj ((pullback (beta ≫ X.fromSpecStalk x)).obj W)) := by
    constructor
    · intro hz
      obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff (F z)).mp hz
      refine (Submodule.mem_torsion_iff z).mpr ⟨r, ?_⟩
      apply F.injective
      exact (F.map_smul (r : T.presheaf.stalk y) z).trans (hr.trans F.map_zero.symm)
    · intro hz
      obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff z).mp hz
      refine (Submodule.mem_torsion_iff (F z)).mpr ⟨r, ?_⟩
      exact (F.map_smul (r : T.presheaf.stalk y) z).symm.trans
        ((congrArg F hr).trans F.map_zero)
  exact (Iff.of_eq (congrArg (fun v => v = 0) hv)).trans (hz.trans ht)

end AlgebraicGeometry.Scheme.Cohomology
