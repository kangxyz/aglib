/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRingMaps
public import Aglib.AlgebraicGeometry.Picard.KummerH1
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.LocalKummer` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`af81d433586deb774972e92e231cb52c6c88f2b6007370556b03a60d419a9090`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (LineBundle)

/-!
# Positive unit-root classes over a local ring

Private investigation for `K2-018#prop:k2018-arithmetic-characters`,
mathematical source revision `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering basis: `7dcde130d429905e2624079dd7a0d18e3ebc94e2`.
The encoded subset is surjectivity of the actual positive rootClass for every
local ring and every positive invertible level. Only the independent actual
rank-one etale-descent and canonical torsor/Ext classification premises remain.
The proof recovers an actual power pair, trivializes its actual line bundle,
and identifies it with the actual positive root torsor of its scalar unit.
-/

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.EtaleCohomology

open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.LocalKummer
open EtaleDescent TrivializedPower UnitPower TrivializedPowerTorsor
open _root_.GroupCohomology.Kummer.Coefficients
universe u w

/-- Trivializing the actual line bundle turns a specified power pair into an
actual unit pair, preserving its specified nth-power trivialization.
Source subset: `K2-018#prop:k2018-arithmetic-characters`, mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; local Kummer prerequisite. -/
theorem pair_isomorphic_unitPair_of_trivial (X : Scheme.{u}) (n : ℕ)
    (P : Pair X n) (e : P.lineBundle.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    ∃ a : Γ(X, ⊤)ˣ,
      (powerIso X (M := unitLineBundle X) e n).hom ≫
        (AlgebraicGeometry.Scheme.Modules.Invertible.PowerRoot.unitPair X n
            a).trivialization.hom = P.trivialization.hom := by
  let d : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
    (unitPowerIso X n).symm ≪≫
      (powerIso X (M := unitLineBundle X) e n).symm ≪≫ P.trivialization
  let a := unitOfIso X d
  refine ⟨a, ?_⟩
  have ha : AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _ a = d :=
    (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.unitAutoEquiv X).left_inv d
  change (powerIso X (M := unitLineBundle X) e n).hom ≫
    ((unitPowerIso X n).hom ≫
        (AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms.scalarIso X _ a).hom) = _
  rw [ha]
  dsimp only [d, Iso.trans_hom, Iso.symm_hom]
  simp only [Iso.hom_inv_id_assoc]

/-- If every actual line bundle is trivial, each actual mu_n H1 class is the
class of the existing positive root torsor of an actual global unit.
Source subset: `K2-018#prop:k2018-arithmetic-characters`, mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. EtaleLineBundleDescent and
Stacks03AJ remain explicit independent arguments in this API; the native
rank-one stack theorem can supply EtaleLineBundleDescent. -/
theorem rootClass_surjective_of_lineBundle_trivial (X : Scheme.{u})
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (hdes : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} X)
    (htriv : ∀ L : LineBundle X, Nonempty (L.val ≅ SheafOfModules.unit X.ringCatSheaf))
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    Function.Surjective
      (GroupCohomology.Kummer.Torsor.rootClass
          GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn hinv)
          := by
  intro c
  obtain ⟨d, hd⟩ := (h03AJ.bijective (mu X n)).surjective c
  obtain ⟨P, rfl⟩ := Quotient.exists_rep d
  let Q := AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.pair P hdes
  obtain ⟨e⟩ := htriv Q.lineBundle
  obtain ⟨a, ha⟩ := pair_isomorphic_unitPair_of_trivial X n Q e
  refine ⟨a, ?_⟩
  have hrec := torsorExtClass_iso
      (AlgebraicGeometry.Scheme.Modules.Invertible.PowerDescent.torsorRecovery P hdes hn hinv)
  have hpair := torsorExtClass_iso
      (AlgebraicGeometry.Scheme.Modules.Invertible.KummerH1.pairTorsorIso hdes X n hn hinv
    (P := Q) (Q := AlgebraicGeometry.Scheme.Modules.Invertible.PowerRoot.unitPair X n a) e ha)
  have hroot := AlgebraicGeometry.Scheme.Modules.Invertible.PowerRoot.torsorExtClass_unitPair
      hdes X n hn hinv a
  exact (hrec.trans (hpair.trans hroot)).symm.trans hd

/-- Actual global-unit positive root classes surject on any local spectrum.
Source subset: `K2-018#prop:k2018-arithmetic-characters`, mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. Only actual local-ring, Ext-size,
positive/invertible-level, etale-descent, and canonical Stacks03AJ conditions. -/
theorem localRootClass_surjective (R : CommRingCat.{u}) [IsLocalRing R]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec R))]
    (hdes : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} (Spec R))
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec R, ⊤))) :
    Function.Surjective (GroupCohomology.Kummer.Torsor.rootClass
        GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
      (Spec R) n hn hinv) :=
  rootClass_surjective_of_lineBundle_trivial (Spec R) hdes h03AJ
    (localLineBundle_trivial R) n hn hinv

/-- The same surjectivity in the literal ring-unit coordinates supplied by
the inverse actual Gamma-Spec isomorphism.
Source subset: `K2-018#prop:k2018-arithmetic-characters`, mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; exact local-origin consumer input. -/
theorem localRingRootClass_surjective (R : CommRingCat.{u}) [IsLocalRing R]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec R))]
    (hdes : EtaleLineBundleDescent.{u}) (h03AJ : Stacks03AJ.{u, w} (Spec R))
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec R, ⊤))) :
    Function.Surjective (fun a : Rˣ =>
      GroupCohomology.Kummer.Torsor.rootClass
          GroupCohomology.Kummer.RootCover.etalePowerSurjectivity (Spec R) n
          hn hinv
        (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom a)) := by
  intro c
  obtain ⟨a, ha⟩ := localRootClass_surjective R hdes h03AJ n hn hinv c
  refine ⟨Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom a, ?_⟩
  have hunit : Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom a) = a := by
    apply Units.ext
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).hom_inv_id (a : Γ(Spec R, ⊤))
  exact (congrArg
    (GroupCohomology.Kummer.Torsor.rootClass
        GroupCohomology.Kummer.RootCover.etalePowerSurjectivity (Spec R) n hn hinv)
    hunit).trans ha

/-- The exact universal local-ring family needed by the local-origin consumer,
derived from independent universal rank-one descent and canonical torsor/Ext
classification on the actual local spectra.
Source subset: `K2-018#prop:k2018-arithmetic-characters`, mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; no specialization premise is used. -/
theorem localRingRootClass_surjective_family (hdes : EtaleLineBundleDescent.{u})
    (h03AJ : ∀ (R : CommRingCat.{u}) [IsLocalRing R]
      [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec R))], Stacks03AJ.{u, w} (Spec R)) :
    ∀ (R : CommRingCat.{u}) [IsLocalRing R]
      [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec R))],
      ∀ (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec R, ⊤))),
        Function.Surjective (fun a : Rˣ =>
          GroupCohomology.Kummer.Torsor.rootClass
              GroupCohomology.Kummer.RootCover.etalePowerSurjectivity (Spec R)
              n hn hinv
            (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom a)) := by
  intro R _ _ n hn hinv
  exact localRingRootClass_surjective R hdes (h03AJ R) n hn hinv

end AlgebraicGeometry.Scheme.Modules.Invertible.LocalKummer
