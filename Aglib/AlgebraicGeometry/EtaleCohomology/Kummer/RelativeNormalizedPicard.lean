/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.UnitsQuotient
public import Aglib.AlgebraicGeometry.Picard.Normalized

/-!
# The original Kummer map to normalized relative Picard torsion

For a family with a section, normalize the original Kummer Picard image by subtracting
its restriction to that section. This gives a surjection onto the actual torsion subgroup
of the normalized Picard group on every test scheme. The map commutes with the original
fibre-product transition maps. Its kernel is characterized by the image of base Picard
pullback, not declared zero. No representability, properness or local vanishing assertion
is hidden in this pointwise construction; passing to the small étale sheaf is separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open RelativePicard

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- The original split normalization on the family Picard group. -/
abbrev normalization (T : Over S) :
    PicardGroup (pullback p T.hom) →+ normalizedSubgroup p o ho (op T) :=
  Split.normalize ((basePullback p).app (op T)).hom
    ((originRestriction p o ho).app (op T)).hom
    (originRestriction_comp_basePullback p o ho (op T))

private theorem normalization_naturality {T T' : Over S} (f : T' ⟶ T)
    (a : PicardGroup (pullback p T.hom)) :
    ((normalizedPicardFunctor p o ho).map f.op).hom (normalization p o ho T a) =
      normalization p o ho T' (((familyPicardFunctor p).map f.op).hom a) := by
  have h := congrArg (fun φ => φ.hom (QuotientAddGroup.mk a))
    ((quotientNormalizedIso p o ho).hom.naturality f.op)
  exact h.symm

/-- The actual `n`-torsion subgroup of the normalized Picard group. -/
abbrev normalizedPicardTorsion (T : Over S) (n : ℕ) :
    AddSubgroup (normalizedSubgroup p o ho (op T)) :=
  (nsmulAddMonoidHom (α := normalizedSubgroup p o ho (op T)) n).ker

variable (T : Over S) [HasExt.{w} (AbelianSheaf.{u, u + 1} (pullback p T.hom))]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(pullback p T.hom, ⊤)))

/-- Normalize the original roots-to-Picard map, retaining its genuine torsion codomain. -/
def rootsNormalizedPicardMap (hn : 0 < n)
    (hinv : IsUnit (n : Γ(pullback p T.hom, ⊤))) : Sheaf.H.{w} (mu (pullback p T.hom) n) 1 →+
    normalizedPicardTorsion p o ho T n :=
  ((normalization p o ho T).comp (rootsPicardMap (pullback p T.hom) n)).codRestrict _
    (fun a => by
      change n • normalization p o ho T (rootsPicardMap (pullback p T.hom) n a) = 0
      rw [← map_nsmul]
      have ht := (rootsPicardTorsionMap (pullback p T.hom) n hn hinv a).property
      change n • rootsPicardMap (pullback p T.hom) n a = 0 at ht
      rw [ht, map_zero])

/-- The underlying line-bundle class is the original Picard image minus its base part. -/
theorem rootsNormalizedPicardMap_val
    (a : Sheaf.H.{w} (mu (pullback p T.hom) n) 1) :
    (rootsNormalizedPicardMap p o ho T n hn hinv a).val.val =
      rootsPicardMap (pullback p T.hom) n a -
        (show PicardGroup (pullback p T.hom) from
          ((basePullback p).app (op T)).hom
            (((originRestriction p o ho).app (op T)).hom
              (rootsPicardMap (pullback p T.hom) n a))) := rfl

/-- Every normalized torsion class has an original Kummer preimage. -/
theorem rootsNormalizedPicardMap_surjective :
    Function.Surjective (rootsNormalizedPicardMap p o ho T n hn hinv) := by
  intro a
  have ha : n • (a.val.val : PicardGroup (pullback p T.hom)) = 0 :=
    congrArg Subtype.val a.property
  obtain ⟨c, hc⟩ := rootsPicardTorsionMap_surjective (pullback p T.hom) n hn hinv
    ⟨a.val.val, ha⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change normalization p o ho T (rootsPicardMap (pullback p T.hom) n c) = a.val
  have hc' := congrArg Subtype.val hc
  change rootsPicardMap (pullback p T.hom) n c = a.val.val at hc'
  rw [hc']
  exact Split.normalize_on_ker _ _ _ a.val

/-- The normalized map vanishes exactly when the original Picard image comes from the base.
This is not a global injectivity assertion: the base class and unit obstruction still have
to be killed locally before sheafification. -/
theorem rootsNormalizedPicardMap_eq_zero_iff
    (a : Sheaf.H.{w} (mu (pullback p T.hom) n) 1) :
    rootsNormalizedPicardMap p o ho T n hn hinv a = 0 ↔
      rootsPicardMap (pullback p T.hom) n a ∈
        (((basePullback p).app (op T)).hom).range := by
  constructor
  · intro h
    have hz := congrArg Subtype.val h
    change normalization p o ho T (rootsPicardMap (pullback p T.hom) n a) = 0 at hz
    exact (SetLike.ext_iff.mp (Split.normalize_ker _ _
      (originRestriction_comp_basePullback p o ho (op T))) _).mp hz
  · intro h
    apply Subtype.ext
    exact (SetLike.ext_iff.mp (Split.normalize_ker _ _
      (originRestriction_comp_basePullback p o ho (op T))) _).mpr h

variable {T}

/-- Naturality of normalized torsion on actual test-scheme maps. The target torsion subgroup
is compared through its original normalized Picard inclusion; no new transition model is used. -/
theorem rootsNormalizedPicardMap_naturality {T' : Over S}
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p T'.hom))] (f : T' ⟶ T)
    (a : Sheaf.H.{w} (mu (pullback p T.hom) n) 1) :
    (rootsNormalizedPicardMap p o ho T' n hn
      (levelInvertible
        (show pullback p T'.hom ⟶ pullback p T.hom from (familyScheme p).map f) n hinv)
      (rootsCohomologyPullback
        (show pullback p T'.hom ⟶ pullback p T.hom from (familyScheme p).map f)
        n hn hinv 1 a)).val =
      ((normalizedPicardFunctor p o ho).map f.op).hom
        (rootsNormalizedPicardMap p o ho T n hn hinv a).val := by
  change normalization p o ho T'
    (rootsPicardMap (pullback p T'.hom) n
      (rootsCohomologyPullback
        (show pullback p T'.hom ⟶ pullback p T.hom from (familyScheme p).map f)
        n hn hinv 1 a)) =
    ((normalizedPicardFunctor p o ho).map f.op).hom
      (normalization p o ho T (rootsPicardMap (pullback p T.hom) n a))
  have h := DFunLike.congr_fun (rootsPicardMap_pullback
    (show pullback p T'.hom ⟶ pullback p T.hom from (familyScheme p).map f) n hn hinv) a
  change rootsPicardMap (pullback p T'.hom) n
      (rootsCohomologyPullback
        (show pullback p T'.hom ⟶ pullback p T.hom from (familyScheme p).map f)
        n hn hinv 1 a) =
    ((familyPicardFunctor p).map f.op).hom (rootsPicardMap (pullback p T.hom) n a) at h
  exact (congrArg (normalization p o ho T') h).trans
    (normalization_naturality p o ho f _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
