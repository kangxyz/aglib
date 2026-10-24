/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Fibers.FieldPoint
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Point-fibre cohomology under base change of the family

Let `p : X ⟶ S` be a morphism, `s : T ⟶ S`, and `b : T' ⟶ T` a morphism over `S`
(`b ≫ s = s'`), with base-change map `familyBaseChange p s s' b hb : X ×_S T' ⟶ X ×_S T`. For
`t' ∈ T'` the fibre of `X ×_S T'` at `t'` is the base change of the fibre of `X ×_S T` at `b t'`
along the residue-field map `κ(b t') ⟶ κ(t')`:

* `fiberBaseChange p s s' b hb t' : X ×_S Spec κ(t') ⟶ X ×_S Spec κ(b t')` makes the square over
  `Spec κ(t') ⟶ Spec κ(b t')` cartesian (`isPullback_fiberBaseChange`), compatibly with the maps
  to `X ×_S T` (`residueFieldBaseChange_comp_familyBaseChange`);
* coefficients transport along it, naturally in the module (`familyBaseChangeFiberNatIso`);
* for `p` quasi-compact and quasi-separated and `M` quasicoherent on `X ×_S T`, the point-fibre
  cohomology dimensions and Euler characteristics of `b^* M` at `t'` and of `M` at `b t'` agree
  (`modulePointFiberCohomologyDimension_familyBaseChange`,
  `modulePointFiberEulerChar_familyBaseChange`), by flat base change over the field extension
  (`moduleCohomologyDimension_pullbackMap_of_eq`), and so does vanishing
  (`subsingleton_modulePointFiberCohomology_familyBaseChange_iff`, through
  `subsingleton_moduleCohomology_iff_fieldBaseChange`).

These are the dimension and vanishing forms of the fibre comparison
`H^i(X_{t'}, L_{t'}(n)) = H^i(X_{p(t')}, L_{p(t')}(n)) ⊗ k_{t'}` of Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, pp. 28–29, which makes the fibre conditions of the Picard strata well
defined; no flatness, properness or Noetherian hypothesis is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

section FieldExtension

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **Field extension at a base point.** For a field map `φ : K ⟶ K'` and a base point
`k' = Spec φ ≫ k`, the dimensions on `X ×_S Spec K'` and on `X ×_S Spec K` agree, for
quasi-compact quasi-separated `p` and quasicoherent `M`. -/
theorem moduleCohomologyDimension_pullbackMap_of_eq [QuasiCompact p] [QuasiSeparated p]
    {K K' : Type u} [Field K] [Field K'] (k : Spec (.of K) ⟶ S)
    (φ : CommRingCat.of K ⟶ CommRingCat.of K') (k' : Spec (.of K') ⟶ S)
    (hk : Spec.map φ ≫ k = k') (M : (pullback p k).Modules) [M.IsQuasicoherent] (q : ℕ) :
    moduleCohomologyDimension (pullback.snd p k')
        ((Scheme.Modules.pullback (pullback.map p k' p k (𝟙 X) (Spec.map φ) (𝟙 S) (by simp)
          (by simp [hk]))).obj M) q =
      moduleCohomologyDimension (pullback.snd p k) M q := by
  subst hk
  rw [← moduleCohomologyDimension_fieldBaseChange (pullback.snd p k) φ.hom M q]
  exact (moduleCohomologyDimension_pullback_snd_pullback_snd p k (Spec.map φ) M q).symm

end FieldExtension

variable {X S T T' : Scheme.{u}} (p : X ⟶ S) (s : T ⟶ S) (s' : T' ⟶ S) (b : T' ⟶ T)
  (hb : b ≫ s = s')

/-- The base-change map `X ×_S T' ⟶ X ×_S T` of a morphism `b : T' ⟶ T` over `S`. -/
abbrev familyBaseChange : pullback p s' ⟶ pullback p s :=
  pullback.map p s' p s (𝟙 X) b (𝟙 S) (by simp) (by simp [hb])

include hb in
/-- The residue-field point of `t'` over `S`, through `κ(b t') ⟶ κ(t')`. -/
theorem specMap_residueFieldMap_comp_eq (t' : T') :
    Spec.map (b.residueFieldMap t') ≫ (T.fromSpecResidueField (b t') ≫ s) =
      T'.fromSpecResidueField t' ≫ s' := by
  rw [← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    Category.assoc, hb]

/-- The base-change map `X ×_S Spec κ(t') ⟶ X ×_S Spec κ(b t')` of the residue-field map
`κ(b t') ⟶ κ(t')`. -/
abbrev fiberBaseChange (t' : T') :
    pullback p (T'.fromSpecResidueField t' ≫ s') ⟶ pullback p (T.fromSpecResidueField (b t') ≫ s) :=
  pullback.map p (T'.fromSpecResidueField t' ≫ s') p (T.fromSpecResidueField (b t') ≫ s) (𝟙 X)
    (Spec.map (b.residueFieldMap t')) (𝟙 S) (by simp)
    (by simp [specMap_residueFieldMap_comp_eq s s' b hb t'])

/-- The two maps `X ×_S Spec κ(t') ⟶ X ×_S T`: through `X ×_S T'`, and through
`X ×_S Spec κ(b t')`. -/
theorem residueFieldBaseChange_comp_familyBaseChange (t' : T') :
    residueFieldBaseChange p s' t' ≫ familyBaseChange p s s' b hb =
      fiberBaseChange p s s' b hb t' ≫ residueFieldBaseChange p s (b t') := by
  apply pullback.hom_ext
  · simp
  · simp [residueFieldBaseChange, familyBaseChange]

/-- **Fibre identification**: the fibre `X ×_S Spec κ(t')` of `X ×_S T'` at `t'` is the base
change of the fibre `X ×_S Spec κ(b t')` of `X ×_S T` at `b t'` along
`Spec κ(t') ⟶ Spec κ(b t')`. -/
theorem isPullback_fiberBaseChange (t' : T') :
    IsPullback (fiberBaseChange p s s' b hb t') (pullback.snd p (T'.fromSpecResidueField t' ≫ s'))
      (pullback.snd p (T.fromSpecResidueField (b t') ≫ s)) (Spec.map (b.residueFieldMap t')) := by
  refine IsPullback.of_right ?_ (by simp [fiberBaseChange])
    (IsPullback.of_hasPullback p (T.fromSpecResidueField (b t') ≫ s))
  have h1 : fiberBaseChange p s s' b hb t' ≫ pullback.fst p (T.fromSpecResidueField (b t') ≫ s) =
      pullback.fst p (T'.fromSpecResidueField t' ≫ s') := by
    simp [fiberBaseChange]
  rw [h1, specMap_residueFieldMap_comp_eq s s' b hb t']
  exact IsPullback.of_hasPullback _ _

/-- **Coefficient transport along the fibre identification**: the fibre of `b^* M` at `t'` is the
pullback of the fibre of `M` at `b t'` along `X ×_S Spec κ(t') ⟶ X ×_S Spec κ(b t')`, naturally
in `M`. -/
def familyBaseChangeFiberNatIso (t' : T') :
    Scheme.Modules.pullback (familyBaseChange p s s' b hb) ⋙
        Scheme.Modules.pullback (residueFieldBaseChange p s' t') ≅
      Scheme.Modules.pullback (residueFieldBaseChange p s (b t')) ⋙
        Scheme.Modules.pullback (fiberBaseChange p s s' b hb t') :=
  Scheme.Modules.pullbackComp _ _ ≪≫
    Scheme.Modules.pullbackCongr (residueFieldBaseChange_comp_familyBaseChange p s s' b hb t') ≪≫
    (Scheme.Modules.pullbackComp _ _).symm

/-- **Point-fibre cohomology is invariant under base change of the family**: for `p`
quasi-compact and quasi-separated, `M` quasicoherent on `X ×_S T` and `b : T' ⟶ T` over `S`, the
point-fibre dimension of `b^* M` at `t'` is that of `M` at `b t'`, in every degree. -/
theorem modulePointFiberCohomologyDimension_familyBaseChange [QuasiCompact p] [QuasiSeparated p]
    (M : (pullback p s).Modules) [M.IsQuasicoherent] (q : ℕ) (t' : T') :
    modulePointFiberCohomologyDimension (pullback.snd p s')
        ((Scheme.Modules.pullback (familyBaseChange p s s' b hb)).obj M) q t' =
      modulePointFiberCohomologyDimension (pullback.snd p s) M q (b t') := by
  rw [modulePointFiberCohomologyDimension_eq_pullbackMap,
    modulePointFiberCohomologyDimension_eq_pullbackMap,
    ← moduleCohomologyDimension_pullbackMap_of_eq p (K := T.residueField (b t'))
      (K' := T'.residueField t') _ (b.residueFieldMap t') _
      (specMap_residueFieldMap_comp_eq s s' b hb t') _ q]
  exact moduleCohomologyDimension_congr _ ((familyBaseChangeFiberNatIso p s s' b hb t').app M) q

/-- **Point-fibre Euler characteristics are invariant under base change of the family.** -/
theorem modulePointFiberEulerChar_familyBaseChange [QuasiCompact p] [QuasiSeparated p]
    (M : (pullback p s).Modules) [M.IsQuasicoherent] (t' : T') :
    modulePointFiberEulerChar (pullback.snd p s')
        ((Scheme.Modules.pullback (familyBaseChange p s s' b hb)).obj M) t' =
      modulePointFiberEulerChar (pullback.snd p s) M (b t') := by
  unfold modulePointFiberEulerChar
  congr 1
  funext q
  rw [modulePointFiberCohomologyDimension_familyBaseChange p s s' b hb M q t']

section Vanishing

/-- Vanishing of original cohomology transports along an isomorphism of schemes with an
isomorphic coefficient. -/
theorem subsingleton_moduleCohomology_iff_of_isIso {P Y : Scheme.{u}} (e : P ⟶ Y) [IsIso e]
    (M : Y.Modules) {N : P.Modules} (C : (Scheme.Modules.pullback e).obj M ≅ N) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf Y M) q) ↔
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf P N) q) := by
  have : (Scheme.Modules.pullback e).IsEquivalence :=
    Scheme.Modules.pullback_isEquivalence_of_isIso e
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app M ≫
      (Scheme.Modules.pushforward e).map C.hom) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app M ≫
      (Scheme.Modules.pushforward e).map C.hom))
  exact (Equiv.ofBijective _ (moduleCohomologyMapAlong_bijective e
    ((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app M ≫
      (Scheme.Modules.pushforward e).map C.hom) q)).subsingleton_congr

/-- Vanishing of original cohomology is invariant under isomorphism of coefficients. -/
theorem subsingleton_moduleCohomology_congr {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf Y M) q) ↔
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf Y N) q) :=
  subsingleton_moduleCohomology_iff_of_isIso (𝟙 Y) M ((Scheme.Modules.pullbackId Y).app M ≪≫ e) q

/-- Vanishing on `(X ×_S T) ×_T W` and on `X ×_S W`, for the pullbacks of a module on
`X ×_S T` along the two canonical maps, agree. -/
theorem subsingleton_moduleCohomology_pullback_snd_pullback_snd_iff {W : Scheme.{u}}
    (x : W ⟶ T) (M : (pullback p s).Modules) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd p s) x)).obj M)) q) ↔
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _ ((Scheme.Modules.pullback
        (pullback.map p (x ≫ s) p s (𝟙 X) x (𝟙 S) (by simp) (by simp))).obj M)) q) :=
  (subsingleton_moduleCohomology_iff_of_isIso (pullbackLeftPullbackSndIso p s x).hom _
    ((Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (pullbackLeftPullbackSndIso_hom_pullbackMap p s x)).app M)
    q).symm

/-- **Point fibres as residue-field base changes**, for vanishing. -/
theorem subsingleton_modulePointFiberCohomology_iff_pullbackMap (M : (pullback p s).Modules)
    (q : ℕ) (t : T) :
    Subsingleton (modulePointFiberCohomology (pullback.snd p s) M q t) ↔
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _
        ((Scheme.Modules.pullback (residueFieldBaseChange p s t)).obj M)) q) :=
  subsingleton_moduleCohomology_pullback_snd_pullback_snd_iff p s (T.fromSpecResidueField t) M q

/-- **Field extension at a base point**, for vanishing: for `k' = Spec φ ≫ k`, vanishing on
`X ×_S Spec K'` and on `X ×_S Spec K` agree (qcqs `p`, quasicoherent `M`). -/
theorem subsingleton_moduleCohomology_pullbackMap_of_eq [QuasiCompact p] [QuasiSeparated p]
    {K K' : Type u} [Field K] [Field K'] (k : Spec (.of K) ⟶ S)
    (φ : CommRingCat.of K ⟶ CommRingCat.of K') (k' : Spec (.of K') ⟶ S)
    (hk : Spec.map φ ≫ k = k') (M : (pullback p k).Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _ ((Scheme.Modules.pullback
        (pullback.map p k' p k (𝟙 X) (Spec.map φ) (𝟙 S) (by simp) (by simp [hk]))).obj M)) q) ↔
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _ M) q) := by
  subst hk
  rw [subsingleton_moduleCohomology_iff_fieldBaseChange (pullback.snd p k) φ.hom M q]
  exact (subsingleton_moduleCohomology_pullback_snd_pullback_snd_iff p k (Spec.map φ) M q).symm

/-- **Point-fibre vanishing is invariant under base change of the family**: for `p`
quasi-compact and quasi-separated, `M` quasicoherent on `X ×_S T` and `b : T' ⟶ T` over `S`,
the point-fibre cohomology of `b^* M` at `t'` vanishes exactly when that of `M` at `b t'` does. -/
theorem subsingleton_modulePointFiberCohomology_familyBaseChange_iff [QuasiCompact p]
    [QuasiSeparated p] (M : (pullback p s).Modules) [M.IsQuasicoherent] (q : ℕ) (t' : T') :
    Subsingleton (modulePointFiberCohomology (pullback.snd p s')
        ((Scheme.Modules.pullback (familyBaseChange p s s' b hb)).obj M) q t') ↔
      Subsingleton (modulePointFiberCohomology (pullback.snd p s) M q (b t')) := by
  rw [subsingleton_modulePointFiberCohomology_iff_pullbackMap,
    subsingleton_modulePointFiberCohomology_iff_pullbackMap,
    ← subsingleton_moduleCohomology_pullbackMap_of_eq p (K := T.residueField (b t'))
      (K' := T'.residueField t') _ (b.residueFieldMap t') _
      (specMap_residueFieldMap_comp_eq s s' b hb t') _ q]
  exact subsingleton_moduleCohomology_congr ((familyBaseChangeFiberNatIso p s s' b hb t').app M) q

end Vanishing

end AlgebraicGeometry.Scheme.Cohomology
