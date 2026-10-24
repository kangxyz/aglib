/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.FieldExtension
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Proper.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism

/-!
# Geometric fibre concentration from residue-field fibres

`FibreCohomologyConcentrated f M r` (the premise of the locally Noetherian cohomology and base
change theorem `localFreeCohomologyBaseChange_of_isLocallyNoetherian`) is stated at
algebraically closed field points. Kleiman's hypotheses are stated at the points of the base:
`H^i(X_t, L_t) = 0` for `i ≥ 1` and every `t` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, condition (4.8.3), p. 29, used with `m = 0` in the proof of Thm 4.8,
p. 30; the criterion 3.10 (v), p. 25, needs only `H^1`). This file supplies the passage between
them.

* `fibreCohomology_residueField_comparison`: for a quasi-compact quasi-separated `f` and
  quasicoherent `M`, the fibre cohomology over a field point `Spec K ⟶ Spec κ(s) ⟶ S` has the
  dimension of the point-fibre cohomology at `s`, and vanishes exactly when it does. This is
  flat base change along the field extension `κ(s) → K` (Stacks Project, Tag 02KH, Cohomology
  of Schemes, Lemma 30.5.2), through `moduleCohomologyFieldBaseChangeEquiv`.
* `fibreCohomologyConcentrated_of_modulePointFiberCohomology`: point-fibre conditions at every
  point of `S` give `FibreCohomologyConcentrated f M r`.
* `isLocallyConstant_modulePointFiberCohomologyDimension_zero`: for a proper `f` over a locally
  Noetherian base and a coherent relatively flat `M` whose higher point-fibre cohomology
  vanishes everywhere, `s ↦ h^0(X_s, M_s)` is locally constant, since it is the fibre Euler
  characteristic (Stacks Project, Tag 0B9T, Lemma 36.32.2). Its fibres are open and closed
  (`isClopen_setOf_modulePointFiberCohomologyDimension_zero_eq`).
* `fibreCohomologyConcentrated_pullback_of_range_subset`: over any `g : T ⟶ S` landing where
  `h^0 = r` and the higher point-fibre cohomology vanishes, the base-changed family is
  geometrically concentrated in degree zero with rank `r`.

Consumer: Picard plan row F15 (statement 15a, the locally free regime of Kleiman 3.10), with
`localFreeCohomologyBaseChange_of_isLocallyNoetherian`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)

/-- Fibre cohomology of a base-changed family at `t` is fibre cohomology of the original family
at `t ≫ g`: equal dimension, and simultaneous vanishing. This is the transport of
`FibreCohomologyConcentrated.pullback`, stated at one field point and at variable data. -/
theorem fibreCohomology_pullback_comparison {T : Scheme.{u}} (g : T ⟶ S) {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ T) (n : ℕ) :
    Module.finrank K (fibreCohomology (Limits.pullback.snd f g)
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M) K t n) =
      Module.finrank K (fibreCohomology f M K (t ≫ g) n) ∧
    (Subsingleton (fibreCohomology (Limits.pullback.snd f g)
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M) K t n) ↔
      Subsingleton (fibreCohomology f M K (t ≫ g) n)) := by
  let e := pullbackLeftPullbackSndIso f g t
  let p := Limits.pullback.fst f (t ≫ g)
  let a := Limits.pullback.fst (Limits.pullback.snd f g) t
  let c := Limits.pullback.fst f g
  let b := Limits.pullback.snd f (t ≫ g)
  let d := Limits.pullback.snd (Limits.pullback.snd f g) t
  let P := (Scheme.Modules.pullback p).obj M
  let N := (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback c).obj M)
  let C : (Scheme.Modules.pullback e.hom).obj P ≅ N :=
    (Scheme.Modules.pullbackComp e.hom p).app M ≪≫
      (Scheme.Modules.pullbackCongr (pullbackLeftPullbackSndIso_hom_fst f g t)).app M ≪≫
        ((Scheme.Modules.pullbackComp a c).app M).symm
  have hw : e.hom ≫ b = d := pullbackLeftPullbackSndIso_hom_snd f g t
  let α := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let β := d.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hα : e.hom.appTop.hom.comp α = β.comp (RingHom.id K) := by
    dsimp only [α, β]
    rw [← hw, Scheme.Hom.comp_appTop]
    rfl
  let : Module K (Sheaf.H.{u + 1} (moduleAddSheaf _ P) n) := moduleCohomologyModuleOfHom _ α P n
  let : Module K (Sheaf.H.{u + 1} (moduleAddSheaf _ N) n) := moduleCohomologyModuleOfHom _ β N n
  let E := moduleCohomologyRestrictionIsoOfPullbackIso e.hom (RingHom.id K) α β hα P C n ≪≫
    ModuleCat.restrictScalarsId'App (RingHom.id K) rfl _
  exact ⟨E.toLinearEquiv.finrank_eq.symm, E.toLinearEquiv.toEquiv.subsingleton_congr.symm⟩

/-- The fibre cohomology over the field point `Spec K ⟶ Spec κ(s) ⟶ S` is the field base change
of the point-fibre cohomology at `s`: it has the same dimension, and it vanishes exactly when
the point-fibre cohomology vanishes (Stacks Project, Tag 02KH). -/
theorem fibreCohomology_residueField_comparison [QuasiCompact f] [QuasiSeparated f]
    [M.IsQuasicoherent] {K : Type u} [Field K] (t : Spec (.of K) ⟶ S) (s : S)
    (σ : S.residueField s →+* K)
    (ht : t = Spec.map (CommRingCat.ofHom σ) ≫ S.fromSpecResidueField s) (n : ℕ) :
    Module.finrank K (fibreCohomology f M K t n) = modulePointFiberCohomologyDimension f M n s ∧
      (Subsingleton (fibreCohomology f M K t n) ↔
        Subsingleton (modulePointFiberCohomology f M n s)) := by
  subst ht
  have : QuasiSeparated (Limits.pullback.snd f (S.fromSpecResidueField s)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have h := fibreCohomology_pullback_comparison f M (S.fromSpecResidueField s)
    (Spec.map (CommRingCat.ofHom σ)) n
  exact ⟨h.1.symm.trans (moduleCohomology_finrank_fieldBaseChange
      (Limits.pullback.snd f (S.fromSpecResidueField s)) σ
      ((Scheme.Modules.pullback (Limits.pullback.fst f (S.fromSpecResidueField s))).obj M) n),
    h.2.symm.trans (subsingleton_moduleCohomology_iff_fieldBaseChange
      (Limits.pullback.snd f (S.fromSpecResidueField s)) σ
      ((Scheme.Modules.pullback (Limits.pullback.fst f (S.fromSpecResidueField s))).obj M)
      n).symm⟩

/-- Point-fibre concentration at every point of the base gives geometric fibre concentration. -/
theorem fibreCohomologyConcentrated_of_modulePointFiberCohomology [QuasiCompact f]
    [QuasiSeparated f] [M.IsQuasicoherent] (r : ℕ)
    (h0 : ∀ s : S, modulePointFiberCohomologyDimension f M 0 s = r)
    (hpos : ∀ (s : S) (n : ℕ), 0 < n → Subsingleton (modulePointFiberCohomology f M n s)) :
    FibreCohomologyConcentrated f M r := by
  intro K _ _ t
  obtain ⟨⟨s, φ⟩, hsφ⟩ := (Scheme.SpecToEquivOfField K S).symm.surjective t
  have ht : t = Spec.map (CommRingCat.ofHom φ.hom) ≫ S.fromSpecResidueField s := hsφ.symm
  exact ⟨(fibreCohomology_residueField_comparison f M t s φ.hom ht 0).1.trans (h0 s),
    fun n hn => (fibreCohomology_residueField_comparison f M t s φ.hom ht n).2.mpr (hpos s n hn)⟩

/-- If the higher point-fibre cohomology vanishes everywhere, the degree-zero point-fibre
dimension is locally constant: it is the fibre Euler characteristic. -/
theorem isLocallyConstant_modulePointFiberCohomologyDimension_zero [IsLocallyNoetherian S]
    [IsProper f] (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (hpos : ∀ (s : S) (n : ℕ), 0 < n → Subsingleton (modulePointFiberCohomology f M n s)) :
    IsLocallyConstant (modulePointFiberCohomologyDimension f M 0) := by
  have hχ : modulePointFiberEulerChar f M =
      fun s => ((modulePointFiberCohomologyDimension f M 0 s : ℕ) : ℤ) := by
    funext s
    have hvan : ∀ q, 0 < q → modulePointFiberCohomologyDimension f M q s = 0 := fun q hq => by
      have := hpos s q hq
      exact Module.finrank_zero_of_subsingleton
    rw [modulePointFiberEulerChar_eq_sum_range f M s 0 hvan]
    simp
  have h := isLocallyConstant_modulePointFiberEulerChar_of_proper f M hM hflat
  rw [hχ] at h
  exact IsLocallyConstant.desc _ (Nat.cast : ℕ → ℤ) h Nat.cast_injective

/-- Under the same hypotheses, the locus where `h^0(X_s, M_s) = r` is open and closed. -/
theorem isClopen_setOf_modulePointFiberCohomologyDimension_zero_eq [IsLocallyNoetherian S]
    [IsProper f] (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (hpos : ∀ (s : S) (n : ℕ), 0 < n → Subsingleton (modulePointFiberCohomology f M n s))
    (r : ℕ) : IsClopen {s : S | modulePointFiberCohomologyDimension f M 0 s = r} :=
  (isLocallyConstant_modulePointFiberCohomologyDimension_zero f M hM hflat hpos).isClopen_fiber r

/-- Over a base change `g : T ⟶ S` landing in the points where `h^0 = r` and the higher
point-fibre cohomology vanishes, the base-changed family is geometrically concentrated in
degree zero with rank `r`. -/
theorem fibreCohomologyConcentrated_pullback_of_range_subset [QuasiCompact f] [QuasiSeparated f]
    [M.IsQuasicoherent] {T : Scheme.{u}} (g : T ⟶ S) (r : ℕ)
    (h0 : ∀ s ∈ Set.range g, modulePointFiberCohomologyDimension f M 0 s = r)
    (hpos : ∀ s ∈ Set.range g, ∀ n : ℕ, 0 < n →
      Subsingleton (modulePointFiberCohomology f M n s)) :
    FibreCohomologyConcentrated (Limits.pullback.snd f g)
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M) r := by
  intro K _ _ t
  obtain ⟨⟨s, φ⟩, hsφ⟩ := (Scheme.SpecToEquivOfField K S).symm.surjective (t ≫ g)
  have ht : t ≫ g = Spec.map (CommRingCat.ofHom φ.hom) ≫ S.fromSpecResidueField s := hsφ.symm
  have hs : s ∈ Set.range g := by
    refine ⟨t (IsLocalRing.closedPoint K), ?_⟩
    have h1 : (t ≫ g) (IsLocalRing.closedPoint K) = s := by
      rw [ht]
      exact Scheme.fromSpecResidueField_apply s _
    simpa using h1
  have hc (n : ℕ) := fibreCohomology_pullback_comparison f M g t n
  have hp (n : ℕ) := fibreCohomology_residueField_comparison f M (t ≫ g) s φ.hom ht n
  exact ⟨((hc 0).1.trans (hp 0).1).trans (h0 s hs),
    fun n hn => (hc n).2.mpr ((hp n).2.mpr (hpos s hs n hn))⟩

end AlgebraicGeometry.Scheme.Cohomology
