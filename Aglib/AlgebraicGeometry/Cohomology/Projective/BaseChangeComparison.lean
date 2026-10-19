/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Composite
public import Aglib.AlgebraicGeometry.Cohomology.Projective.LargeTwistBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiberVanishing
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Finiteness
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.ToSpec

/-!
# Base change of global sections onto a flat base change, from the fibres

Let `A` and `B` be Noetherian rings, `σ : A →+* B`, and `G` a coherent module on
`P^n_A = ProjectiveSpace A ι`, `ι ≃ Fin (n + 1)`. Write `X_B = P^n_A ×_{Spec A} Spec B` with
projections `p`, `f_B`, `G_B = p^* G`, and for `s ∈ Spec A` write `X_s`, `G_s` for the fibre
product over `κ(s)` and the pulled-back coefficient. Assume, for every point `s = σ⁻¹ t` in the
image of `Spec B ⟶ Spec A`:

* (C) the fibre map `κ(s) ⊗_A H^0(P^n_A, G) ⟶ H^0(X_s, G_s)` is an isomorphism;
* (B) `H^q(X_s, G_s) = 0` for every `q ≥ 1`;

and that `G_B` is relatively flat over `Spec B`. Then the base-change map
`B ⊗_A H^0(P^n_A, G) ⟶ H^0(X_B, G_B)` is an isomorphism and its target is a projective `B`-module
(`moduleCohomologyBaseChangeMap_isIso_and_projective_of_fiberwise`). Neither `G` nor `σ` need be
flat. Nitsure's (B) and (C) hold at every point of `Spec A`; the forms with hypotheses at every
point are the twisted corollaries below.

This is the comparison `φ^* π_* F(m) ≅ π_{T*} F_T(m)` in the proof of the universal property of
the flattening stratification, Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Thm 4.3 (ii), proof pp. 22–23, for affine `S = Spec A` and
`T = Spec B`, with `G = F(m)`; there (B) and (C) are Nitsure's statements (B) and (C) for
`m ≥ N`. The twisted form, with `F_B` flat on `P^n_B`, is
`moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_fiberwise`; the same with the fibres
and the base change written on `P^n_{κ(s)}` and `P^n_B` is
`bijective_baseChangeTwist_and_projective_of_fiberwise_projectiveSpace`.

The proof, following Nitsure p. 22:
1. The fibres of `G_B` are field base changes of fibres of `G`
   (`subsingleton_moduleCohomology_residueField_pullback`), so `H^q` of every fibre of `G_B`
   vanishes for `q ≥ 1`; as `G_B` is flat, `H^q(X_B, G_B) = 0` for `q ≥ 1`
   (`subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper`). Cohomology and base
   change in the vanishing case (`VanishingProjective`, on the embedding
   `X_B ≅ P^n_B`) makes `H^0(X_B, G_B)` projective and its fibre maps isomorphisms.
2. At `t ∈ Spec B` over `s`, the composite
   `κ(t) ⊗_B (B ⊗_A H^0(G)) ⟶ κ(t) ⊗_B H^0(G_B) ⟶ H^0((X_B)_t, (G_B)_t)` is an isomorphism, by (C)
   at `s` and flat base change along `κ(s) → κ(t)`
   (`isIso_moduleCohomologyBaseChangeMap_comp_residueField`). With step 1, `κ(t) ⊗` the base-change
   map is an isomorphism for every `t`.
3. A map of finite modules with projective target that is an isomorphism on every residue-field
   fibre is an isomorphism (`LinearMap.bijective_of_residueField_baseChange_bijective`).

Both (B) and (C) enter only at the points `σ⁻¹ t`. Step 1 uses (B) in every degree `q ≥ 1`,
through the vanishing case of cohomology and base change; (C) is used as an isomorphism, in
step 2.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsNoetherianRing B]
  (σ : A →+* B) {ι : Type u}

/-- **Vanishing for the flat base change, from the fibres**: if the positive-degree cohomology of
the fibre of a coherent `G` on `P^n_A` vanishes at every point `σ⁻¹ t`, `t ∈ Spec B`, and the
base change `G_B` to
`X_B = P^n_A ×_{Spec A} Spec B` is flat over `B`, then `H^q(X_B, G_B) = 0` for every `q ≥ 1`. -/
theorem subsingleton_moduleCohomology_baseChange_of_fiberwise (n : ℕ) (e : ι ≃ Fin (n + 1))
    (G : (ProjectiveSpace A ι).Modules) (hG : affineLocallyFiniteType (ProjectiveSpace A ι) G)
    (hB : ∀ (t : PrimeSpectrum B) (q : ℕ), q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom
        (algebraMap A (PrimeSpectrum.comap σ t).asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom
        (algebraMap A (PrimeSpectrum.comap σ t).asIdeal.ResidueField))))).obj G)) q))
    (hflat : relativeFlat (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (Spec.map (CommRingCat.ofHom σ)))).obj G))
    (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom σ)))).obj G)) q) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : G.IsQuasicoherent := quasicoherent_of_affineCharts G (fun A j _ => (hG A j).1)
  exact subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper _ _
    (affineLocallyFiniteType_pullback _ hG) hflat q fun t =>
      subsingleton_moduleCohomology_residueField_pullback (toSpec A ι) σ G q t (hB t q hq)

/-- **Base change onto a flat base change, from the fibres** (Nitsure, arXiv:math/0504590v1,
Thm 4.3 (ii), proof pp. 22–23, over affine Noetherian `S = Spec A`, `T = Spec B`): if, at every
point `σ⁻¹ t` with `t ∈ Spec B`, the fibre map of `H^0` of a coherent `G` on `P^n_A` is an
isomorphism and the positive-degree cohomology of the fibre vanishes, and the base change `G_B` to
`X_B = P^n_A ×_{Spec A} Spec B` is flat over `B`, then `B ⊗_A H^0(P^n_A, G) ⟶ H^0(X_B, G_B)` is an
isomorphism and `H^0(X_B, G_B)` is a projective `B`-module. -/
theorem moduleCohomologyBaseChangeMap_isIso_and_projective_of_fiberwise
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (G : (ProjectiveSpace A ι).Modules)
    (hG : affineLocallyFiniteType (ProjectiveSpace A ι) G)
    (hC : ∀ t : PrimeSpectrum B, IsIso (moduleCohomologyBaseChangeMap (toSpec A ι)
      (algebraMap A (PrimeSpectrum.comap σ t).asIdeal.ResidueField) G 0))
    (hB : ∀ (t : PrimeSpectrum B) (q : ℕ), q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom
        (algebraMap A (PrimeSpectrum.comap σ t).asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom
        (algebraMap A (PrimeSpectrum.comap σ t).asIdeal.ResidueField))))).obj G)) q))
    (hflat : relativeFlat (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (Spec.map (CommRingCat.ofHom σ)))).obj G)) :
    IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ G 0) ∧
      (let β := (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
       letI := moduleCohomologyModuleOfHom _ β ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
         (Spec.map (CommRingCat.ofHom σ)))).obj G) 0
       Module.Projective B (Sheaf.H.{u + 1}
         (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom σ)))).obj G)) 0)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : G.IsQuasicoherent := quasicoherent_of_affineCharts G (fun A j _ => (hG A j).1)
  have hMB := affineLocallyFiniteType_pullback
    (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))) hG
  have hi := baseChangeIso_inv_toSpec σ ι
  have hvan := subsingleton_moduleCohomology_baseChange_of_fiberwise σ n e G hG hB hflat
  have hproj := moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding
    (i := (baseChangeIso σ ι).inv) e hi hMB hflat hvan
  refine ⟨?_, hproj⟩
  let φ := moduleCohomologyBaseChangeMap (toSpec A ι) σ G 0
  have hext (t : PrimeSpectrum B) :
      IsIso ((ModuleCat.extendScalars (algebraMap B t.asIdeal.ResidueField)).map φ) := by
    have := moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding
      (i := (baseChangeIso σ ι).inv) e hi hMB hflat hvan 0 (algebraMap B t.asIdeal.ResidueField)
    have := isIso_moduleCohomologyBaseChangeMap_comp_residueField (toSpec A ι) σ G 0 t (hC t)
    exact IsIso.of_isIso_comp_right _ (moduleCohomologyBaseChangeMap
      (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
      (algebraMap B t.asIdeal.ResidueField) _ 0)
  let β := (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let := moduleCohomologyModuleOfHom _ β ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
    (Spec.map (CommRingCat.ofHom σ)))).obj G) 0
  have hbc (t : PrimeSpectrum B) :
      Function.Bijective (φ.hom.baseChange t.asIdeal.ResidueField) := by
    have h₁ := ModuleCat.extendScalarsAlgebraObjIso_naturality B t.asIdeal.ResidueField φ
    have h₂ : ModuleCat.ofHom (φ.hom.baseChange t.asIdeal.ResidueField) =
        (ModuleCat.extendScalarsAlgebraObjIso B t.asIdeal.ResidueField _).inv ≫
          (ModuleCat.extendScalars (algebraMap B t.asIdeal.ResidueField)).map φ ≫
            (ModuleCat.extendScalarsAlgebraObjIso B t.asIdeal.ResidueField _).hom := by
      rw [h₁, Iso.inv_hom_id_assoc]
    have := hext t
    have : IsIso (ModuleCat.ofHom (φ.hom.baseChange t.asIdeal.ResidueField)) := by
      rw [h₂]
      infer_instance
    exact (ConcreteCategory.isIso_iff_bijective _).mp this
  let α := (toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let := moduleCohomologyModuleOfHom _ α G 0
  have : Module.Finite A (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) G) 0) :=
    moduleCohomology_finite_of_proper A (toSpec A ι) G hG 0
  have := ModuleCat.finite_extendScalars σ
    (ModuleCat.of A (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) G) 0))
  have := moduleCohomology_finite_of_proper B
    (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))) _ hMB 0
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr
    (LinearMap.bijective_of_residueField_baseChange_bijective φ.hom hbc)

/-- The pullback along `X_B ≅ P^n_B` and back is the identity. -/
def baseChangeIsoPullbackInvHomIso {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)
    (ι : Type u) (N : (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).Modules) :
    (Scheme.Modules.pullback (baseChangeIso σ ι).inv).obj
        ((Scheme.Modules.pullback (baseChangeIso σ ι).hom).obj N) ≅ N :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeIso σ ι).inv_hom_id).app N ≪≫
      (Scheme.Modules.pullbackId _).app N

omit [IsNoetherianRing B] in
/-- **Flatness of `F_B` on `P^n_B` gives flatness of the base change of every twist to the
fibre product**: if `π^* F` is flat over `B` on `P^n_B` (`π = map σ ι`), then the pullback of
`F(m)` to `X_B = P^n_A ×_{Spec A} Spec B` is flat over `B`. -/
theorem relativeFlat_pullback_twist_of_relativeFlat_map [Finite ι]
    (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F) (m : ℤ)
    (hflat : relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (map σ ι)).obj F)) :
    relativeFlat (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F)) := by
  have hFm := twistingTensor_affineLocallyFiniteType A ι m F hF
  have : ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj
      F).IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (hFm A j).1)
  have h₁ : relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (baseChangeIso σ ι).hom).obj
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (Spec.map (CommRingCat.ofHom σ)))).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F))) :=
    relativeFlat_of_iso (toSpec B ι) (baseChangeTwistIso σ ι m F)
      (twistingTensor_relativeFlat (toSpec B ι) _ hflat m)
  have hsq : IsPullback (baseChangeIso σ ι).inv
      (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))) (toSpec B ι)
      (𝟙 (Spec (CommRingCat.of B))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, baseChangeIso_inv_toSpec]⟩
  exact relativeFlat_of_iso _ (baseChangeIsoPullbackInvHomIso σ ι _).symm
    (relativeFlat_pullback_of_isPullback hsq _ h₁)

/-- **The comparison for twists, with `F_B` flat on `P^n_B`** (Nitsure, arXiv:math/0504590v1,
Thm 4.3 (ii), proof pp. 22–23, over affine Noetherian `S = Spec A`, `T = Spec B`): let `F` be
coherent on `P^n_A` and `m : ℤ`. If for every point `s` of `Spec A` the fibre map
`κ(s) ⊗_A H^0(P^n_A, F(m)) ⟶ H^0(X_s, F(m)_s)` is an isomorphism and `H^q(X_s, F(m)_s) = 0` for
`q ≥ 1`, and `F_B = π^* F` is flat over `B` on `P^n_B`, then the base-change map
`B ⊗_A H^0(P^n_A, F(m)) ⟶ H^0(X_B, F(m)_B)` is an isomorphism and its target is a projective
`B`-module. -/
theorem moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_fiberwise (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F) (m : ℤ)
    (hC : ∀ s : PrimeSpectrum A, IsIso (moduleCohomologyBaseChangeMap (toSpec A ι)
      (algebraMap A s.asIdeal.ResidueField)
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0))
    (hB : ∀ (s : PrimeSpectrum A) (q : ℕ), q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec A ι)
        (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (Spec.map (CommRingCat.ofHom (algebraMap A s.asIdeal.ResidueField))))).obj
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F))) q))
    (hflat : relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (map σ ι)).obj F)) :
    IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0) ∧
      (let β := (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
       letI := moduleCohomologyModuleOfHom _ β ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
         (Spec.map (CommRingCat.ofHom σ)))).obj
         ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F)) 0
       Module.Projective B (Sheaf.H.{u + 1}
         (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom σ)))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F)))
              0)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact moduleCohomologyBaseChangeMap_isIso_and_projective_of_fiberwise σ n e _
    (twistingTensor_affineLocallyFiniteType A ι m F hF) (fun t => hC _) (fun t => hB _)
    (relativeFlat_pullback_twist_of_relativeFlat_map σ F hF m hflat)

/-- **The comparison for twists in the coordinates of `P^n_{κ(s)}` and `P^n_B`** (Nitsure,
arXiv:math/0504590v1, Thm 4.3 (ii), proof pp. 22–23, over affine Noetherian `S = Spec A`,
`T = Spec B`): let `F` be coherent on `P^n_A`, `m : ℤ`, and write `F_s = π_s^* F` on
`P^n_{κ(s)}`, `F_B = π^* F` on `P^n_B`. Assume that for every point `s` of `Spec A` the fibre map
`κ(s) ⊗_A H^0(P^n_A, F(m)) ⟶ H^0(P^n_{κ(s)}, F_s(m))` is bijective and
`H^q(P^n_{κ(s)}, F_s(m)) = 0` for `q ≥ 1`, and that `F_B` is flat over `B`. Then the base-change
map `B ⊗_A H^0(P^n_A, F(m)) ⟶ H^0(P^n_B, F_B(m))` is bijective and `H^0(P^n_B, F_B(m))` is a
projective `B`-module. The maps to `P^n_{κ(s)}` and `P^n_B` are the base-change maps followed by
the transport `baseChangeTwistCohomologyHom`, as in
`exists_twist_baseChange_bijective_projectiveSpace`. -/
theorem bijective_baseChangeTwist_and_projective_of_fiberwise_projectiveSpace (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F) (m : ℤ)
    (hC : ∀ s : PrimeSpectrum A, Function.Bijective
      (baseChangeTwistCohomologyHom (algebraMap A s.asIdeal.ResidueField) ι m F 0 ∘
        moduleCohomologyBaseChangeMap (toSpec A ι) (algebraMap A s.asIdeal.ResidueField)
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0))
    (hB : ∀ (s : PrimeSpectrum A) (q : ℕ), q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace s.asIdeal.ResidueField ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace s.asIdeal.ResidueField ι)
          (twistingSheaf s.asIdeal.ResidueField ι m)).obj
          ((Scheme.Modules.pullback (map (algebraMap A s.asIdeal.ResidueField) ι)).obj F))) q))
    (hflat : relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (map σ ι)).obj F)) :
    Function.Bijective (baseChangeTwistCohomologyHom σ ι m F 0 ∘
        moduleCohomologyBaseChangeMap (toSpec A ι) σ
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0) ∧
      (let α := (toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace B ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι m)).obj
           ((Scheme.Modules.pullback (map σ ι)).obj F)) 0
       Module.Projective B (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι m)).obj
           ((Scheme.Modules.pullback (map σ ι)).obj F))) 0)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hC' (s : PrimeSpectrum A) : IsIso (moduleCohomologyBaseChangeMap (toSpec A ι)
      (algebraMap A s.asIdeal.ResidueField)
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((Function.Bijective.of_comp_iff'
        (baseChangeTwistCohomologyHom_bijective (algebraMap A s.asIdeal.ResidueField) ι m F 0)
        _).mp (hC s))
  have hB' (s : PrimeSpectrum A) (q : ℕ) (hq : q ≠ 0) := by
    have := hB s q hq
    exact (baseChangeTwistCohomologyHom_bijective (algebraMap A s.asIdeal.ResidueField) ι m F
      q).1.subsingleton
  have hflat' := relativeFlat_pullback_twist_of_relativeFlat_map σ F hF m hflat
  have hFm := twistingTensor_affineLocallyFiniteType A ι m F hF
  obtain ⟨hiso, -⟩ := moduleCohomologyBaseChangeMap_isIso_and_projective_of_fiberwise σ n e _
    hFm (fun t => hC' _) (fun t => hB' _) hflat'
  refine ⟨(baseChangeTwistCohomologyHom_bijective σ ι m F 0).comp
    ((ConcreteCategory.isIso_iff_bijective _).mp hiso), ?_⟩
  have hvan (q : ℕ) (hq : q ≠ 0) : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace B ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι m)).obj
          ((Scheme.Modules.pullback (map σ ι)).obj F))) q) := by
    have := subsingleton_moduleCohomology_baseChange_of_fiberwise σ n e _ hFm (fun t => hB' _)
      hflat' q hq
    exact (baseChangeTwistCohomologyHom_bijective σ ι m F q).2.subsingleton
  exact moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding (i := 𝟙 _) e
    (Category.id_comp _)
    (twistingTensor_affineLocallyFiniteType B ι m _ (affineLocallyFiniteType_pullback _ hF))
    (twistingTensor_relativeFlat (toSpec B ι) _ hflat m) hvan

end AlgebraicGeometry.Scheme.Cohomology
