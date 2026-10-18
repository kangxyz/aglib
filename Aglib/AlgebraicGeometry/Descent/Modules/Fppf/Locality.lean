/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Zariski
public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.Precoverage
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# fpqc locality of properties of quasi-coherent sheaves

`Scheme.Modules.prop_of_mem_fpqcPrecoverage`: let `P` be a property of module sheaves that is
invariant under isomorphisms, stable under pullback, local for Zariski covering sieves, and that
descends along `Spec.map φ` for every faithfully flat ring map `φ`, on quasi-coherent sheaves.
Then `P` descends along every fpqc covering presieve, on quasi-coherent sheaves. The proof is the
property-level form of the reduction of [Stack](Stack.lean): Zariski localization on the base
(`affineOpenCover`), a finite affine refinement of an fpqc covering of an affine scheme (Mathlib's
`QuasiCompactCover.exists_hom`), and the coproduct of the refinement, which is affine and maps to
the base by `Spec.map` of a faithfully flat ring map (Mathlib's `flat_and_surjective_SpecMap_iff`).
No descent data are involved.

`Scheme.Modules.prop_of_mem_fppfTopology`: the same for the covering sieves of the fppf topology.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme.Modules

variable (P : ∀ X : Scheme.{u}, X.Modules → Prop)
  (hiso : ∀ (X : Scheme.{u}) (M N : X.Modules), (M ≅ N) → P X M → P X N)
  (hpull : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) (M : Y.Modules), P Y M → P X ((pullback f).obj M))

include hiso hpull in
/-- Pullback along a composite. -/
lemma prop_pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (h : P Y ((pullback g).obj M)) : P X ((pullback (f ≫ g)).obj M) :=
  hiso _ _ _ ((pullbackComp f g).app M) (hpull f _ h)

include hiso in
/-- Pullback along equal morphisms. -/
lemma prop_pullback_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (M : Y.Modules)
    (h : P X ((pullback f).obj M)) : P X ((pullback g).obj M) :=
  hiso _ _ _ ((pullbackCongr hfg).app M) h

variable
  (hzar : ∀ (X : Scheme.{u}) (R : Sieve X), R ∈ Scheme.zariskiTopology X → ∀ M : X.Modules,
    (∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ X), R g → P Y ((pullback g).obj M)) → P X M)
  (haff : ∀ ⦃A B : CommRingCat.{u}⦄ (φ : A ⟶ B), φ.hom.FaithfullyFlat →
    ∀ M : (Spec A).Modules, M.IsQuasicoherent → P _ ((pullback (Spec.map φ)).obj M) → P _ M)

include hiso hpull hzar haff in
-- Without this option the instance `MorphismProperty.RespectsLeft @Flat @IsOpenImmersion` needed
-- by `mem_propQCPrecoverage_iff_exists_quasiCompactCover (P := @Flat)` is not found (checked by
-- removing the option); `Stack.lean` supplies the same instance by hand instead.
set_option backward.isDefEq.respectTransparency.types false in
/-- **Affine base.** -/
lemma prop_of_mem_fpqcPrecoverage_spec {A : CommRingCat.{u}} {R : Presieve (Spec A)}
    (hR : R ∈ Scheme.fpqcPrecoverage (Spec A)) (M : (Spec A).Modules) [M.IsQuasicoherent]
    (hM : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ Spec A), R g → P Y ((pullback g).obj M)) :
    P _ M := by
  classical
  obtain ⟨𝒰, h𝒰, rfl⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover (P := @Flat)).1 hR
  have := h𝒰
  obtain ⟨𝒱, f, hfin, -⟩ := QuasiCompactCover.exists_hom 𝒰
  have : ∀ j, Flat (𝒱.f j) := 𝒱.map_prop
  have h𝒱 : ∀ j, P _ ((pullback (𝒱.f j)).obj M) := fun j ↦
    prop_pullback_congr P hiso (f.w₀ j) M
      (prop_pullback_comp P hiso hpull _ _ M (hM _ ⟨f.s₀ j⟩))
  let X : 𝒱.I₀ → Scheme.{u} := fun j ↦ Spec (𝒱.X j)
  let e := (∐ X).isoSpec
  let q : Spec Γ(∐ X, ⊤) ⟶ Spec A := e.inv ≫ Sigma.desc 𝒱.f
  have : Surjective (Sigma.desc 𝒱.f) := Surjective.sigmaDesc_of_union_range_eq_univ
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨𝒱.idx x, 𝒱.covers x⟩)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective q
  have : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨‹_›, ‹_›⟩
  refine haff φ hff M ‹_› (hzar _ _ (Scheme.zariskiTopology.pullback_stable e.inv
    (sigmaOpenCover X).mem_grothendieckTopology) _ ?_)
  rintro Z t ⟨W, a, _, ⟨l⟩, hat⟩
  have ht : t ≫ Spec.map φ = a ≫ 𝒱.f l := by
    rw [hφ]
    simp only [q, ← reassoc_of% hat]
    exact congrArg (a ≫ ·) (Sigma.ι_comp_desc 𝒱.f l)
  have := prop_pullback_congr P hiso ht.symm M (prop_pullback_comp P hiso hpull a _ M (h𝒱 l))
  exact hiso _ _ _ ((pullbackComp t (Spec.map φ)).app M).symm this

include hiso hpull hzar haff in
/-- **fpqc locality.** A property of module sheaves that is invariant under isomorphisms, stable
under pullback, Zariski-local, and descends along faithfully flat morphisms of affine schemes on
quasi-coherent sheaves descends along every fpqc covering presieve, on quasi-coherent sheaves. -/
theorem prop_of_mem_fpqcPrecoverage {T : Scheme.{u}} {R : Presieve T}
    (hR : R ∈ Scheme.fpqcPrecoverage T) (M : T.Modules) [M.IsQuasicoherent]
    (hM : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ T), R g → P Y ((pullback g).obj M)) :
    P T M := by
  let 𝒰 := T.affineOpenCover
  have h𝒰 : Sieve.ofArrows (fun k ↦ Spec (𝒰.X k)) 𝒰.f ∈ Scheme.zariskiTopology T :=
    𝒰.openCover.mem_grothendieckTopology
  refine hzar T _ h𝒰 M ?_
  rintro Y g ⟨W, a, _, ⟨k⟩, rfl⟩
  refine prop_pullback_comp P hiso hpull a _ M ?_
  have : ((pullback (𝒰.f k)).obj M).IsQuasicoherent := quasicoherent_pullback _ _
  refine prop_of_mem_fpqcPrecoverage_spec P hiso hpull hzar haff
    (Precoverage.pullbackArrows_mem (𝒰.f k) hR) ((pullback (𝒰.f k)).obj M) ?_
  rintro Z _ ⟨Z', r, hr⟩
  have := prop_pullback_comp P hiso hpull (pullback.fst r (𝒰.f k)) r M (hM r hr)
  have := prop_pullback_congr P hiso pullback.condition M this
  exact hiso _ _ _ ((pullbackComp (pullback.snd r (𝒰.f k)) (𝒰.f k)).app M).symm this

include hiso hpull hzar haff in
/-- **fppf locality**, for the covering sieves of `Scheme.fppfTopology`. -/
theorem prop_of_mem_fppfTopology {T : Scheme.{u}} (R : Sieve T)
    (hR : R ∈ Scheme.fppfTopology T) (M : T.Modules) [M.IsQuasicoherent]
    (hM : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ T), R g → P Y ((pullback g).obj M)) :
    P T M := by
  have hR₁ : R ∈ Scheme.fppfPrecoverage.toGrothendieck T := hR
  rw [← Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck] at hR₁
  obtain ⟨R', hR', h⟩ := hR₁
  exact prop_of_mem_fpqcPrecoverage P hiso hpull hzar haff
    (fppfPrecoverage_le_fpqcPrecoverage _ hR') M (fun Y g hg ↦ hM g (h _ g hg))

end AlgebraicGeometry.Scheme.Modules
