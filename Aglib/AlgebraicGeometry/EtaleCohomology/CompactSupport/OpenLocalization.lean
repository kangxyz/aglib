/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.PointRemoval
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.Comparisons

/-!
# The open-closed sequence on an open subscheme, with compact supports

Let `jU : U ⟶ X` be an open immersion, `jV : V ⟶ U` an open immersion and `i : Z ⟶ U` a
closed immersion with `Set.range jV = (Set.range i)ᶜ`, such that `i ≫ jU` is again a closed
immersion. For an abelian sheaf `F` on `U`, the original sequence
`0 → jV_! jV^* F → F → i_* i^* F → 0` on `U` (Stacks, Tag 095L) is short exact, and the long
exact sequence of compactly supported cohomology along `jU` (`CompactSupport.longSequence`)
applies to it. Its terms are identified as follows.

* `H^q_c(U, jV_! A) ≃+ H^q_c(V, A)` (`lowerShriekAddEquiv`), through the original composition
  comparison `etaleLowerShriekCompIso`. The original map `jV_! jV^* F ⟶ F` (the counit)
  becomes the extension map `extensionCohomologyMap` of `CompactSupport.PointRemoval`
  (`extensionMap_eq_compIso_counit`, `extensionCohomologyMap_eq_map_counit`).
* `H^q_c(U, i_* M) ≃+ H^q(Z, M)` (`directImageAddEquiv`), through the isomorphism
  `jU_! ∘ i_* ≅ (i ≫ jU)_*` (`etaleLowerShriekDirectImageIso`; Stacks, Tag 0GJ1, for the
  cartesian square of `i ≫ jU` and `jU`) and the finite direct-image comparison
  `Finite.finiteCohomologyDirectImageAddEquiv` along the closed immersion `i ≫ jU`. The
  isomorphism `jU_! ∘ i_* ≅ (i ≫ jU)_*` is the original counit of `jU_! ⊣ jU^*` at
  `(i ≫ jU)_* M`, which is invertible because the stalks of `(i ≫ jU)_* M` vanish off `U`
  (Stacks, Tag 0F70, second statement).

The resulting long exact sequence is

`… → H^r_c(V, F|_V) → H^r_c(U, F) → H^r(Z, i^* F) → H^{r+1}_c(V, F|_V) → …`

(`exact_extensionCohomologyMap_compactRestriction`, `exact_compactRestriction_compactBoundary`,
`exact_compactBoundary_extensionCohomologyMap`); its first map is injective in degree zero.

For a finite set `D` of points of `U` that are closed in `X`, with `Set.range jV = Dᶜ`, the
inclusion `FiniteClosedSupport.inclusion U D` of the literal point scheme satisfies these
hypotheses (`isClosedImmersion_inclusion_comp`), and the third term is
`H^r(pointScheme U D, i^* F)`. If the residue fields at `D` are separably closed, it vanishes for
`r > 0`. This is the lower row of the diagram of Milne, *Lectures on Étale Cohomology* v2.21,
Thm. 14.7, proof, Step 2, p. 94: the compact cohomology sequence of
`0 → j_! F|_V → F → i_* i^* F → 0` on `U`.

The first map is the same as that of the point-removal sequence on `X` of
`CompactSupport.PointRemoval`; the comparison of the third terms is not formalized here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

section DirectImage

variable {U Z X : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]

/-- For a closed immersion `f : Z ⟶ X` whose image lies in the open `U`, the original counit
`jU_! jU^* (f_* M) ⟶ f_* M` is an isomorphism: it is one on the stalks at geometric points of
`U`, and both stalks vanish elsewhere. -/
theorem etaleLowerShriek_counit_directImage_isIso_of_range_subset (f : Z ⟶ X) [IsClosedImmersion f]
    (hf : Set.range f ⊆ Set.range jU) (M : AbelianSheaf.{u, u + 1} Z) :
    IsIso ((etaleLowerShriekAdjunction jU).counit.app ((directImage f).obj M)) := by
  apply StalkUniverse.isIso_of_original_geometricStalks (𝟙 X)
  intro x
  let η := FibrewiseClosed.geometricPoint x.val
  by_cases hj : η default ∈ Set.range jU
  · obtain ⟨ζ, hζ⟩ := exists_openImmersion_pointLift jU η hj
    exact etaleLowerShriek_counit_stalk_isIso jU ζ η hζ _
  · have h₁ := isZero_etaleLowerShriek_stalk_of_no_lift jU η
      (fun ζ hζ => hj ⟨ζ default, congrArg (fun g : _ ⟶ X => g default) hζ⟩)
      ((inverseImage jU).obj ((directImage f).obj M))
    have h₂ := isZero_closedDirectImage_stalk_of_no_lift f η
      (fun ζ hζ => hj (hf ⟨ζ default, congrArg (fun g : _ ⟶ X => g default) hζ⟩)) M
    exact ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

variable (i : Z ⟶ U)

/-- `jU^* ((i ≫ jU)_* M) ≅ i_* M`: the inverse of the original direct-image composition,
followed by the original counit of `jU^* ⊣ jU_*`, which is invertible for an open immersion. -/
def inverseImageDirectImageCompIso :
    directImage (i ≫ jU) ⋙ inverseImage jU ≅ directImage i :=
  Functor.isoWhiskerRight (directImageCompIso jU i).symm (inverseImage jU) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (directImage i) (asIso (inverseImageAdjunction jU).counit) ≪≫
    Functor.rightUnitor _

variable [IsClosedImmersion (i ≫ jU)]

/-- Extension by zero along an open immersion of a direct image from a closed part that stays
closed in `X`: `jU_! ∘ i_* ≅ (i ≫ jU)_*` (Stacks, Tag 0GJ1, for the cartesian square of
`i ≫ jU` and `jU`). It is `jU_!` of the inverse of `inverseImageDirectImageCompIso` followed by
the original counit of `jU_! ⊣ jU^*`. -/
def etaleLowerShriekDirectImageIso :
    directImage i ⋙ etaleLowerShriek jU ≅ directImage (i ≫ jU) :=
  letI : IsIso (Functor.whiskerLeft (directImage (i ≫ jU))
      (etaleLowerShriekAdjunction jU).counit) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M =>
      etaleLowerShriek_counit_directImage_isIso_of_range_subset jU (i ≫ jU)
        (by rintro _ ⟨z, rfl⟩; exact ⟨i z, rfl⟩) M
  Functor.isoWhiskerRight (inverseImageDirectImageCompIso jU i).symm (etaleLowerShriek jU) ≪≫
    Functor.associator _ _ _ ≪≫
    asIso (Functor.whiskerLeft (directImage (i ≫ jU)) (etaleLowerShriekAdjunction jU).counit) ≪≫
    Functor.rightUnitor _

end DirectImage

namespace CompactSupport

section DirectImage

variable {U Z X : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU] (i : Z ⟶ U)
  [IsClosedImmersion (i ≫ jU)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} Z)]

/-- `H^q_c(U, i_* M) ≃+ H^q(Z, M)`: `Sheaf.H` of `etaleLowerShriekDirectImageIso`, then the
finite direct-image comparison along the closed immersion `i ≫ jU`. -/
def directImageAddEquiv (M : AbelianSheaf.{u, u + 1} Z) (q : ℕ) :
    H jU ((directImage i).obj M) q ≃+ Sheaf.H.{w'} M q :=
  ((Sheaf.functorH (Scheme.smallEtaleTopology X) q).mapIso
      ((etaleLowerShriekDirectImageIso jU i).app M)).addCommGroupIsoToAddEquiv.trans
    (Finite.finiteCohomologyDirectImageAddEquiv (i ≫ jU) M q)

theorem directImageAddEquiv_apply (M : AbelianSheaf.{u, u + 1} Z) (q : ℕ)
    (x : H jU ((directImage i).obj M) q) :
    directImageAddEquiv jU i M q x =
      Finite.finiteCohomologyDirectImageAddEquiv (i ≫ jU) M q
        (Sheaf.H.map ((etaleLowerShriekDirectImageIso jU i).hom.app M) q x) :=
  rfl

end DirectImage

section Composition

variable {V U X : Scheme.{u}} (jV : V ⟶ U) [IsOpenImmersion jV] (jU : U ⟶ X)
  [IsOpenImmersion jU] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- `H^q_c(U, jV_! A) ≃+ H^q_c(V, A)`: `Sheaf.H` of the inverse of the original composition
comparison `(jV ≫ jU)_! ≅ jU_! ∘ jV_!`. -/
def lowerShriekAddEquiv (A : AbelianSheaf.{u, u + 1} V) (q : ℕ) :
    H jU ((etaleLowerShriek jV).obj A) q ≃+ H (jV ≫ jU) A q :=
  ((Sheaf.functorH (Scheme.smallEtaleTopology X) q).mapIso
    ((etaleLowerShriekCompIso jU jV).app A).symm).addCommGroupIsoToAddEquiv

theorem lowerShriekAddEquiv_apply (A : AbelianSheaf.{u, u + 1} V) (q : ℕ)
    (x : H jU ((etaleLowerShriek jV).obj A) q) :
    lowerShriekAddEquiv jV jU A q x =
      Sheaf.H.map ((etaleLowerShriekCompIso jU jV).inv.app A) q x :=
  rfl

theorem lowerShriekAddEquiv_symm_apply (A : AbelianSheaf.{u, u + 1} V) (q : ℕ)
    (x : H (jV ≫ jU) A q) :
    (lowerShriekAddEquiv jV jU A q).symm x =
      Sheaf.H.map ((etaleLowerShriekCompIso jU jV).hom.app A) q x :=
  rfl

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] in
/-- The extension map of the point-removal sequence is the original composition comparison
followed by `jU_!` of the original counit `jV_! jV^* F ⟶ F`. -/
theorem extensionMap_eq_compIso_counit (F : AbelianSheaf.{u, u + 1} U) :
    extensionMap jV jU F =
      (etaleLowerShriekCompIso jU jV).hom.app ((inverseImage jV).obj F) ≫
        (etaleLowerShriek jU).map ((etaleLowerShriekAdjunction jV).counit.app F) := by
  apply ((etaleLowerShriekAdjunction (jV ≫ jU)).homEquiv ((inverseImage jV).obj F)
    ((etaleLowerShriek jU).obj F)).injective
  have h₁ : (etaleLowerShriekAdjunction (jV ≫ jU)).homEquiv _ _ (extensionMap jV jU F) =
      (restrictionExtensionIso jV jU F).inv := by
    rw [extensionMap, ← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]
  have h₂ := etaleLowerShriekCompIso_unit jU jV ((inverseImage jV).obj F)
  have h₃ : (etaleLowerShriekAdjunction (jV ≫ jU)).homEquiv _ _
      ((etaleLowerShriekCompIso jU jV).hom.app ((inverseImage jV).obj F)) =
      ((etaleLowerShriekAdjunction jV).unit.app ((inverseImage jV).obj F) ≫
        (inverseImage jV).map ((etaleLowerShriekAdjunction jU).unit.app
          ((etaleLowerShriek jV).obj ((inverseImage jV).obj F)))) ≫
        (inverseImageComp jU jV).inv.app
          ((etaleLowerShriek jU).obj ((etaleLowerShriek jV).obj ((inverseImage jV).obj F))) := by
    rw [← h₂, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [h₁, Adjunction.homEquiv_naturality_right, h₃, Category.assoc, Category.assoc,
    ← (inverseImageComp jU jV).inv.naturality, Functor.comp_map, ← Functor.map_comp_assoc,
    Adjunction.unit_naturality, Functor.map_comp, Category.assoc,
    Adjunction.right_triangle_components_assoc]
  rfl

/-- On cohomology, the extension map is `H.map` of the original counit `jV_! jV^* F ⟶ F` after
`lowerShriekAddEquiv`. -/
theorem extensionCohomologyMap_eq_map_counit (F : AbelianSheaf.{u, u + 1} U) (r : ℕ)
    (x : H (jV ≫ jU) ((inverseImage jV).obj F) r) :
    extensionCohomologyMap jV jU F r x =
      H.map jU ((etaleLowerShriekAdjunction jV).counit.app F) r
        ((lowerShriekAddEquiv jV jU ((inverseImage jV).obj F) r).symm x) := by
  rw [extensionCohomologyMap, extensionMap_eq_compIso_counit, lowerShriekAddEquiv_symm_apply,
    H.map_apply]
  exact Sheaf.H.map_comp_apply _ _ x

end Composition

section Sequence

variable {V Z U X : Scheme.{u}} (jV : V ⟶ U) [IsOpenImmersion jV] (jU : U ⟶ X)
  [IsOpenImmersion jU] (i : Z ⟶ U) [IsClosedImmersion (i ≫ jU)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} Z)]

/-- The map `H^r_c(U, F) → H^r(Z, i^* F)`: the original unit `F ⟶ i_* i^* F` on compactly
supported cohomology, followed by `directImageAddEquiv`. -/
def compactRestriction (F : AbelianSheaf.{u, u + 1} U) (r : ℕ) :
    H jU F r →+ Sheaf.H.{w'} ((inverseImage i).obj F) r :=
  (directImageAddEquiv jU i ((inverseImage i).obj F) r).toAddMonoidHom.comp
    (H.map jU ((inverseImageAdjunction i).unit.app F) r)

theorem compactRestriction_apply (F : AbelianSheaf.{u, u + 1} U) (r : ℕ) (x : H jU F r) :
    compactRestriction jU i F r x =
      directImageAddEquiv jU i ((inverseImage i).obj F) r
        (H.map jU ((inverseImageAdjunction i).unit.app F) r x) :=
  rfl

variable [IsClosedImmersion i] (hcomp : Set.range jV = (Set.range i)ᶜ)
  (F : AbelianSheaf.{u, u + 1} U)

/-- The connecting map `H^{n₀}(Z, i^* F) → H^{n₁}_c(V, F|_V)`: the inverse of
`directImageAddEquiv`, the original connecting map of compactly supported cohomology for the
open-closed sequence on `U`, and `lowerShriekAddEquiv`. -/
def compactBoundary (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Sheaf.H.{w'} ((inverseImage i).obj F) n₀ →+ H (jV ≫ jU) ((inverseImage jV).obj F) n₁ :=
  (lowerShriekAddEquiv jV jU ((inverseImage jV).obj F) n₁).toAddMonoidHom.comp
    ((δ jU (abelianLocalization_shortExact jV i hcomp F) n₀ n₁ h).comp
      (directImageAddEquiv jU i ((inverseImage i).obj F) n₀).symm.toAddMonoidHom)

theorem compactBoundary_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Sheaf.H.{w'} ((inverseImage i).obj F) n₀) :
    compactBoundary jV jU i hcomp F n₀ n₁ h x =
      lowerShriekAddEquiv jV jU ((inverseImage jV).obj F) n₁
        (δ jU (abelianLocalization_shortExact jV i hcomp F) n₀ n₁ h
          ((directImageAddEquiv jU i ((inverseImage i).obj F) n₀).symm x)) :=
  rfl

include hcomp

/-- Exactness at `H^r_c(U, F)`. -/
theorem exact_extensionCohomologyMap_compactRestriction (r : ℕ) :
    Function.Exact (extensionCohomologyMap jV jU F r) (compactRestriction jU i F r) := by
  let e := lowerShriekAddEquiv jV jU ((inverseImage jV).obj F) r
  have hex := exact_map_f_map_g jU (abelianLocalization_shortExact jV i hcomp F) r
  intro y
  change directImageAddEquiv jU i ((inverseImage i).obj F) r
      (H.map jU ((inverseImageAdjunction i).unit.app F) r y) = 0 ↔ _
  refine (AddEquiv.map_eq_zero_iff _).trans ((hex y).trans ⟨?_, ?_⟩)
  · rintro ⟨x, rfl⟩
    exact ⟨e x, (extensionCohomologyMap_eq_map_counit jV jU F r (e x)).trans
      (congrArg (H.map jU ((etaleLowerShriekAdjunction jV).counit.app F) r)
        (e.symm_apply_apply x))⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, (extensionCohomologyMap_eq_map_counit jV jU F r x).symm⟩

/-- Exactness at `H^{n₀}(Z, i^* F)`. -/
theorem exact_compactRestriction_compactBoundary (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (compactRestriction jU i F n₀) (compactBoundary jV jU i hcomp F n₀ n₁ h) := by
  let e := directImageAddEquiv jU i ((inverseImage i).obj F) n₀
  let e' := lowerShriekAddEquiv jV jU ((inverseImage jV).obj F) n₁
  have hex := exact_map_g_δ jU (abelianLocalization_shortExact jV i hcomp F) n₀ n₁ h
  intro y
  change e' (δ jU (abelianLocalization_shortExact jV i hcomp F) n₀ n₁ h (e.symm y)) = 0 ↔ _
  refine (AddEquiv.map_eq_zero_iff e').trans ((hex (e.symm y)).trans ⟨?_, ?_⟩)
  · rintro ⟨x, hx⟩
    exact ⟨x, (e.eq_symm_apply).mp hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, (e.symm_apply_apply _).symm⟩

/-- Exactness at `H^{n₁}_c(V, F|_V)`. -/
theorem exact_compactBoundary_extensionCohomologyMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (compactBoundary jV jU i hcomp F n₀ n₁ h)
      (extensionCohomologyMap jV jU F n₁) := by
  let e := directImageAddEquiv jU i ((inverseImage i).obj F) n₀
  let e' := lowerShriekAddEquiv jV jU ((inverseImage jV).obj F) n₁
  have hex := exact_δ_map_f jU (abelianLocalization_shortExact jV i hcomp F) n₀ n₁ h
  intro y
  rw [extensionCohomologyMap_eq_map_counit]
  refine (hex (e'.symm y)).trans ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    calc compactBoundary jV jU i hcomp F n₀ n₁ h (e x) =
          e' (δ jU (abelianLocalization_shortExact jV i hcomp F) n₀ n₁ h x) :=
        congrArg (fun z => e' (δ jU (abelianLocalization_shortExact jV i hcomp F) n₀ n₁ h z))
          (e.symm_apply_apply x)
      _ = y := (congrArg e' hx).trans (e'.apply_symm_apply y)
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, (e'.symm_apply_apply _).symm⟩

omit [IsClosedImmersion (i ≫ jU)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} Z)] in
/-- The extension map is injective in degree zero, since the original counit
`jV_! jV^* F ⟶ F` is a monomorphism. -/
theorem extensionCohomologyMap_zero_injective_of_closedImmersion :
    Function.Injective (extensionCohomologyMap jV jU F 0) := by
  have : Mono ((etaleLowerShriek jU).map ((etaleLowerShriekAdjunction jV).counit.app F)) :=
    (shortExact_etaleLowerShriek jU (abelianLocalization_shortExact jV i hcomp F)).mono_f
  have hinj : Function.Injective
      (H.map jU ((etaleLowerShriekAdjunction jV).counit.app F) 0) :=
    Abelian.Ext.postcomp_mk₀_injective_of_mono _ _
  intro x y hxy
  rw [extensionCohomologyMap_eq_map_counit, extensionCohomologyMap_eq_map_counit] at hxy
  exact (lowerShriekAddEquiv jV jU ((inverseImage jV).obj F) 0).symm.injective (hinj hxy)

end Sequence

section Points

open Curves.FiniteClosedSupport

variable {V U X : Scheme.{u}} (jV : V ⟶ U) [IsOpenImmersion jV] (jU : U ⟶ X)
  [IsOpenImmersion jU] (D : Set U) (hfin : D.Finite)
  (hclosed : ∀ x ∈ D, IsClosed ({jU x} : Set X))

include hclosed in
/-- A point of `U` that is closed in `X` is closed in `U`. -/
theorem isClosed_singleton_of_isClosed_image : ∀ x ∈ D, IsClosed ({x} : Set U) := by
  intro x hx
  have h : (jU : U → X) ⁻¹' {jU x} = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact jU.isOpenEmbedding.injective.eq_iff
  rw [← h]
  exact (hclosed x hx).preimage jU.continuous

include hfin hclosed in
/-- The literal point scheme of a finite set of points of `U` that are closed in `X` is a
closed subscheme of `X` through `inclusion U D ≫ jU`. -/
theorem isClosedImmersion_inclusion_comp : IsClosedImmersion (inclusion U D ≫ jU) := by
  let : IsClosedImmersion (inclusion U D) :=
    inclusion_isClosedImmersion U D hfin (isClosed_singleton_of_isClosed_image jU D hclosed)
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  have h : Set.range (inclusion U D ≫ jU) = ⋃ x ∈ D, ({jU x} : Set X) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨inclusion U D t, (range_inclusion U D).subset ⟨t, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, rfl⟩ := (range_inclusion U D).symm.subset hx
      exact ⟨t, rfl⟩
  rw [h]
  exact hfin.isClosed_biUnion hclosed

include hfin in
/-- With separably closed residue fields at `D`, every coefficient on the point scheme is acyclic
in positive degree; in particular the third term vanishes for `r > 0`. -/
theorem subsingleton_H_inverseImage_inclusion_of_sepClosed
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pointScheme U D))] (F : AbelianSheaf.{u, u + 1} U)
    (hsep : ∀ x : D, IsSepClosed (U.residueField x.val)) (r : ℕ) (hr : 0 < r) :
    Subsingleton (Sheaf.H.{w'} ((inverseImage (inclusion U D)).obj F) r) :=
  subsingleton_H U D hfin hsep _ r hr

variable (hD : Set.range jV = Dᶜ) (F : AbelianSheaf.{u, u + 1} U)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pointScheme U D))]

/-- The map `H^r_c(U, F) → H^r(pointScheme U D, i^* F)` for `i = inclusion U D`. -/
def compactPointRestriction (r : ℕ) :
    H jU F r →+ Sheaf.H.{w'} ((inverseImage (inclusion U D)).obj F) r :=
  letI := isClosedImmersion_inclusion_comp jU D hfin hclosed
  compactRestriction jU (inclusion U D) F r

/-- The connecting map `H^{n₀}(pointScheme U D, i^* F) → H^{n₁}_c(V, F|_V)` for
`i = inclusion U D`. -/
def compactPointBoundary (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Sheaf.H.{w'} ((inverseImage (inclusion U D)).obj F) n₀ →+
      H (jV ≫ jU) ((inverseImage jV).obj F) n₁ :=
  letI := isClosedImmersion_inclusion_comp jU D hfin hclosed
  letI := inclusion_isClosedImmersion U D hfin (isClosed_singleton_of_isClosed_image jU D hclosed)
  compactBoundary jV jU (inclusion U D) (range_eq_compl_range_inclusion D jV hD) F n₀ n₁ h

include hD

/-- Exactness at `H^r_c(U, F)` in the point case. -/
theorem exact_extensionCohomologyMap_compactPointRestriction (r : ℕ) :
    Function.Exact (extensionCohomologyMap jV jU F r)
      (compactPointRestriction jU D hfin hclosed F r) := by
  let := isClosedImmersion_inclusion_comp jU D hfin hclosed
  let := inclusion_isClosedImmersion U D hfin (isClosed_singleton_of_isClosed_image jU D hclosed)
  exact exact_extensionCohomologyMap_compactRestriction jV jU (inclusion U D)
    (range_eq_compl_range_inclusion D jV hD) F r

/-- Exactness at `H^{n₀}(pointScheme U D, i^* F)` in the point case. -/
theorem exact_compactPointRestriction_compactPointBoundary (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (compactPointRestriction jU D hfin hclosed F n₀)
      (compactPointBoundary jV jU D hfin hclosed hD F n₀ n₁ h) := by
  let := isClosedImmersion_inclusion_comp jU D hfin hclosed
  let := inclusion_isClosedImmersion U D hfin (isClosed_singleton_of_isClosed_image jU D hclosed)
  exact exact_compactRestriction_compactBoundary jV jU (inclusion U D)
    (range_eq_compl_range_inclusion D jV hD) F n₀ n₁ h

/-- Exactness at `H^{n₁}_c(V, F|_V)` in the point case. -/
theorem exact_compactPointBoundary_extensionCohomologyMap (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (compactPointBoundary jV jU D hfin hclosed hD F n₀ n₁ h)
      (extensionCohomologyMap jV jU F n₁) := by
  let := isClosedImmersion_inclusion_comp jU D hfin hclosed
  let := inclusion_isClosedImmersion U D hfin (isClosed_singleton_of_isClosed_image jU D hclosed)
  exact exact_compactBoundary_extensionCohomologyMap jV jU (inclusion U D)
    (range_eq_compl_range_inclusion D jV hD) F n₀ n₁ h

end Points

end CompactSupport

end AlgebraicGeometry.Scheme.EtaleCohomology
