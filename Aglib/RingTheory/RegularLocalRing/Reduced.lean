/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.Domain
public import Mathlib.RingTheory.LocalProperties.Reduced

/-! # Regular rings are reduced -/

@[expose] public section

namespace IsRegularRing

/-- A regular ring is reduced: every maximal localization is a regular local
domain, and reducedness descends from maximal localizations. -/
theorem isReduced_of_regular (R : Type*) [CommRing R] [IsRegularRing R] :
    IsReduced R := by
  apply isReduced_ofLocalizationMaximal R
  intro m hm
  let : m.IsMaximal := hm
  let : IsDomain (Localization.AtPrime m) :=
    IsRegularLocalRing.isDomain_of_regularLocal (Localization.AtPrime m)
  infer_instance

end IsRegularRing
