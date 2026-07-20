/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import ComputableReals.CRealsFast.Dyadic
import ComputableReals.CRealsFast.Ball
import ComputableReals.CRealsFast.FastReal

/-!
# The fast executable engine

This module is the aggregator for the three layers of the engine, kept so
that `import ComputableReals.CRealsFast` continues to mean what it always
did:

* `CRealsFast/Dyadic.lean` — exact dyadic scalars `man * 2^exp`;
* `CRealsFast/Ball.lean` — midpoint ± radius enclosures over the dyadics;
* `CRealsFast/FastReal.lean` — precision-indexed streams of balls, the
  executable real number type.
-/
