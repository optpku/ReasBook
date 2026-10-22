/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_6_13
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped RelatorSetIr

section

variable {X : Type u}

-- Layer triage:
-- `source-facing`: a single minimal strictly quadratic cyclic word `q`, together with the
-- hypothesis that `q` uses every generator of the ambient alphabet, and the irreducibility rank
-- of the represented relator set.
-- `core/canonical`: `CyclicWord X`, its canonical length `CyclicWord.length`,
-- `CyclicWord.HasFullSupport`, `ConjClasses (FreeGroup X)` with the owner set view
-- `ConjClasses.carrier`, and the relator-set owner notation `Ir(W)` in the ambient free group.
-- `bridge/view`: a single cyclic word determines its represented relator set
-- `(q.toConjClasses).carrier`, obtained from the canonical conjugacy-class bridge
-- `q.toConjClasses`; the full-support hypothesis is the bridge ensuring that this ambient free
-- group has no unused generators beyond the letters of `q`.
-- Domain sampling:
-- 1. `CyclicWord` from Definition `1-4-17` is the chapter owner abstraction for cyclic words.
-- 2. `CyclicWord.toConjClasses` from Definition `1-4-17` is the canonical bridge from one cyclic
--    word to its conjugacy class in `FreeGroup X`.
-- 3. `ConjClasses.carrier` with `ConjClasses.mem_carrier_iff_mk_eq` is the canonical owner API
--    for the represented relator set of a conjugacy class.
-- 4. `CyclicWord.HasFullSupport` from Definition `1-4-17` is the owner predicate asserting that
--    the ambient alphabet contributes no unused free generators.
-- 5. `CyclicWord.IsMinimalStrictlyQuadratic` from Proposition `1-7-11` is the chapter owner
--    predicate for the textbook single-word hypothesis.
-- 6. `Ir(W)` from Proposition `1-6-13` is the existing relator-set owner abstraction for
--    irreducibility rank, so this file should reuse it directly rather than introduce a parallel
--    cyclic-word owner with the wrong ambient alphabet.
-- Primitive vs. derived:
-- the primitive data here are only the cyclic word `q`; the represented relator set
-- `(q.toConjClasses).carrier` and its irreducibility rank are canonical derived owner views.

namespace CyclicWord

/-- Proposition 1-7-13: if `q` is a minimal strictly quadratic cyclic word and `q` uses every
generator of the ambient alphabet, then the irreducibility rank of its represented relator set is
the greatest integer in one quarter of the cyclic length of `q`. -/
-- Proof sketch: the lower bound comes from pairing the generators appearing in `q` and
-- specializing every second one so as to obtain a free quotient of rank `⌊|q| / 4⌋`. For the
-- upper bound, Proposition `1-6-15` expresses the relator-set irreducibility rank through the
-- number of singular steps in a reduction to triviality, while Proposition `1-7-12` shows that
-- each singular step can decrease the length of a minimal strictly quadratic word by at most `4`.
-- Since the generators appearing in a strictly quadratic word occur in signed pairs, their number
-- is `|q| / 2`, and these two bounds coincide once the ambient alphabet has no unused generators.
theorem ir_eq_length_div_four_of_minimal_strictlyQuadratic
    (q : CyclicWord X) (hq : q.IsMinimalStrictlyQuadratic) (hfull : q.HasFullSupport) :
    Ir((q.toConjClasses).carrier) = ↑(q.length / 4) := sorry

end CyclicWord

end
