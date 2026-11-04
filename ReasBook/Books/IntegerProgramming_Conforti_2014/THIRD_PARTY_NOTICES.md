# Source notices and attribution scope

## Original textbook

Integer Programming, Michele Conforti, Gérard Cornuéjols and Giacomo Zambelli,
Springer, Graduate Texts in Mathematics 271 (2014). Printed ISBN 978-3-319-11007-3;
eBook ISBN 978-3-319-11008-0; DOI 10.1007/978-3-319-11008-0.
The title and imprint pages of the submitter-supplied PDF identify
© Springer International Publishing Switzerland 2014. This notice identifies the
printed textbook and is not assigned to the separate Lean implementation.
The PDF itself is not included in this contribution.

## First-party formalization

Ziyu Wang and Zaiwen Wen were explicitly confirmed as the project formalization
contributors on 2026-11-04.
Opening Authors fields in 1010 first-party chapter/support/integration modules use
that project-level attribution and cite the README's Confirmed formalization
attribution section. This records project responsibility, not sole authorship of
each proof line. A personal copyright holder or GitHub username was not supplied
and has not been invented. Existing ReasBook project headers use this Authors,
Apache-license and provenance form without inventing a legacy copyright holder.

The received snapshot includes no code generator for the full formalization.
The header-sync helper preserves upstream notices and reapplies this confirmed
project attribution when the candidate's import root or source wrappers are regenerated.
The historical v4.26.0/main contributor roster remains unchanged.

## DPRM / Hilbert10 source

The following 55 files already contained this notice in the received source:

Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer

Those exact notices are retained and moved before the module command, so that they
are now opening file headers. No author or copyright holder is replaced. Their
presence is verified in this candidate's original commit
d3b525dbfb221fa593149214f04e955b1778052e and the downloaded terminal source snapshot.
The associated upstream project is [cameronfreer/hilbert10](https://github.com/cameronfreer/hilbert10).
Its source, README and Apache 2.0 LICENSE were consulted at
53313aa90c6b75c43eb3b16b64ad32fce33042cf during this attribution review. That is a consulted reference;
the exact imported upstream revision was not recorded in the received snapshot
and is not inferred here. Local integration changes include module/import-path
adaptation; moving the notices does not change the executable Lean source.
The repository's Apache 2.0 LICENSE remains in place.

### Files retaining Cameron Freer's original notices

- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Computability.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/DiophToRE.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Endpoints.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/ExistsCode.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/ExistsCodeRepresents.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/FourSquares.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Instantiate.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/IntSolvable.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/AcceptsDioph.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/BlockPacking.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/CleanScratch.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/CodeAlgebra.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/CodeAlgebraComp.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/CodeMachine.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/CodePair.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/CodePrec.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/CodeRfind.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ConfigCoding.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ConfigCodingDioph.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ExpDioph.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ExpDiophChoose.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ForMathlib/BinarySubmask.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ForMathlib/ChooseDigit.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ForMathlib/PairingEnumeration.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ForMathlib/PrimrecInt.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ForMathlib/PrimrecNat.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ForMathlib/RightRename.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/ForMathlib/SubmaskChoose.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/FourSquaresComp.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/PackedRun.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/RegisterMachine.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/RegisterMachineComp.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/RegisterMachineMacros.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/RegisterMachinePair.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/RegisterMachinePairing.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/RegisterMachineRealises.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/RegisterMachineUnpair.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/RunWidth.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/SelectorMask.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/SelectorRegs.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/SelectorRegsDioph.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/SelectorRegsGlobal.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/SubUVComp.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Internal/TupleCoding.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/NatSolvable.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/NormalForm.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/PolyBridge.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/PolynomialCode.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/PolynomialCodeComp.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/PolynomialCodeDenote.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/PolynomialCodeInt.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/PolynomialCodePrimcodable.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/Specialization.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM/SubUV.lean
- Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_3_theorem_1_4/DPRM.lean
