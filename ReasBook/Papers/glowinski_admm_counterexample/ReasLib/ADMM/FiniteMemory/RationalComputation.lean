/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalReconstruction
public meta import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalReconstruction

/-! Finite tables and exact checks for rational finite-memory ADMM certificates. -/

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction.Computation

/-- A quadratic contraction omitting terms whose coordinate factor vanishes. -/
def sparseQuadraticStorage {k : ℕ}
    (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (Z : (Fin k × Fin 2) → ℚ) : ℚ :=
  ∑ i, if Z i = 0 then 0 else
    ∑ j, if Z j = 0 then 0 else P i j * Z i * Z j

theorem sparseQuadraticStorage_eq {k : ℕ}
    (P : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (Z : (Fin k × Fin 2) → ℚ) :
    sparseQuadraticStorage P Z = quadraticStorage P Z := by
  rw [quadraticStorage_apply]
  unfold sparseQuadraticStorage
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Z i = 0
  · simp [hi]
  · rw [if_neg hi]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : Z j = 0
    · simp [hj]
    · rw [if_neg hj]


universe u

/-- Tabulate a finite function through a list for transparent kernel evaluation. -/
@[noinline] def tabulateVector {n : Nat} {α : Type u} (f : Fin n → α) : Vector α n :=
  ⟨⟨List.ofFn f⟩, by simp⟩

@[simp] theorem tabulateVector_eq {n : Nat} {α : Type u} (f : Fin n → α) :
    tabulateVector f = Vector.ofFn f := by
  simp [tabulateVector, Vector.ofFn, ← List.toArray_ofFn]

abbrev PairTable (k : ℕ) (α : Type u) := Vector (Vector α 2) k

@[noinline] def tabulatePair {k : ℕ} {α : Type u}
    (f : (Fin k × Fin 2) → α) : PairTable k α :=
  tabulateVector fun i : Fin k ↦ tabulateVector fun j : Fin 2 ↦ f (i, j)

def readPair {k : ℕ} {α : Type u}
    (values : PairTable k α) (p : Fin k × Fin 2) : α := values[p.1][p.2]

theorem read_tabulatePair {k : ℕ} {α : Type u}
    (f : (Fin k × Fin 2) → α) (p : Fin k × Fin 2) :
    readPair (tabulatePair f) p = f p := by
  simp [readPair, tabulatePair]

abbrev MatrixTable (k : ℕ) := PairTable k (PairTable k ℚ)

@[noinline] def tabulateMatrix {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) : MatrixTable k :=
  tabulatePair fun i ↦ tabulatePair (K i)

def readMatrix {k : ℕ} (values : MatrixTable k) :
    Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ :=
  fun i j ↦ readPair (readPair values i) j

theorem read_tabulateMatrix {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) :
    readMatrix (tabulateMatrix K) = K := by
  funext i j
  simp [readMatrix, tabulateMatrix, read_tabulatePair]

abbrev TwoColumnTable (k : ℕ) := PairTable k (Vector ℚ 2)

@[noinline] def tabulateTwoColumns {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin 2) ℚ) : TwoColumnTable k :=
  tabulatePair fun i ↦ tabulateVector (K i)

def readTwoColumns {k : ℕ} (values : TwoColumnTable k) :
    Matrix (Fin k × Fin 2) (Fin 2) ℚ :=
  fun i j ↦ (readPair values i)[j]

theorem read_tabulateTwoColumns {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin 2) ℚ) (i : Fin k × Fin 2) (j : Fin 2) :
    readTwoColumns (tabulateTwoColumns K) i j = K i j := by
  simp [readTwoColumns, tabulateTwoColumns, read_tabulatePair]

/-- Materialize the supply action, its prefix sums, and the completed storage blocks. -/
@[noinline] def storageTable {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    MatrixTable (ℓ + 1) :=
  let q := tabulateTwoColumns (supplyConstantModes c (endpointGamma c e))
  let x := tabulateTwoColumns fun (i : Fin (ℓ + 1) × Fin 2) (j : Fin 2) ↦
    -∑ t : Fin (ℓ + 2), if t ≤ i.1.castSucc then readTwoColumns q (t, i.2) j else 0
  let a := tabulateMatrix (upperTriangleMatrix c e)
  let t := tabulateTwoColumns fun (i : Fin ℓ × Fin 2) (j : Fin 2) ↦
    readTwoColumns x (i.1.castSucc, i.2) j -
      ∑ r : Fin ℓ × Fin 2, readMatrix a i r * constantModes ℓ r j
  let w := tabulateVector fun (i : Fin 2) ↦ tabulateVector fun (j : Fin 2) ↦
    readTwoColumns x (Fin.last ℓ, i) j -
      ∑ r : Fin ℓ × Fin 2, readTwoColumns t r i * constantModes ℓ r j
  tabulateMatrix fun (i j : Fin (ℓ + 1) × Fin 2) ↦
    if hi : i.1 < ℓ then
      if hj : j.1 < ℓ then
        readMatrix a (⟨i.1, hi⟩, i.2) (⟨j.1, hj⟩, j.2)
      else readTwoColumns t (⟨i.1, hi⟩, i.2) j.2
    else if hj : j.1 < ℓ then readTwoColumns t (⟨j.1, hj⟩, j.2) i.2
    else w[i.2][j.2]

theorem storageTable_eq {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    readMatrix (storageTable c e) = storageMatrix c e := by
  funext i j
  simp [storageTable, read_tabulateMatrix, read_tabulateTwoColumns,
    storageMatrix, storageTerminal_apply, storageOffDiagonal_apply, cumulativePrefix_apply,
    Matrix.mul_apply]

@[noinline] def descentTable {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    MatrixTable (ℓ + 2) :=
  let p := storageTable c e
  tabulateMatrix (matrixOfQuadratic fun Z ↦
    sparseQuadraticStorage (readMatrix p) (fun i ↦ Z (i.1.succ, i.2)) -
      sparseQuadraticStorage (readMatrix p) (fun i ↦ Z (i.1.castSucc, i.2)) -
        supply c (endpointGamma c e) Z)

theorem descentTable_eq {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    readMatrix (descentTable c e) = descentMatrix c e := by
  simp [descentTable, read_tabulateMatrix, storageTable_eq,
    sparseQuadraticStorage_eq, descentMatrix]

@[noinline] def principalTable {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    MatrixTable (ℓ + 1) :=
  let data := descentTable c e
  tabulateMatrix fun (i j : Fin (ℓ + 1) × Fin 2) ↦
    readMatrix data (i.1.castSucc, i.2) (j.1.castSucc, j.2)

theorem principalTable_eq {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    readMatrix (principalTable c e) = descentPrincipal c e := by
  funext i j
  simpa [principalTable, read_tabulateMatrix, descentTable_eq] using
    (descentPrincipal_apply c e i j).symm

def optionIndex {ℓ : ℕ} : Option (Fin ℓ) → Fin (ℓ + 1)
  | none => 0
  | some i => i.succ

def optionCoordinate {ℓ : ℕ} (i : Fin (ℓ + 1)) : Option (Fin ℓ) :=
  Fin.cases none some i

theorem optionCoordinate_index {ℓ : ℕ} (i : Option (Fin ℓ)) :
    optionCoordinate (optionIndex i) = i := by
  cases i <;> simp [optionCoordinate, optionIndex]

abbrev WeightTable (ℓ : ℕ) := Vector (Vector ℚ (ℓ + 1)) (ℓ + 1)

structure Weights (ℓ : ℕ) where
  blockF : WeightTable ℓ
  blockJ : WeightTable ℓ

@[noinline] def tabulateWeights {ℓ : ℕ} (c : RationalCase ℓ)
    (b : ADMM.FiniteMemory.Block) : WeightTable ℓ :=
  tabulateVector fun (i : Fin (ℓ + 1)) ↦ tabulateVector fun (j : Fin (ℓ + 1)) ↦
    reconstructMu c b (optionCoordinate i) (optionCoordinate j)

@[noinline] def weightData {ℓ : ℕ} (c : RationalCase ℓ) : Weights ℓ :=
  ⟨tabulateWeights c .F, tabulateWeights c .J⟩

def weightEntry {ℓ : ℕ} (data : Weights ℓ)
    (b : ADMM.FiniteMemory.Block) (i j : Option (Fin ℓ)) : ℚ :=
  let table := match b with | .F => data.blockF | .J => data.blockJ
  table[optionIndex i][optionIndex j]

theorem weightData_eq {ℓ : ℕ} (c : RationalCase ℓ)
    (b : ADMM.FiniteMemory.Block) (i j : Option (Fin ℓ)) :
    weightEntry (weightData c) b i j = reconstructMu c b i j := by
  cases b <;> simp [weightEntry, weightData, tabulateWeights,
    optionCoordinate_index]

@[noinline] def lowerTable {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    MatrixTable (ℓ + 1) :=
  let p := storageTable c e
  let weights := weightData c
  tabulateMatrix (matrixOfQuadratic fun Z ↦
    sparseQuadraticStorage (readMatrix p) Z -
      (∑ b : ADMM.FiniteMemory.Block, ∑ i : Option (Fin ℓ), ∑ j : Option (Fin ℓ),
        weightEntry weights b i j *
          (-interpolationNormal (endpointGamma c e) b j Z *
            (interpolationPosition b i Z - interpolationPosition b j Z))) -
      c.zeta * (Z (0, 0) ^ 2 + Z (0, 1) ^ 2))

theorem lowerTable_eq {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint) :
    readMatrix (lowerTable c e) = lowerMatrix c e := by
  simp [lowerTable, read_tabulateMatrix, storageTable_eq,
    sparseQuadraticStorage_eq, weightData_eq, lowerMatrix]

@[noinline] def terminalSymmetryCheck {ℓ : ℕ} (c : RationalCase ℓ)
    (e : Endpoint) : Bool :=
  let data := storageTable c e
  decide (readMatrix data (Fin.last ℓ, 0) (Fin.last ℓ, 1) =
    readMatrix data (Fin.last ℓ, 1) (Fin.last ℓ, 0))

theorem storageTerminal_isSymm_of_check {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (h : terminalSymmetryCheck c e = true) : (storageTerminal c e).IsSymm := by
  have equality : readMatrix (storageTable c e) (Fin.last ℓ, 0) (Fin.last ℓ, 1) =
      readMatrix (storageTable c e) (Fin.last ℓ, 1) (Fin.last ℓ, 0) :=
    of_decide_eq_true h
  have offDiagonal : storageTerminal c e 0 1 = storageTerminal c e 1 0 := by
    simpa [storageTable_eq, storageMatrix] using equality
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact offDiagonal.symm
  · exact offDiagonal
  · rfl

structure LDLTable (k : ℕ) where
  lower : MatrixTable k
  pivot : PairTable k ℚ

@[noinline] def tabulateLDL {k : ℕ} (s : LDL k) : LDLTable k :=
  { lower := tabulateMatrix s.lower
    pivot := tabulatePair s.pivot }

def readLDL {k : ℕ} (s : LDLTable k) : LDL k :=
  { lower := readMatrix s.lower
    pivot := readPair s.pivot }

theorem read_tabulateLDL {k : ℕ} (s : LDL k) :
    readLDL (tabulateLDL s) = s := by
  cases s
  simp [readLDL, tabulateLDL, read_tabulateMatrix,
    funext (read_tabulatePair _)]

@[noinline] def ldlTableStep {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (s : LDLTable k) (i : Fin k × Fin 2) : LDLTable k :=
  tabulateLDL (ldlStep K (readLDL s) i)

theorem read_foldl_ldlTableStep {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (xs : List (Fin k × Fin 2)) (s : LDLTable k) :
    readLDL (xs.foldl (ldlTableStep K) s) =
      xs.foldl (ldlStep K) (readLDL s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
    simp [List.foldl_cons, ih, ldlTableStep, read_tabulateLDL]

@[noinline] def ldlTable {k : ℕ} (entries : MatrixTable k) :
    LDLTable k :=
  (coordinateList k).foldl (ldlTableStep (readMatrix entries))
    (tabulateLDL { lower := 0, pivot := 0 })


@[noinline] def pivotsCheck {k : ℕ} (threshold : ℚ)
    (entries : MatrixTable k) : Bool :=
  let state := ldlTable entries
  (List.finRange k).all fun i ↦ (List.finRange 2).all fun j ↦
    decide (threshold < readPair state.pivot (i, j))

theorem read_ldlTable {k : ℕ} (entries : MatrixTable k) :
    readLDL (ldlTable entries) = ldl (readMatrix entries) := by
  simp [ldlTable, read_foldl_ldlTableStep, read_tabulateLDL, ldl]

theorem pivotsCheck_iff {k : ℕ} (threshold : ℚ)
    (entries : MatrixTable k) :
    pivotsCheck threshold entries = true ↔
      PositivePivots threshold (readMatrix entries) := by
  rw [positivePivots_iff, ← read_ldlTable]
  simp [pivotsCheck, readLDL, List.all_eq_true, Prod.forall]

@[noinline] def constantModesCheck {k : ℕ} (entries : MatrixTable k) : Bool :=
  (List.finRange k).all fun i ↦ (List.finRange 2).all fun a ↦
    (List.finRange 2).all fun j ↦
      decide ((∑ t : Fin k, readMatrix entries (i, a) (t, j)) = 0)

theorem constantModesCheck_iff {k : ℕ} (entries : MatrixTable k) :
    constantModesCheck entries = true ↔
      readMatrix entries * constantModes k = 0 := by
  rw [← Matrix.ext_iff]
  simp [constantModesCheck, List.all_eq_true, Prod.forall,
    Matrix.mul_apply, Fintype.sum_prod_type, constantModes_apply]

theorem descent_constantModes_of_check {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (h : constantModesCheck (descentTable c e) = true) :
    descentMatrix c e * constantModes (ℓ + 2) = 0 := by
  simpa only [descentTable_eq] using
    (constantModesCheck_iff (descentTable c e)).mp h

theorem descent_positivePivots_of_check {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (threshold : ℚ) (h : pivotsCheck threshold (principalTable c e) = true) :
    PositivePivots threshold (descentPrincipal c e) := by
  simpa only [principalTable_eq] using
    (pivotsCheck_iff threshold (principalTable c e)).mp h

theorem lower_positivePivots_of_check {ℓ : ℕ} (c : RationalCase ℓ) (e : Endpoint)
    (threshold : ℚ) (h : pivotsCheck threshold (lowerTable c e) = true) :
    PositivePivots threshold (lowerMatrix c e) := by
  simpa only [lowerTable_eq] using
    (pivotsCheck_iff threshold (lowerTable c e)).mp h


end ADMM.FiniteMemory.Reconstruction.Computation
