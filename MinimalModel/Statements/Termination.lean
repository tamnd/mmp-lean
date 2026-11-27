/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import MinimalModel.Statements.BasicRelative
import MinimalModel.Statements.Boundedness
import MinimalModel.Statements.GeneralizedPairs

/-!
# Family C: termination and flips

The statements of family C of spec 06.2.2 that are planned at S0, S1 and S3, and the statements S49 and S50 of family F that S28 uses. The statement S27 uses the generalized pairs of `GeneralizedPairs.lean`. "Every program" is the form of each termination statement (spec 06.2.3): the statements say that no infinite sequence of steps exists, so they cover each choice of the extremal rays. S23 is about the programs with scaling only, as its source is, and it covers each choice of the rays in such a program.
-/

universe u

namespace MinimalModel

open AlgebraicGeometry CategoryTheory

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- S20, the termination conjecture `T(n)`. For each projective lc pair of dimension `n`, each sequence of `(K + Δ)`-flips is finite. This is open for `n ≥ 4`. -/
def Termination (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsLc A.P → ¬ HasInfiniteFlips A

/-- S22, a fresh claim (OpenAI 056, AxiomMath/MMP; spec 01.3). For each projective lc pair of dimension 4 with a rational boundary, each sequence of steps of the minimal model program is finite. The class is `claimed`: this statement is never a hypothesis of another proof (spec 06.6). -/
def TerminationLc4Rational : Prop :=
  ∀ A : PairModel k, A.X.dim = 4 → IsLc A.P → A.P.IsRationalBoundary → ¬ HasInfiniteProgram A

/-- S49, the ACC conjecture for minimal log discrepancies in dimension `n` (Shokurov; KM98 3.16 in spec 03). For each set `I ⊆ [0, 1]` that satisfies the DCC, the set of the mlds at the closed points of the lc pairs of dimension `n` with coefficients in `I` satisfies the ACC. -/
def ACCMld (n : ℕ) : Prop :=
  ∀ I : Set ℝ, I ⊆ Set.Icc 0 1 → I.IsWF →
    ∀ a : ℕ → ℝ, (∀ i, ∃ (X : NormalVariety k) (P : Pair X) (x : X.toScheme), X.dim = n ∧
      IsLc P ∧ P.Δ.CoeffsIn I ∧ IsClosed ({x} : Set X.toScheme) ∧ mld P x = (a i : WithBot ℝ)) →
    ¬ StrictMono a

/-- S50, the lower semicontinuity conjecture for minimal log discrepancies in dimension `n` (Ambro). For each lc pair of dimension `n` and each real `t`, the closed points `x` with `mld(x) > t` are the closed points of an open set. -/
def LSCMld (n : ℕ) : Prop :=
  ∀ (X : NormalVariety k) (P : Pair X), X.dim = n → IsLc P → ∀ t : ℝ,
    ∃ U : Set X.toScheme, IsOpen U ∧ ∀ x : X.toScheme, IsClosed ({x} : Set X.toScheme) →
      (x ∈ U ↔ (t : WithBot ℝ) < mld P x)

/-- S28, Shokurov's reduction (Shokurov 2004). The ACC and the lower semicontinuity of the minimal log discrepancies in dimension `n` give the termination of flips in dimension `n`. The `reader` role checks the class of pairs of the source (klt or lc) before F5. -/
def ShokurovReduction (n : ℕ) : Prop :=
  ACCMld k n → LSCMld k n → Termination k n

/-- S19, special termination (Fujino for dlt pairs; Lazić, Moraga and Tsakanikas for lc pairs). Assume `T(m)` for each `m < n`. Let `(X, Δ)` be a projective `ℚ`-factorial dlt pair of dimension `n`. Then each infinite sequence of steps from `(X, Δ)` is an isomorphism near `⌊Δ⌋` after finitely many steps: from some step on, the contraction and the small map of each step are isomorphisms over an open set of the base that contains the image of `⌊Δ⌋`. The class is reduction. The spec writes the hypothesis as `T(n - 1)`; this statement asks for termination in each dimension below `n`, as the proof uses it on the strata of `⌊Δ⌋`. The `reader` role checks this form against the source before F5. -/
def SpecialTermination (n : ℕ) : Prop :=
  (∀ m < n, Termination k m) →
    ∀ model : ℕ → PairModel k, (model 0).X.dim = n → IsQFactorial (model 0).X →
      IsDlt (model 0).P → (∀ i, IsMMPStep (model i) (model (i + 1))) →
      ∃ N : ℕ, ∀ i, N ≤ i →
        ∃ s : MMPStepData (model i) (model (i + 1)), s.IsIsoNear (model i).P.reducedSupp

/-- S21, the termination of flips for pseudo-effective lc 4-folds (Moraga; Chen and Tsakanikas). For each projective lc pair of dimension 4 such that `K + Δ` is pseudo-effective, each sequence of `(K + Δ)`-flips is finite. -/
def TerminationPseffLc4 : Prop :=
  ∀ A : PairModel k, A.X.dim = 4 → IsLc A.P → IsPseudoEffective A.P.KΔ → ¬ HasInfiniteFlips A

/-- S23, the termination of the program with scaling for a big boundary (BCHM Corollary 1.4.2, the absolute case). Let `(X, Δ)` be a projective `ℚ`-factorial klt pair with `Δ` big. Let `C ≥ 0` be a divisor such that `(X, Δ + C)` is klt and `K + Δ + C` is nef. Then each `(K + Δ)`-program with scaling of `C` is finite: no infinite sequence of steps with scaling starts at `(X, Δ)` and `C`. The divisor `C i` on the model `i` is the strict transform of `C`. This is about the programs with scaling only. BCHM say that they do not prove the termination of each program; that is S24 and S25 for a big boundary. -/
def TerminationScalingBig : Prop :=
  ∀ (model : ℕ → PairModel k) (C : ∀ i, Divisor ℝ (model i).X),
    IsQFactorial (model 0).X → IsKlt (model 0).P → IsBig (model 0).P.Δ → 0 ≤ C 0 →
    (∃ P' : Pair (model 0).X, P'.K = (model 0).P.K ∧ P'.Δ = (model 0).P.Δ + C 0 ∧ IsKlt P') →
    IsNef (model 0).I ((model 0).P.KΔ + C 0) →
    ¬ ∀ i, IsScalingStep (model i) (model (i + 1)) (C i) (C (i + 1))

/-- S24, a fresh claim (Han, Liu and Zhuang, arXiv:2509.01501; spec 01.3). For each projective klt pair of dimension at most 5 such that `Δ` is big or `K + Δ` is big, each sequence of steps of the minimal model program is finite. The class is `claimed`: this statement is never a hypothesis of another proof (spec 06.6). -/
def TerminationBigLe5 : Prop :=
  ∀ A : PairModel k, A.X.dim ≤ 5 → IsKlt A.P → (IsBig A.P.Δ ∨ IsBig A.P.KΔ) →
    ¬ HasInfiniteProgram A

/-- S25, a fresh claim (Hashizume, arXiv:2609.33679; claim C2 of spec 01.3). The statement of S24 in dimension `n`, with no bound on `n`: for each projective klt pair of dimension `n` such that `Δ` is big or `K + Δ` is big, each sequence of steps of the minimal model program is finite. The class is `claimed`: this statement is never a hypothesis of another proof (spec 06.6). -/
def TerminationBig (n : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = n → IsKlt A.P → (IsBig A.P.Δ ∨ IsBig A.P.KΔ) →
    ¬ HasInfiniteProgram A

/-- S26, the existence of lc flips (Birkar 2012; Hacon and Xu 2013). Let `(X, Δ)` be a projective lc pair, and let `f : X → Z` be a flipping contraction: a small contraction of relative Picard number one with `-(K + Δ)` ample over `Z`. Then the flip `g : X⁺ → Z` exists. This is S30 for lc pairs. -/
def LcFlips : Prop :=
  ∀ A : PairModel k, IsLc A.P → ∀ (Z : NormalVariety k) (f : A.X.toScheme ⟶ Z.toScheme),
    f ≫ Z.str = A.X.str → IsContraction f → IsSmallHom f → IsExtremalContraction A.I f →
    IsRAmpleOver (-A.P.KΔ) f →
    ∃ (B : PairModel k) (g : B.X.toScheme ⟶ Z.toScheme), g ≫ Z.str = B.X.str ∧
      IsContraction g ∧ IsSmallHom g ∧ IsRAmpleOver B.P.KΔ g ∧ IsStrictTransform A B f g

/-- S27, a fresh claim (Hu and Liu, arXiv:2603.03817, Theorem 1.1, with the base `U` a point). Let `(X, B, M)` be a projective lc generalized pair, and let `f : X → Z` be a flipping contraction: a small contraction of relative Picard number one with `-(K + B + M_X)` ample over `Z`. Then the flip `g : X⁺ → Z` exists: a small contraction from a generalized pair `(X⁺, B⁺, M)` with `K + B⁺ + M_{X⁺}` ample over `Z`, where `X ⇢ X⁺` is a birational map over `Z`, `B⁺` is the strict transform of `B`, and the nef part is the same b-divisor `M`. The class is `claimed`: this statement is never a hypothesis of another proof (spec 06.6). With `M = 0` this is S26. -/
def GeneralizedLcFlips : Prop :=
  ∀ (X : NormalVariety k) (I : IntersectionData X) (G : GenPair X), IsProjective X → IsGenLc G →
    ∀ (Z : NormalVariety k) (f : X.toScheme ⟶ Z.toScheme), f ≫ Z.str = X.str → IsContraction f →
    IsSmallHom f → IsExtremalContraction I f → IsRAmpleOver (-G.KBM) f →
    ∃ (X' : NormalVariety k) (G' : GenPair X') (g : X'.toScheme ⟶ Z.toScheme), g ≫ Z.str = X'.str ∧
      IsContraction g ∧ IsSmallHom g ∧ IsRAmpleOver G'.KBM g ∧
      ∃ σ : FF X' ≃ₐ[k] FF X, IsBirMapOver (X := X) (Y := X') f g σ ∧
        (∀ Q : PrimeDivisor X', ∃ P : PrimeDivisor X, SameDivisor σ P Q ∧ G'.B Q = G.B P) ∧
        SameBDivisor G.N G'.N σ

/-- The hypothesis (2) of Han and Liu, Theorem 1.1: each sequence of `ℚ`-factorial terminal flips in dimension `d` terminates. For each projective `ℚ`-factorial terminal pair of dimension `d`, each sequence of `(K + Δ)`-flips is finite. A flip keeps the source `ℚ`-factorial and terminal, so the hypothesis is asked of the first model. -/
def QFactorialTerminalTermination (d : ℕ) : Prop :=
  ∀ A : PairModel k, A.X.dim = d → IsQFactorial A.X → IsTerminal A.P → ¬ HasInfiniteFlips A

/-- S29, the reduction of Han and Liu (arXiv:2209.13122, Theorem 1.1). Let `d` be a positive integer. Assume the ACC for the global mlds of enc pairs of dimension `d` with coefficients in a finite set (`EncMldACC` of `Boundedness.lean`, which is Conjecture 1.9(2') of the source), and the termination of `ℚ`-factorial terminal flips in dimension `d`. Then each sequence of lc flips in each dimension `m ≤ d` terminates. Theorem 1.2 of the source is the case `d = 4`, where the second hypothesis is known. The flips of the source are not asked to be projective; this statement is about the projective pairs of `Termination`. The class is reduction. -/
def HanLiuReduction (d : ℕ) : Prop :=
  EncMldACC k d → QFactorialTerminalTermination k d → ∀ m ≤ d, Termination k m

end MinimalModel
