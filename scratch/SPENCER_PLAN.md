# Plan: proving Komlos.spencer_six_deviations (the 6√n bound)

## The dead end (documented, don't repeat)

`partial_coloring_via_kleitman` (already Proved) bounds *each row separately* via a
union bound over all n rows using `HasSubgaussianMGF`/measure theory, giving a
per-row failure probability that forces ν ≳ √(log n) *in every round*, independent
of the active-set size. Iterating this geometrically (any schedule) therefore
costs a total of Θ(√(n log n)), never √n. This is not a bug in the schedule design
— it's inherent to bounding row-failure via `n · 2·exp(-ν²/2) < 1` (a per-round
constraint on the *full* row count n, not the shrinking active set). Confirmed
by direct calculation and by a concrete counterexample search (r even, r < 1/θ)
showing `Komlos.spencer_partial_coloring`'s own generic-θ interface has a genuine
parity/integrality obstruction when routed through the "difference of two
Hamming-far colorings" method. Also confirmed independently: web research on why
Spencer's proof avoids the O(√(n log n)) floor that "all partial-coloring methods"
otherwise pay (only Banaszczyk's separate geometric method was believed log-free —
this sent me looking for what actually makes Spencer's original method log-free).

## The real mechanism (Rothvoss's Lemma 8/9, matching Spencer 1985 exactly when m=n)

Source: math.mit.edu/classes/18.095/lect6/notes.pdf (Rothvoss, "Discrepancy Theory").
Saved locally: /tmp/.../scratchpad/rothvoss.txt (already pdftotext'd).

Key structural difference from the dead end: bound the **row failures jointly via
entropy subadditivity**, not via a probability union bound. This is the actual
reason no log(n) tax is paid:

1. For a uniform random ±1 coloring χ of an m-element active set, and each row
   (set) S_i with 0/1 coefficients, define the *quantized* row-sum
   `Z_i(χ) := ⌊χ(S_i) / (2Δ_i)⌋ ∈ ℤ` for a threshold `Δ_i = λ_i·√m`.
2. **Lemma 9 (the new lemma to build):** `H(Z_i) ≤ G(λ_i)` where
   `G(λ) := 10·e^{-λ²/10}` for `λ ≥ 2` (and a log-based bound for `λ < 2`, we won't
   need that branch). Proved via: `H(Z_i) = H((X_j)_j)` where `X_j := 1[Z_i = j]`,
   subadditivity `H((X_j)_j) ≤ Σ_j H(X_j)`, and bounding each `H(X_j)` via
   `H(p) ≤ 2p·log(1/p)` for small p, combined with a Chernoff/subgaussian tail bound
   on `Pr[X_j = 1]` (this tail bound is exactly the same kind of estimate already
   built in `row_tail_bound` / `HasSubgaussianMGF` machinery from
   `Sol_Komlos_partial_coloring_via_kleitman.lean` and `Sol_Komlos_spencer_random_finish.lean`
   — reusable, just needs bridging from MeasureTheory.Measure to the counting-based
   `empiricalProb`/`shannonEntropy` framework, exactly as `TMeasure_real_coe_finset`
   already bridges these two worlds).
3. **Joint bound via subadditivity over ALL m=n rows simultaneously** (not a
   union bound!): `H(Z) ≤ Σ_i H(Z_i) ≤ Σ_i G(λ_i)`, using the ALREADY-PROVEN
   `shannonEntropy_pi_le` (theorem_id 7c9a1a4b-e45d-4824-9b06-1d262d0c94c3, Proved).
   Choosing λ_i so `Σ_i G(λ_i) ≤ m/10` (a budget on the ACTIVE set size m, not on n)
   is what lets λ_i stay a FIXED CONSTANT independent of n — this is the crux of
   why the log(n) factor disappears. (Compare: the dead-end approach effectively
   needed budget ~1/n per row since it summed failure PROBABILITIES, not entropies;
   entropy subadditivity spreads a budget of m/10 ADDITIVELY across m~n terms,
   giving each one a CONSTANT (not 1/n) share.)
4. **Pigeonhole** (ALREADY PROVEN: `shannonEntropy_pigeonhole`,
   theorem_id 3b07a0c9-deb1-4361-84bb-db70fdc56660): since `H(Z) ≤ m/10`, some
   specific joint bucket-value b has `|{χ : Z(χ)=b}| ≥ 2^m · 2^{-m/10} = 2^{0.9m}`.
5. **Kleitman** (ALREADY PROVEN — our own `kleitman_diameter`/Katona apparatus,
   or a fixed-fraction restatement of it): any subset of `{0,1}^m` of size `≥2^{0.9m}`
   contains two points x,y at Hamming/L1 distance `≥ m/10`.
6. Take χ_A, χ_B mapping to the SAME b with Hamming distance ≥ m/10. Since both
   land in the same quantization bucket for EVERY row i (⌊χ_A(S_i)/2Δ_i⌋ =
   ⌊χ_B(S_i)/2Δ_i⌋ = b_i), their difference χ := (χ_A - χ_B)/2 satisfies
   `|χ(S_i)| ≤ Δ_i` for every row, AND has `≥ m/10` nonzero (newly colored) entries
   (from the Hamming distance). This is Lemma 8's conclusion, matching the SHAPE
   of `Komlos.spencer_partial_coloring`'s conclusion but via a fixed 1/10 fraction,
   not an arbitrary θ (no parity obstruction — we pick the fraction ourselves).
7. **Iteration**: start m_0 = n, color ≥1/10 each round (m_{k+1} ≤ 0.9·m_k), so
   m_k = n·0.9^k. Each round's Δ needs `λ_i ~ const` (from step 3, using budget
   m_k/10 spread across the SAME n rows — wait, careful: this needs checking
   whether the "n" in step-3's subadditivity sum is the ORIGINAL total row count
   (always n, unchanging) or the current active size. Rothvoss's own worked
   calculation (already transcribed in rothvoss.txt around "Proof of Spencer's
   Thm") uses `Δ := C·sqrt(active_size · log(2m/active_size))` per round, with
   `m` = TOTAL rows (fixed = n throughout), giving a term that GROWS slowly
   (log(2n/m_k) grows linearly in k since m_k decays geometrically) but is
   DOMINATED by the geometric √(m_k) decay, so
   `Σ_k sqrt(m_k · log(2n/m_k)) = O(sqrt(n · log(2n/n))) = O(sqrt(n))`
   when m_0 = n (Spencer's exact setting, log(2n/n)=log 2, a CONSTANT). This
   is the exact resolution of why the total stays O(√n) despite each round
   individually needing a slowly-growing λ_k. MUST re-verify this telescoping
   sum rigorously in Lean (it's a finite geometric-ish series bound, should be
   tractable via `Finset.sum` + comparison to a geometric series, but needs care).
8. Assemble to hit the literal constant 6 (Spencer's own tight constant), or
   failing that, prove a clean O(√n) bound and document the achieved constant
   honestly if 6 exactly proves too delicate to match without the original
   paper's precise numerics.

## What's already built and reusable (all Proved on the platform)

- `shannonEntropy_pigeonhole` (3b07a0c9-deb1-4361-84bb-db70fdc56660)
- `shannonEntropy_prod_le` (47c26647-3202-42bf-88fc-fd3223961afc)
- `shannonEntropy_pi_le` (7c9a1a4b-e45d-4824-9b06-1d262d0c94c3) — the m-way subadditivity, EXACTLY what step 3 needs
- `gibbs_inequality` (1c44dd3d-300b-4471-91c4-534aa3d35695)
- `choose_sum_le_exp_mul_binEntropy` (c5bd7e35-04b8-4e26-b1f6-36603f94075a)
- `binEntropy_le_log_two_sub_sq` (scratch/BinEntropyPinsker.lean, local only, not yet submitted — reusable Pinsker-type bound, may help bound G(λ) or the entropy-of-a-skewed-binary-variable estimate in Lemma 9)
- `Katona.katona`, `Katona.katona_union`, `kleitman_diameter` (all Proved) — for step 5
- `Komlos.spencer_random_finish` (Proved, by another contributor) — NOT needed for this
  route (it was for the dead-end schedule), but still useful as the eventual
  cleanup for whatever tiny residual set remains after the geometric iteration
  bottoms out (m_K = O(1) or below a threshold where a direct random coloring
  is cheap).
- `Sol_Komlos_partial_coloring_via_kleitman.lean`'s subgaussian tail-bound
  machinery (`row_tail_bound`, `TMeasure_real_coe_finset`, etc.) — reusable
  template for Lemma 9's Chernoff step, bridging MeasureTheory.Measure and the
  counting-based `empiricalProb`/`shannonEntropy` framework.

## IMPORTANT CORRECTION (found and fixed this session)

The original `shellIdx := ⌊rowSumB/(2Δ)⌋` (floor) convention was WRONG: it makes
shells `{-1,0}` both "central" (straddling 0, neither has a useful tail bound).
By the symmetry `χ ↦ ¬χ` (flip all signs), which sends `shellIdx j ↦ -j-1`
combinatorially, this forces `p_{-1} = p_0` exactly, and together they'd
contribute close to 1 bit of entropy REGARDLESS of λ (does not shrink as λ
grows). Since this cost is paid by EVERY one of the n rows, summing it via
`shannonEntropy_pi_le` would need a budget of ~n bits just for this — but the
budget is `m_k/10`, which for `m_k ≪ n` (later iteration rounds) would be
violated. This would have silently sunk the whole approach if not caught.

**Fix**: switched `shellIdx` to `round(rowSumB/(2Δ))` (nearest integer, via
Mathlib's `round`/`abs_sub_round`), giving a SINGLE symmetric central bucket
(`shellIdx=0 ↔ |rowSumB|≤Δ`) whose probability `p_0 → 1` as λ grows, so its
entropy contribution `(1-p_0)/log2 → 0` as required. Already reflected in
`scratch/SpencerEntropyLemma.lean` (shellIdx_dist, shellIdx_bound,
shellIdx_prob_le — the floor-era shellIdx_ge/lt and the pos/neg split are gone,
replaced by one unified lemma using `|j|`).

## The full entropy-sum derivation (worked by hand, ready to formalize)

Target: `shannonEntropy (shellFin Δ a) ≤ (12/log 2)·exp(-λ²/4)` for `Δ=λ√m`, `λ≥2`
(a clean, self-derived bound — constants are NOT tight, just correct and simple).

Write `p_j := Pr[shellIdx = j]` (`= empiricalProb` after the `shellFin` reindex),
`f(p) := if p=0 then 0 else p·logb 2 (1/p)`, so `H(Z) = Σ_j f(p_j)` (sum over the
bounded integer range from `shellIdx_bound`).

1. **Central term** (`j=0`): `f(p_0) = negMulLog(p_0)/log 2 ≤ (1-p_0)/log 2` via
   the EXISTING Mathlib lemma `Real.negMulLog_le_one_sub_self` (already found
   and used conceptually for `partial_coloring_via_kleitman`'s cousin bounds).
   And `1-p_0 = Σ_{j≠0} p_j` (probabilities sum to 1).
2. **Peripheral terms** (`j≠0`): via `shellIdx_prob_le`, `p_j ≤ q_j :=
   2·exp(-λ²(2|j|-1)²/2)`. Since `q_j ≤ 1/e` even at the worst case `λ=2,|j|=1`
   (`2e^{-2} ≈ 0.271 < 1/e ≈ 0.368` — CHECK THIS ARITHMETIC CAREFULLY when
   formalizing, it's a real numeric inequality, not just "obviously small"),
   `x·logb2(1/x)` is increasing on `(0,1/e)`, so `f(p_j) ≤ f(q_j)`. Direct
   computation: `f(q_j) = q_j·(-1 + λ²(2|j|-1)²/(2·log 2)) ≤ q_j·λ²(2|j|-1)²/(2 log 2)`
   (drop the `-q_j` term, valid since `q_j>0`).
3. Combine: `H(Z) ≤ Σ_{j≠0} p_j/log2 + Σ_{j≠0} f(p_j) ≤ Σ_{j≠0} q_j/log2 · (1 + λ²(2|j|-1)²/2)`
   roughly — fold into `H(Z) ≤ (2/log2)·Σ_{j≠0} q_j·(1+λ²(2|j|-1)²)` (absorbing
   constants generously; redo the exact bookkeeping when formalizing rather than
   trusting this paraphrase literally).
4. Reindex `Σ_{j≠0} = 2·Σ_{k=1}^{m+1}` (j and -j give the same `|j|=k`, using the
   SAME symmetry fact noted above — this time as a genuine finite-sum reindexing
   via `Finset.sum_nbij'` or similar, not just a probability identity).
5. Bound `(1+λ²r_k)·e^{-λ²r_k/2} ≤ 2·e^{-λ²r_k/4}` where `r_k:=(2k-1)²`, via the
   UNIVERSAL fact `(1+X)e^{-X/4} ≤ 2` for all `X≥0` (max at `X=3`, value
   `4e^{-3/4}≈1.89<2` — an elementary one-variable calculus fact; in Lean, easiest
   via `Real.add_one_le_exp` applied cleverly, OR by bounding `(1+X) ≤ exp(X/4)·2`
   directly using `Real.add_one_le_exp (X/4) : 1+X/4 ≤ exp(X/4)`, so
   `(1+X) ≤ 1 + 4·(X/4) ≤ 4·(1+X/4) ≤ 4·exp(X/4)` when `X/4≥... ` — REDERIVE
   CAREFULLY when formalizing; the max-at-X=3 approach needs calculus machinery
   (`IsLocalMax`/derivative) unless a cruder elementary bound suffices instead,
   e.g. splitting into `X≤3` (where `1+X≤4` trivially, so `(1+X)e^{-X/4}≤4`) and
   `X>3` (where a direct exponential comparison closes it) — a case-split avoiding
   calculus may be more Lean-friendly than the true optimum-point argument).
6. `(2k-1)² ≥ 4k-3` for all `k≥1` (equality at `k=1`; elementary: `(2k-1)²-(4k-3)
   = 4(k-1)² ≥ 0`), so `Σ_{k≥1} e^{-λ²r_k/4} ≤ e^{3λ²/4}·Σ_{k≥1}e^{-λ²k} =
   e^{3λ²/4}·e^{-λ²}/(1-e^{-λ²})` (finite geometric series, `Finset.geom_sum_eq`
   or a direct comparison bound suffices since we only need an upper bound, not
   exact value). For `λ≥2`: `e^{3λ²/4}e^{-λ²}=e^{-λ²/4}` and
   `1/(1-e^{-λ²})≤1/(1-e^{-4})≤1.02`.
7. Assemble: `Σ_{k≥1}(1+λ²r_k)e^{-λ²r_k/2} ≤ 2·1.02·e^{-λ²/4} ≤ 3e^{-λ²/4}`, giving
   the final `H(Z) ≤ (2/log2)·2·3·e^{-λ²/4} = (12/log2)e^{-λ²/4}`.

**Formalization order suggestion**: prove step 5's elementary bound first (fully
self-contained, no other dependencies), then step 6's geometric-series bound
(also self-contained), then assemble the per-shell bound from `shellIdx_prob_le`
(step 2, needs the `x logb2(1/x)` monotonicity fact — check Mathlib for
`Real.negMulLog` monotonicity on an interval, or derive via `strictMonoOn` from
its derivative, similar to how `strictConcave_binEntropy` was derived), then do
the finite-sum reindexing (step 4, `Finset.sum_nbij'`, same pattern used
repeatedly in the Katona/Kleitman work), then combine everything (steps 1,3,7).

## Current state of scratch/SpencerEntropyLemma.lean (compiles clean, no sorries)

- `RSign`, `rowSumB`: the ±1 coloring and 0/1-weighted row sum on `Fin m → Bool`.
- `uMeasure`, `uMeasure_real_coe_finset`: uniform measure on `Fin m → Bool` bridged
  to plain Finset-counting (`(uMeasure m).real S = S.card / 2^m`) — the bridge
  between the counting-based `shannonEntropy`/`empiricalProb` framework and the
  measure-theoretic `HasSubgaussianMGF` framework.
- `rowSumB_subgaussian`, `rowSumB_tail_bound`: the full Chernoff chain, giving
  `(uMeasure m).real {ω | t ≤ |rowSumB a ω|} ≤ 2·exp(-t²/(2m))`.
- `shellIdx := round(rowSumB/(2Δ))`, `shellIdx_dist`, `shellIdx_bound`: the
  CORRECTED (round-based, single-central-bucket) quantization — see the
  correction section above.
- `shellFin`, `shellIdx_shift_range`, `shellFin_eq_toNat`, `shellFin_eq_iff`,
  `empiricalProb_shellFin`: the Fintype-codomain (`Fin (2m+3)`) version via a
  shift, with the bridge from `empiricalProb (shellFin Δ a) k` to plain
  Finset-counting on `shellIdx`.
- `shellIdx_prob_le`: the single unified per-shell Chernoff tail bound for `j≠0`,
  `p_j ≤ 2·exp(-Δ²(2|j|-1)²/(2m))`.

## Remaining work on Lemma 9 itself (not yet started — see the full hand-derived
proof above under "The full entropy-sum derivation")

This is the hardest remaining piece — genuinely comparable to the hardest single
lemmas from the Katona/Kleitman project, and now has a complete, checked-by-hand
proof sketch with concrete constants (see above), ready to formalize
step-by-step. Everything built so far (the measure bridge, the Chernoff chain,
the shell-index bookkeeping) is exactly the infrastructure this needs; no more
new "supporting" lemmas should be needed before tackling the sum itself
directly.

## Immediate next step: the entropy-of-a-shell-index bound

Rather than reproducing Rothvoss's exact two-case `G(λ)` formula (which needs
`log(10/λ)` for `λ<2`, not needed here since we only ever use `λ≥2`), derive our
OWN clean sufficient bound — we don't need to match his constants, just need
SOME workable one (same philosophy as `binEntropy_le_log_two_sub_sq` and
`partial_coloring_via_kleitman`: independently-derived is fine).

**Target**: for `Δ = λ√m`, `λ ≥ 2`: `shannonEntropy (shellFin Δ a) ≤ C·λ²·exp(-2λ²)`
for an absolute constant C (or any similarly-shaped bound where the RHS depends
only on λ, not on m — that's the property that actually matters for the later
steps, since it lets λ be chosen as a fixed constant per round rather than
growing with m or n).

**Proof plan** (worked by hand, not yet formalized):
`H(Z) = Σ_j p_j·log(1/p_j)` where `p_j := Pr[Z=j]`. Split into `j=0` and `j≠0`.
- For `j ≠ 0`: `Z=j` (j≥1, say) implies `rowSumB ≥ 2jΔ`, so via
  `rowSumB_tail_bound`, `p_j ≤ 2·exp(-2j²λ²)` (using `(2jΔ)²/(2m) = 2j²Δ²/m = 2j²λ²`
  since `Δ=λ√m`). Symmetric for `j ≤ -1` via `-rowSumB`.
- Since `p_j` is tiny for `λ≥2`, use `x·log(1/x)` increasing on `(0,1/e)` to bound
  `p_j·log(1/p_j) ≤ 2exp(-2j²λ²)·(2j²λ² + log(1/2))`, then sum over `j≠0`: the
  series is dominated by `j=±1` (Gaussian-tail-style decay in `j²`), giving a total
  of order `λ²·exp(-2λ²)` (times an absolute constant from the geometric tail).
- For `j=0`: `p_0 = 1 - Σ_{j≠0}p_j ≥ 1-ε` where `ε` is the tail mass just bounded.
  Use `x·log(1/x) ≤ 2(1-x)` for `x ∈ [1/2,1]` (elementary, provable the same way
  as the `1-log(1+y)≤y`-style bound used in `partial_coloring_via_kleitman`, or
  via `Real.log_le_sub_one_of_pos` applied to `1/x`) to get `p_0·log(1/p_0) ≤ 2ε`.
- Total: `H(Z) ≤ (tail sum bound) + 2ε = O(λ²·exp(-2λ²))`.

This is a real, self-contained analytic proof (bounded-but-many-term sum with
exponential decay, elementary log inequalities) — estimate 150-300 lines, on par
with the hardest single lemmas from the Katona/Kleitman project. Next concrete
step: define `shellFin` (the Fintype-codomain version of `shellIdx`, via a shift
into `Fin (2m+3)`, using `hΔpos : (1:ℝ)/2 ≤ Δ` to keep the bound uniform), then
attack the sum above, testing incrementally.

## After that: assembling the rest

1. Apply `shannonEntropy_pi_le` across all `n` rows simultaneously (this is where
   the "no log(n) factor" property actually kicks in — see the main writeup above).
2. `shannonEntropy_pigeonhole` to find a bucket `b` with `≥ 2^{0.9m}`-many colorings
   (choosing `λ` so `n · C·λ²·exp(-2λ²) ≤ m/10`; note `λ` here does NOT need to grow
   with `n` in the way the dead-end approach required, because this budget is
   compared against `m/10`, i.e. it's about how many bits of entropy `n` roughly-
   independent constant-entropy terms contribute, not about making a single
   probability tinier than `1/n`).
3. Kleitman (`kleitman_diameter`/Katona apparatus, already proven) with a FIXED
   fraction `0.9`/`0.1` split (simpler than the general-θ case, no parity issue
   since we pick the fraction) to get two colorings at Hamming distance `≥ m/10`.
4. Difference of the two colorings gives the partial-coloring step (Rothvoss
   Lemma 8's conclusion): `≥ m/10` newly colored, row bound `≤ Δ_i` per row.
5. Iterate: `m_{k} = n·0.9^k`, each round needs its own `λ_k` satisfying step 2's
   budget with the CURRENT `m_k` (this is where `λ_k` grows slowly with `k`, since
   `log(2n/m_k)` grows linearly in `k` while `m_k` itself decays geometrically —
   Rothvoss's own worked calculation, transcribed in
   `/tmp/.../scratchpad/rothvoss.txt` under "Proof of Spencer's Thm", shows the
   SERIES `Σ_k sqrt(m_k·log(2n/m_k))` telescopes to `O(sqrt(n·log(2n/n))) = O(sqrt(n))`
   when `m_0 = n` (our exact setting) — dominated by the `k=0` term since the
   exponential decay of `sqrt(m_k)` beats the linear growth of the log term).
6. Stop once `m_K` is small enough that `spencer_random_finish`'s bound
   `sqrt(2·m_K·log(4n))` is a negligible addition, sum everything, and verify the
   total stays under `6√n` (or report the honestly-achieved constant if 6 exactly
   proves too delicate without Spencer's original paper's precise schedule).
