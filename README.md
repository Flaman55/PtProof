# PtProof: deterministic primality for PrimeAtlas pt1

Lean 4.35.0 + Mathlib v4.35.0. Author: Artur Flamandzki. License: Apache-2.0.

Paper: [`Latex/ptproof.pdf`](Latex/ptproof.pdf) (source `Latex/ptproof.tex`).

The pt1 engine sieves to a bound B and tests the survivors. This project replaces the
probabilistic BPSW test by the pseudosquares test and proves it correct
(`PtProof/PseudoSquares.lean`):

- `lpw_sorenson`: Lukes–Patterson–Williams with Sorenson's sieve bound (Sorenson 2006, Lemma 3.1);
- `prime_of_pss`: with s ≥ n^(1/4), not a square and not a cube ⇒ prime;
- `pss_complete`: the test never rejects a prime;
- `pssProve_sound`, `pssProve_complete`: the same for the C routine `pss_prove` as written
  (table from `engine_pt_pss.h`, return values 1 / 0 / -1).

The table of pseudosquares L_p (OEIS A002189) is an explicit assumption (`TableCorrect`). Its
transcription is checked by `decide`: three typos in the C table (p = 229, 353, 359), each
below the true value, so the table errs on the safe side. Correct values:
L_229 = 196640248121928601, L_353 = L_359 = 295363487400900310880401.

`measurements/`: pt1-pss vs BPSW benchmarks and the n−1 smooth-part study (`REPORT.md`, raw
rows in `results.tsv`). They are not part of the formal results. Rebuilding them needs the
PrimeAtlas engine (`prime_sieve/prime_sieve_engine_pt1.c`) and primesieve:

    export PRIMEATLAS_DIR=/path/to/primeAtlas
    export PSS_SIEVE=/path/to/pseudosquares_prime_sieve   # Walisch, for the comparison column
    gcc -O3 -march=native -I"$PRIMEATLAS_DIR/prime_sieve" measurements/pt1det_bench.c \
        -o measurements/pt1det_bench -lprimesieve -lpthread -lm

## Build

    lake exe cache get
    lake build
