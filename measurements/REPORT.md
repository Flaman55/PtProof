# pt1 deterministic — measurement report

Machine: AMD Ryzen 9 5900X 12C/24T, 54 GB, WSL2. Code: PrimeAtlas commit
[9afe9c6](https://github.com/Flaman55/primeAtlas/commit/9afe9c6) (now in `main`; base d722e09). 24 threads, window 1e7. Raw rows: results.tsv.

**Prime counts agree on every row** (pt1-pss = pt1-bpsw = Kim = v7.2 for each floor/size). No mismatch.

## 1. Engines (Mn/s, sieve seconds)

| floor | numbers | pt1-pss | pt1-bpsw | pt1-none (survivors) | Kim pss | v7.2 | n_bases | primes |
|---|---|---|---|---|---|---|---|---|
| 25 | 1e9 | 20.7 | 157.9 | 2053 | 28.6 | 82.6 | 54 | 17376254 |
| 26 | 1e9 | 17.9 | 151.9 | 2151 | 25.4 | 37.7 | 59 | 16705096 |
| 28 | 1e9 | 17.0 | 155.1 | 2237 | 22.5 | 7.3 | 64 | 15514691 |
| 30 | 1e9 | 15.6 | 153.9 | 2183 | 19.4 | 1.34 | 68 | 14473890 |
| 32 | 1e9 | 14.3 | 143.8 | 1502 | 17.8 | — | 73 | 13573489 |
| 25 | 1e10 | 21.0 | 158.0 | 2268 | 29.4 | 470.9 | 54 | 173728551 |
| 26 | 1e10 | 17.9 | 151.8 | 2599 | 25.5 | 266.5 | 59 | 167026529 |
| 28 | 1e10 | 16.8 | 155.7 | 2495 | 22.6 | 66.2 | 64 | 155111392 |
| 30 | 1e10 | 15.4 | 152.5 | 2748 | 19.2 | 12.9 | 68 | 144758509 |
| 32 | 1e10 | 14.4 | 149.1 | 1868 | 17.2 | — | 73 | 135707959 |

- Proof costs ~9x BPSW; it is the whole cost of pt1-pss (sieve ~0.5%).
- Square+cube check: 93–100 ns/call, 0.07–0.15% of thread time — negligible.
- pt1-pss RAM 150–170 MB; Kim 0.7–2.2 GB; v7.2 1.4–8.2 GB.
- Kim is ~1.2–1.4x faster than pt1-pss on the same proof.

## 2. B sweep at 1e9 (pt1-pss)

| floor | default B | best Mn/s (B) | default Mn/s | works from B | RAM at 2^32 |
|---|---|---|---|---|---|
| 28 | 1.0e7 | 18.05 (2.56e9) | 14.1 | default | 923 MB |
| 30 | 3.2e7 | 15.5 (5.1e8) | 14.2 | default | 923 MB |
| 32 | 1.0e8 | 14.3 (4.0e8) | 13.8 | default | 922 MB |
| 33 | 1.8e8 | 15.1 (7.1e8) | no bases | 7.1e8 | 922 MB |
| 34 | 3.2e8 | 13.0 (2^32) | no bases | 2^32 only | 923 MB |
| 35 | 5.6e8 | — | no bases | **never** (table to L_373 too short) | — |

Larger B gains at most ~25% (f28), elsewhere within noise. f35 needs a longer pseudosquares table
or another proof.

## 3. n−1 smooth part (Pocklington route), 1e7 numbers per floor

| floor | B | F ≥ n^1/2 | F ≥ n^1/3 | median log F / log n |
|---|---|---|---|---|
| 25 | 1.8e6 | 10.5% | 29.7% | 0.235 |
| 28 | 1.0e7 | 10.3% | 29.4% | 0.232 |
| 30 | 3.2e7 | 10.3% | 29.2% | 0.232 |
| 32 | 1.0e8 | 10.2% | 29.2% | 0.231 |

Only ~10% of primes are cheaply provable by n−1 alone; not a general replacement.

## 4. v7.2 wide runs vs pt1-pss

| floor | v7.2 1e9 | v7.2 1e10 | v7.2 1e11 (RAM) | pt1-pss | crossover (v7.2 faster above) |
|---|---|---|---|---|---|
| 25 | 82.6 | 470.9 | — | 21.0 | ~2.5e8 |
| 26 | 37.7 | 266.5 | — | 17.9 | ~5e8 |
| 28 | 7.3 | 66.2 | 373.7 (11.1 GB) | 16.8 | ~2.4e9 |
| 29 | — | — | 209.3 (11.1 GB) | ~16 | ~5e9 (consistent with pt1.1 note) |
| 30 | 1.34 | 12.9 | 94.5 (11.2 GB) | 15.4 | ~1.2e10 |

Crossovers interpolated log-linearly (v7.2 n/s grows ~linearly with size in this range).

## Conclusions

- Deterministic pt1 (pss) is correct and stable up to f34 (f33 needs B ≥ 7.1e8, f34 B = 2^32),
  at ~13–21 Mn/s — about 9–11x slower than BPSW pt1.
- For ranges above the crossover, v7.2 is the faster deterministic verifier through f30;
  above f30, pt1.1 / pt1-pss is the only option (Artur's decision), now proven to f34.
- Speed of pt1-pss at f35 would require extending the pseudosquares table beyond L_373.
