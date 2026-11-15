"""pt1 deterministic research runs. python3 run_bench.py <step> ...
Appends one TSV row per run to results.tsv:
item floor numbers windows engine B n_bases seconds n_per_s maxrss_MB primes notes
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.environ.get("PRIMEATLAS_DIR", "")   # PrimeAtlas checkout, see README
SIEVE = os.path.join(REPO, "prime_sieve")
BENCH = os.path.join(HERE, "pt1det_bench")
KIM = os.environ.get("PSS_SIEVE", "")   # Walisch's pseudosquares_prime_sieve binary
OUT = os.path.join(HERE, "results.tsv")
W = 10 ** 7


V72_MAX_FLOOR = 30   # above it v7.2 is too slow to matter (Artur)


def done(item, floor, numbers, engine, b=None):
    """True when results.tsv already holds this run (restarts skip it)."""
    if not os.path.exists(OUT):
        return False
    for line in open(OUT):
        f = line.rstrip("\n").split("\t")
        if len(f) > 5 and f[:3] == [str(item), str(floor), f"{numbers:.0e}"] and f[4] == engine \
                and (b is None or f[5] == str(b)):
            return True
    return False


def row(item, floor, numbers, engine, b, n_bases, secs, rss, primes, notes=""):
    nps = numbers / secs if secs else 0
    line = "\t".join(str(x) for x in (item, floor, f"{numbers:.0e}", numbers // W, engine, b, n_bases,
                                      f"{secs:.2f}", f"{nps / 1e6:.2f}M", rss, primes, notes))
    with open(OUT, "a") as f:
        f.write(line + "\n")
    print(line, flush=True)


def timed(cmd, env=None):
    t = time.perf_counter()
    p = subprocess.run(["/usr/bin/time", "-f", "RSS %M"] + cmd, capture_output=True, text=True,
                       env=env)
    secs = time.perf_counter() - t
    rss = int(p.stderr.strip().splitlines()[-1].split()[1]) // 1024
    return p, secs, rss


def pt1(item, floor, numbers, mode, b=0, notes=""):
    if done(item, floor, numbers, f"pt1-{mode}", b if item == 2 else None):
        return None
    p, _, _ = timed([BENCH, str(floor), f"{numbers:.0e}", str(b), mode, "24"])
    f = p.stdout.split()
    if len(f) < 6 or f[5] == "nobases":
        row(item, floor, numbers, f"pt1-{mode}", f[2] if len(f) > 2 else b, 0, 0, 0, 0,
            "no bases: top/B >= L_373 " + notes)
        return None
    _, _, bb, _, nb, secs, primes, rss, sq_ns = f[:9]
    secs, primes = float(secs), int(primes)
    if mode == "pss":
        share = primes * float(sq_ns) * 1e-9 / (24 * secs) * 100
        notes = f"sq+cube {sq_ns} ns/call, ~{share:.2f}% of thread time " + notes
    row(item, floor, numbers, f"pt1-{mode}", bb, nb, secs, rss, primes, notes)
    return secs, primes


def kim(item, floor, numbers):
    if done(item, floor, numbers, "pss-count(Kim)"):
        return
    lo = 10 ** floor
    p, secs, rss = timed([KIM, str(lo), str(lo + numbers - 1), "--threads=24"])
    primes = next(int(l.split()[1]) for l in p.stdout.splitlines() if l.startswith("Primes:"))
    own = next(float(l.split()[1]) for l in p.stdout.splitlines() if l.startswith("Seconds:"))
    lp = next((l.split()[1] for l in p.stdout.splitlines() if l.startswith("p:")), "?")
    row(item, floor, numbers, "pss-count(Kim)", "-", f"p={lp}", own, rss, primes,
        f"wall {secs:.1f}s")


def v72(item, floor, numbers):
    if floor > V72_MAX_FLOOR or done(item, floor, numbers, "v7.2"):
        return
    portal = tempfile.mkdtemp(prefix="v72_", dir="/tmp")
    try:
        env = dict(os.environ, CONSTELLATION_PORTAL_DIR=portal)
        n = numbers // W
        p, secs, rss = timed(["python3", os.path.join(SIEVE, "prime_sieve_v7_2.py"), str(floor), "0",
                              str(n - 1), "24", "2", "0", "0", str(W)], env=env)
        with open(os.path.join(portal, "last_scan_metrics.json")) as f:
            m = json.load(f)
        row(item, floor, numbers, "v7.2", "-", "-", m["sieve_seconds"], rss,
            m["total_primes_found"], f"wall {secs:.1f}s base_gen {m.get('base_gen_seconds', 0):.1f}s")
    finally:
        shutil.rmtree(portal, ignore_errors=True)


def item1():
    for numbers in (10 ** 9, 10 ** 10):
        for floor in (25, 26, 28, 30, 32):
            pt1(1, floor, numbers, "pss")
            pt1(1, floor, numbers, "bpsw")
            pt1(1, floor, numbers, "none", notes="primes column = survivors")
            kim(1, floor, numbers)
            v72(1, floor, numbers)


def item2():
    for floor in (28, 30, 32, 33, 34, 35):
        b0 = int(10 ** (floor / 4))
        b = b0
        while True:
            pt1(2, floor, 10 ** 9, "pss", b, notes=f"B = default x{b // b0}")
            if b >= 2 ** 32 - 1:
                break
            b = min(b * 4, 2 ** 32 - 1)


def item3():
    for floor in (25, 28, 30, 32):
        b = int(10 ** (floor / 4))
        p = subprocess.run([os.path.join(HERE, "nminus1"), str(floor), "1e7", str(b)],
                           capture_output=True, text=True)
        line = "3\t" + "\t".join(p.stdout.split()) + \
            "\t(floor count B primes F>=n^1/2 F>=n^1/3 median_logF/logn secs)"
        with open(OUT, "a") as f:
            f.write(line + "\n")
        print(line, flush=True)


def item4():
    for floor in (28, 29, 30):
        v72(4, floor, 10 ** 11)


if __name__ == "__main__":
    for step in sys.argv[1:]:
        {"1": item1, "2": item2, "3": item3, "4": item4}[step]()
    print("DONE", flush=True)
