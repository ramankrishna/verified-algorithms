import bisect
import math
import random

import pytest

from verified_algorithms.classic import (euclid, fib_dp, insertion_sort, lower_bound,
                                         merge, merge_sort, pow_fast)

rng = random.Random(0)


def test_euclid_matches_math_gcd():
    for a in range(0, 120):
        for b in range(0, 120):
            assert euclid(a, b) == math.gcd(a, b)
    for _ in range(2000):
        a, b = rng.randrange(10**30), rng.randrange(10**30)
        assert euclid(a, b) == math.gcd(a, b)


def test_pow_fast_matches_builtin():
    for b in range(0, 12):
        for e in range(0, 70):
            assert pow_fast(b, e) == b ** e
    for _ in range(300):
        b, e = rng.randrange(10**6), rng.randrange(300)
        assert pow_fast(b, e) == b ** e


def test_fib_dp_matches_recurrence_and_closed_values():
    f = [0, 1]
    for i in range(2, 300):
        f.append(f[-1] + f[-2])
    assert [fib_dp(i) for i in range(300)] == f
    assert fib_dp(100) == 354224848179261915075


@pytest.mark.parametrize("sort", [insertion_sort, merge_sort])
def test_sorts_match_sorted(sort):
    for n in range(0, 9):
        for _ in range(60):
            xs = [rng.randrange(6) for _ in range(n)]  # many duplicates on purpose
            assert sort(xs) == sorted(xs)
    for _ in range(200):
        xs = [rng.randrange(10**9) for _ in range(rng.randrange(400))]
        assert sort(xs) == sorted(xs)


def test_merge_of_sorted_is_sorted_permutation():
    for _ in range(500):
        xs = sorted(rng.randrange(20) for _ in range(rng.randrange(15)))
        ys = sorted(rng.randrange(20) for _ in range(rng.randrange(15)))
        assert merge(xs, ys) == sorted(xs + ys)


def test_lower_bound_is_bisect_left():
    for _ in range(3000):
        a = sorted(rng.randrange(50) for _ in range(rng.randrange(40)))
        x = rng.randrange(-2, 53)
        assert lower_bound(lambda i: a[i] >= x, 0, len(a)) == bisect.bisect_left(a, x)


def test_lower_bound_spec_on_monotone_predicates():
    # exactly the Lean theorem: p false on [lo, r), true on [r, hi)
    for lo in range(0, 12):
        for hi in range(lo, 25):
            for t in range(lo - 2, hi + 3):
                p = lambda i, t=t: i >= t
                r = lower_bound(p, lo, hi)
                assert lo <= r <= hi
                assert all(not p(i) for i in range(lo, r))
                assert all(p(i) for i in range(r, hi))


def test_rejects_negative_inputs():
    with pytest.raises(ValueError):
        euclid(-1, 2)
    with pytest.raises(ValueError):
        pow_fast(2, -1)
    with pytest.raises(ValueError):
        fib_dp(-3)
