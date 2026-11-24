"""Classic algorithms. Each function mirrors the Lean definition of the same name, so the
Lean correctness theorem is a statement about exactly this procedure."""
from __future__ import annotations

from typing import Callable, Sequence


def euclid(a: int, b: int) -> int:
    """gcd(a, b) by Euclid: gcd(a, 0) = a, gcd(a, b) = gcd(b, a mod b). O(log min(a, b)) steps."""
    if a < 0 or b < 0:
        raise ValueError("natural numbers only")
    while b != 0:
        a, b = b, a % b
    return a


def pow_fast(b: int, e: int) -> int:
    """b ** e by repeated squaring, written recursively to match the Lean `powFast`."""
    if b < 0 or e < 0:
        raise ValueError("natural numbers only")
    if e == 0:
        return 1
    half = pow_fast(b, e // 2)
    return half * half if e % 2 == 0 else half * half * b


def fib_dp(n: int) -> int:
    """F(n) in O(n) by carrying the pair (F(k), F(k+1))."""
    if n < 0:
        raise ValueError("natural numbers only")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def insert_sorted(x: int, ys: list[int]) -> list[int]:
    """Insert x before the first element it is <= to (the Lean `insertSorted`)."""
    for i, y in enumerate(ys):
        if x <= y:
            return ys[:i] + [x] + ys[i:]
    return ys + [x]


def insertion_sort(xs: Sequence[int]) -> list[int]:
    """Insertion sort, processing the list from the back like the Lean `insSort`."""
    out: list[int] = []
    for x in reversed(xs):
        out = insert_sorted(x, out)
    return out


def merge(xs: Sequence[int], ys: Sequence[int]) -> list[int]:
    """Merge two lists, taking the smaller head first (ties go to xs)."""
    i = j = 0
    out: list[int] = []
    while i < len(xs) and j < len(ys):
        if xs[i] <= ys[j]:
            out.append(xs[i])
            i += 1
        else:
            out.append(ys[j])
            j += 1
    out.extend(xs[i:])
    out.extend(ys[j:])
    return out


def merge_sort(xs: Sequence[int]) -> list[int]:
    """Top-down merge sort: split at len // 2, sort halves, merge. O(n log n)."""
    xs = list(xs)
    if len(xs) < 2:
        return xs
    mid = len(xs) // 2
    return merge(merge_sort(xs[:mid]), merge_sort(xs[mid:]))


def lower_bound(p: Callable[[int], bool], lo: int, hi: int) -> int:
    """Least i in [lo, hi) with p(i), or hi if none, for a monotone p (False...False True...True).
    Same midpoint rule as the Lean `lowerBound`; equals bisect_left for p(i) = a[i] >= x."""
    while lo < hi:
        mid = (lo + hi) // 2
        if p(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


# ------------------------------------------------------------------ shortest paths

def dijkstra_array(n: int, w: dict[tuple[int, int], int], s: int) -> list[int | None]:
    """O(n^2) Dijkstra, step for step the Lean `dijkstra`: settle the unvisited vertex with the
    smallest finite tentative distance (ties to the smallest index), relax its out-edges.
    `w[(u, v)]` is the weight of the directed edge u -> v (non-negative). None = unreachable."""
    if any(c < 0 for c in w.values()):
        raise ValueError("non-negative weights only")
    out: list[list[tuple[int, int]]] = [[] for _ in range(n)]
    for (u, v), c in w.items():
        out[u].append((v, c))
    dist: list[int | None] = [None] * n
    dist[s] = 0
    visited = [False] * n
    for _ in range(n):
        u, du = None, None
        for v in range(n):
            if not visited[v] and dist[v] is not None and (du is None or dist[v] < du):
                u, du = v, dist[v]
        if u is None:
            break
        visited[u] = True
        for v, c in out[u]:
            if dist[v] is None or du + c < dist[v]:
                dist[v] = du + c
    return dist


def dijkstra_heap(n: int, w: dict[tuple[int, int], int], s: int) -> list[int | None]:
    """O((n + m) log n) Dijkstra with a binary heap and lazy deletion. Same answer as the
    array version; the Lean proof covers the array version."""
    import heapq
    if any(c < 0 for c in w.values()):
        raise ValueError("non-negative weights only")
    out: list[list[tuple[int, int]]] = [[] for _ in range(n)]
    for (u, v), c in w.items():
        out[u].append((v, c))
    dist: list[int | None] = [None] * n
    dist[s] = 0
    heap = [(0, s)]
    while heap:
        d, u = heapq.heappop(heap)
        if d != dist[u]:
            continue
        for v, c in out[u]:
            if dist[v] is None or d + c < dist[v]:
                dist[v] = d + c
                heapq.heappush(heap, (d + c, v))
    return dist


# ------------------------------------------------------------------ disjoint sets

def uf_build(n: int, pairs) -> list[int]:
    """Quick-find, exactly the Lean `ufBuild`: start with lbl[x] = x; union(a, b) gives every
    element labelled lbl[a] the label lbl[b]. O(n) per union."""
    lbl = list(range(n))
    for a, b in pairs:
        la, lb = lbl[a], lbl[b]
        lbl = [lb if l == la else l for l in lbl]
    return lbl


class UnionFind:
    """Union by size with path compression: near-constant amortized time per operation."""

    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, x: int) -> int:
        root = x
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[x] != root:
            self.parent[x], x = root, self.parent[x]
        return root

    def union(self, a: int, b: int) -> None:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        if self.size[ra] < self.size[rb]:
            ra, rb = rb, ra
        self.parent[rb] = ra
        self.size[ra] += self.size[rb]
