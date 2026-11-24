"""Graph algorithms used for the WOWII conjectures. Graphs are adjacency bitmasks:
adj[v] has bit u set iff u ~ v. Exponential algorithms are exact and meant for small graphs
(they are used to search every graph on up to ~10 vertices)."""
from __future__ import annotations

from math import inf

Adj = list[int]


def from_edges(n: int, edges) -> Adj:
    adj = [0] * n
    for a, b in edges:
        if a == b:
            raise ValueError("no loops")
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return adj


def _bits(mask: int):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def popcount(x: int) -> int:
    return bin(x).count("1")


# ---------------------------------------------------------------- distances (BFS)

def bfs_distances(adj: Adj, s: int, within: int | None = None) -> list[float]:
    """Layer-by-layer BFS on bitmasks. O(n^2 / wordsize). inf for unreachable vertices.
    `within` restricts the search to an induced subgraph."""
    n = len(adj)
    allowed = (1 << n) - 1 if within is None else within
    dist = [inf] * n
    dist[s] = 0
    seen = frontier = 1 << s
    d = 0
    while frontier:
        d += 1
        nxt = 0
        for v in _bits(frontier):
            nxt |= adj[v]
        nxt &= allowed & ~seen
        for v in _bits(nxt):
            dist[v] = d
        seen |= nxt
        frontier = nxt
    return dist


def eccentricities(adj: Adj) -> list[float]:
    return [max(bfs_distances(adj, s)) for s in range(len(adj))]


def radius(adj: Adj) -> float:
    return min(eccentricities(adj))


def diameter(adj: Adj) -> float:
    return max(eccentricities(adj))


def dist_even(adj: Adj, v: int) -> int:
    """Number of vertices at even distance from v (v itself included)."""
    return sum(1 for d in bfs_distances(adj, v) if d != inf and d % 2 == 0)


# ---------------------------------------------------------------- subset predicates

def is_connected(adj: Adj, S: int) -> bool:
    if S == 0:
        return False
    s = (S & -S).bit_length() - 1
    reach = bfs_distances(adj, s, within=S)
    return all(reach[v] != inf for v in _bits(S))


def edges_inside(adj: Adj, S: int) -> int:
    return sum(popcount(adj[v] & S) for v in _bits(S)) // 2


def components(adj: Adj, S: int) -> int:
    count, rest = 0, S
    while rest:
        s = (rest & -rest).bit_length() - 1
        d = bfs_distances(adj, s, within=S)
        comp = sum(1 << v for v in _bits(S) if d[v] != inf)
        rest &= ~comp
        count += 1
    return count


def is_independent(adj: Adj, S: int) -> bool:
    return all(adj[v] & S == 0 for v in _bits(S))


def is_forest(adj: Adj, S: int) -> bool:
    return edges_inside(adj, S) == popcount(S) - components(adj, S)


def is_tree(adj: Adj, S: int) -> bool:
    return S != 0 and is_connected(adj, S) and edges_inside(adj, S) == popcount(S) - 1


# ---------------------------------------------------------------- exact invariants

def _max_subset(adj: Adj, pred, universe: int | None = None) -> int:
    n = len(adj)
    U = (1 << n) - 1 if universe is None else universe
    best, sub = 0, U
    while True:
        k = popcount(sub)
        if k > best and pred(adj, sub):
            best = k
        if sub == 0:
            return best
        sub = (sub - 1) & U


def independence_number(adj: Adj, within: int | None = None) -> int:
    return _max_subset(adj, is_independent, within)


def local_independence(adj: Adj, v: int) -> int:
    """lambda(v): independence number of the neighbourhood of v."""
    return independence_number(adj, adj[v])


def largest_induced_tree(adj: Adj) -> int:
    return _max_subset(adj, is_tree)


def largest_induced_forest(adj: Adj) -> int:
    return _max_subset(adj, is_forest)


def residue(degrees: list[int]) -> int:
    """Havel-Hakimi residue: repeatedly delete the largest degree d and subtract 1 from the next d
    (floored at 0, matching Lean's natural-number subtraction); the residue is the number of zeros left."""
    s = sorted(degrees, reverse=True)
    while s and s[0] > 0:
        d, rest = s[0], s[1:]
        s = sorted([max(x - 1, 0) for x in rest[:d]] + rest[d:], reverse=True)
    return len(s)


def path_vertex_sets(adj: Adj) -> list[bool]:
    """hp[S] is True iff some (not necessarily induced) path visits exactly the vertices of S.
    Held-Karp style DP over (S, endpoint). O(2^n n^2)."""
    n = len(adj)
    end = [0] * (1 << n)
    for v in range(n):
        end[1 << v] = 1 << v
    for S in range(1, 1 << n):
        for v in _bits(end[S]):
            for w in _bits(adj[v] & ~S):
                end[S | 1 << w] |= 1 << w
    return [e != 0 for e in end]


def has_hamiltonian_path(adj: Adj) -> bool:
    return path_vertex_sets(adj)[(1 << len(adj)) - 1]


def path_cover_number(adj: Adj) -> int:
    """Fewest vertex-disjoint paths covering every vertex. Subset DP over path sets, O(3^n)."""
    n = len(adj)
    hp = path_vertex_sets(adj)
    f = [0] + [inf] * ((1 << n) - 1)
    for S in range(1, 1 << n):
        low = S & -S
        sub = S
        while sub:
            if sub & low and hp[sub]:
                f[S] = min(f[S], f[S & ~sub] + 1)
            sub = (sub - 1) & S
    return int(f[(1 << n) - 1])


def vertex_connectivity(adj: Adj) -> int:
    """Smallest vertex set whose removal disconnects the graph; n - 1 for complete graphs."""
    n = len(adj)
    full = (1 << n) - 1
    best = n - 1
    for S in range(1 << n):
        if popcount(S) < best and not is_connected(adj, full & ~S):
            best = popcount(S)
    return best
