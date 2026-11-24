import random

import networkx as nx

from verified_algorithms.classic import UnionFind, dijkstra_array, dijkstra_heap, uf_build

rng = random.Random(1)


def random_digraph(n, p, maxw):
    return {(u, v): rng.randrange(maxw + 1)
            for u in range(n) for v in range(n) if u != v and rng.random() < p}


def test_dijkstra_matches_networkx():
    for _ in range(600):
        n = rng.randrange(1, 14)
        w = random_digraph(n, rng.uniform(0.05, 0.6), rng.choice([0, 1, 5, 100]))
        g = nx.DiGraph()
        g.add_nodes_from(range(n))
        g.add_weighted_edges_from((u, v, c) for (u, v), c in w.items())
        s = rng.randrange(n)
        ref = nx.single_source_dijkstra_path_length(g, s)
        expected = [ref.get(v) for v in range(n)]
        assert dijkstra_array(n, w, s) == expected
        assert dijkstra_heap(n, w, s) == expected


def test_dijkstra_zero_weights_and_unreachable():
    w = {(0, 1): 0, (1, 2): 0, (3, 4): 7}
    assert dijkstra_array(5, w, 0) == [0, 0, 0, None, None]


def test_union_find_matches_connected_components():
    for _ in range(800):
        n = rng.randrange(1, 25)
        pairs = [(rng.randrange(n), rng.randrange(n)) for _ in range(rng.randrange(2 * n + 1))]
        g = nx.Graph()
        g.add_nodes_from(range(n))
        g.add_edges_from(pairs)
        comp = {v: i for i, c in enumerate(nx.connected_components(g)) for v in c}
        lbl = uf_build(n, pairs)
        uf = UnionFind(n)
        for a, b in pairs:
            uf.union(a, b)
        for x in range(n):
            for y in range(n):
                same = comp[x] == comp[y]
                assert (lbl[x] == lbl[y]) == same
                assert (uf.find(x) == uf.find(y)) == same
