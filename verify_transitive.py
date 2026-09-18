#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
JSP-001021 — machine verification of the lower bound ceil(log2(n+1)).

Checks performed:
  (A) Exhaustive (n = 1..6): over ALL 2^{C(n,2)} tournaments, the minimum over
      tournaments of the largest transitive subtournament size equals bound(n)
      = ceil(log2(n+1)). (For these n the lower bound is sharp / attained.)
  (B) Constructive greedy algorithm (the induction proof, implemented): on many
      random tournaments it always returns a transitive subtournament of size
      >= bound(n).
  (C) Tight examples: the 3-cycle (n=3), a non-transitive 4-vertex tournament
      (n=4), and Paley(7) (n=7) each have largest transitive subtournament
      exactly bound(n).

NOTE: this script verifies the lower bound and its sharpness for specific small n.
It does NOT claim the lower bound is tight for every n. That is an open problem:
Erdos-Moser (1964) conjectured f(n)=ceil(log2(n+1)) and Reid-Parker (1970)
disproved it (f(n) > ceil(log2(n+1)) for some n).
"""

import itertools, random, sys

def bound(n):
    """Exact integer match of the Lean `bound`: bound(0)=0, bound(v)=1+bound(v//2).
    Equals ceil(log2(n+1)); no floating point involved."""
    res = 0
    v = n
    while v > 0:
        res += 1
        v = v // 2
    return res

# ---------- 竞赛图表示 ----------
# 顶点 0..n-1，edge[a] = 出邻域的 bitmask（a 击败的全体顶点）
def make_tournament(n, bitmask_edges):
    """bitmask_edges 长度为 C(n,2)，按 (i,j), i<j 的顺序给出方向 i->j 与否。"""
    edge = [0] * n
    k = 0
    for i in range(n):
        for j in range(i + 1, n):
            if (bitmask_edges >> k) & 1:
                edge[i] |= (1 << j)
            else:
                edge[j] |= (1 << i)
            k += 1
    return edge

def is_transitive(edge, verts):
    """verts 为顶点集合(bitmask)，判断诱导子竞赛图是否传递（无有向 3-圈）。"""
    vs = [v for v in range(64) if (verts >> v) & 1]
    for a in range(len(vs)):
        for b in range(len(vs)):
            for c in range(len(vs)):
                if a == b or b == c or a == c:
                    continue
                va, vb, vc = vs[a], vs[b], vs[c]
                if (edge[va] >> vb) & 1 and (edge[vb] >> vc) & 1 and (edge[vc] >> va) & 1:
                    return False
    return True

def max_transitive_bruteforce(edge, n):
    """穷举所有子集求最大传递子竞赛图尺寸。仅适用于小 n。"""
    best = 0
    for mask in range(1 << n):
        cnt = bin(mask).count("1")
        if cnt <= best:
            continue
        if is_transitive(edge, mask):
            best = cnt
    return best

def max_transitive_fast(edge, n):
    """按子集尺寸从大到小搜索，命中即返回（大部分图不必穷尽所有子集）。"""
    verts = list(range(n))
    for k in range(n, 0, -1):
        for combo in itertools.combinations(verts, k):
            mask = 0
            for v in combo:
                mask |= (1 << v)
            if is_transitive(edge, mask):
                return k
    return 0

def greedy_transitive(edge, n):
    """归纳证明的构造算法：取顶点 v，比较出/入邻域大小，递归较大者，
    把 v 接到有序序列头或尾，返回 (尺寸, 有序顶点列表)。"""
    vertices = list(range(n))
    # 返回该点集上的传递子竞赛图最大有序序列
    def rec(subset):
        if not subset:
            return []
        # 选第一个顶点 v
        v = subset[0]
        rest = [u for u in subset if u != v]
        out_nbr = [u for u in rest if (edge[v] >> u) & 1]   # v 击败的
        in_nbr  = [u for u in rest if (edge[u] >> v) & 1]   # 击败 v 的
        if len(out_nbr) >= len(in_nbr):
            seq = rec(out_nbr)          # v 击败 out_nbr 中全部
            return [v] + seq
        else:
            seq = rec(in_nbr)           # in_nbr 全部击败 v
            return seq + [v]
    seq = rec(vertices)
    return seq

def seq_is_transitive(edge, seq):
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if not ((edge[seq[i]] >> seq[j]) & 1):
                return False
    return True

# ---------- (A) 穷举 n=1..6 ----------
def exhaustive_check(max_n=6):
    print("=== (A) 穷举验证：对所有竞赛图，最小最大传递子竞赛图尺寸 == bound(n) ===")
    ok = True
    for n in range(1, max_n + 1):
        m = n * (n - 1) // 2
        total = 1 << m
        minmt = n  # 上界
        for bm in range(total):
            edge = make_tournament(n, bm)
            mt = max_transitive_fast(edge, n)
            if mt < minmt:
                minmt = mt
        b = bound(n)
        status = "OK" if minmt == b else "FAIL"
        if minmt != b:
            ok = False
        print(f"  n={n:2d}: 竞赛图数={total:>8}  最小最大传递尺寸={minmt}  bound(n)={b}  -> {status}")
    return ok

# ---------- (B) 构造性贪心在随机竞赛图上 ----------
def greedy_random_check(trials=2000, max_n=40):
    print("\n=== (B) 构造性贪心算法（归纳证明的算法）随机验证：返回尺寸 >= bound(n) ===")
    ok = True
    random.seed(12345)
    for n in range(1, max_n + 1):
        b = bound(n)
        worst = n
        for _ in range(trials):
            m = n * (n - 1) // 2
            bm = random.getrandbits(m)
            edge = make_tournament(n, bm)
            seq = greedy_transitive(edge, n)
            assert seq_is_transitive(edge, seq), "贪心返回了非传递序列！"
            sz = len(seq)
            worst = min(worst, sz)
            if sz < b:
                ok = False
                print(f"  n={n}: 反例！贪心返回 {sz} < bound {b}")
                break
        print(f"  n={n:2d}: bound={b}  贪心最差返回尺寸={worst}  -> {'OK' if worst >= b else 'FAIL'}")
    return ok

# ---------- (C) 紧例构造 ----------
def paley7():
    """Paley 竞赛图（模 7 二次剩余），n=7，应最大传递尺寸=3。"""
    n = 7
    residues = {1, 2, 4}
    edge = [0] * n
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            d = (b - a) % n
            if d in residues:
                edge[a] |= (1 << b)
    return edge, n

def check_tight_examples():
    print("\n=== (C) 紧例（最大传递子竞赛图尺寸 == bound(n)）===")
    ok = True
    # n=3: 3-圈
    # 显式构造 3-圈：0->1, 1->2, 2->0（顶点集上不含传递三元组）
    e3 = [0]*3
    e3[0] |= (1<<1); e3[1] |= (1<<2); e3[2] |= (1<<0)
    mt3 = max_transitive_bruteforce(e3, 3)
    print(f"  n=3  3-圈:        最大传递尺寸={mt3}  bound={bound(3)}  -> {'紧' if mt3==bound(3) else 'FAIL'}")
    ok &= (mt3 == bound(3))

    # 具体构造：顶点 {0,1,2} 构成有向 3-圈 0->1, 1->2, 2->0；
    #           顶点 3 击败 0 与 1，并被 2 击败（3->0, 3->1, 2->3）。
    #           该 4 阶竞赛图非传递，其最大传递子竞赛图尺寸恰为 bound(4)=3。
    e4 = [0]*4
    # 0->1,1->2,2->0 构成 3-圈；3->0, 3->1, 2->3
    e4[0] |= (1<<1); e4[1] |= (1<<2); e4[2] |= (1<<0)
    e4[3] |= (1<<0); e4[3] |= (1<<1); e4[2] |= (1<<3)
    mt4 = max_transitive_bruteforce(e4, 4)
    print(f"  n=4  非传递图:    最大传递尺寸={mt4}  bound={bound(4)}  -> {'紧' if mt4==bound(4) else 'FAIL'}")
    ok &= (mt4 == bound(4))

    # n=7: Paley
    e7, n7 = paley7()
    mt7 = max_transitive_bruteforce(e7, n7)
    print(f"  n=7  Paley(7):    最大传递尺寸={mt7}  bound={bound(7)}  -> {'紧' if mt7==bound(7) else 'FAIL'}")
    ok &= (mt7 == bound(7))
    return ok

def main():
    print("JSP-001021 竞赛图传递子竞赛图下界  ceil(log2(n+1))  机器验证\n")
    print("说明：n<=6 为对所有竞赛图的完全穷举（精确证明 bound 值）；")
    print("      n<=40 的构造性贪心算法(即归纳证明的算法)随机验证；紧例单独验证。\n")
    a = exhaustive_check(6)
    b = greedy_random_check(2000, 40)
    c = check_tight_examples()
    print("\n汇总:", "全部通过 ✅" if (a and b and c) else "存在失败 ❌")
    sys.exit(0 if (a and b and c) else 1)

if __name__ == "__main__":
    main()
