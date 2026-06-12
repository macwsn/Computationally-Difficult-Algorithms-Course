#!/usr/bin/python3
# -*- coding: utf-8 -*-
"""
Generator GWARANTOWANIE rozwiazywalnych plansz.
Kazdy kot dostaje rozlaczna, czysta trase L-ksztaltna (1 lustro) od wlasnego lasera,
wiec zamierzone rozwiazanie (po 1 lustrze na rogu kazdej trasy) oswietla wszystkie koty.

Uzycie:
  python gen.py W H walls cats L seed > test.txt
  python gen.py 100 100 50 100 150 1 test.txt   # 5. arg = plik wyjscia
Domyslnie: 100 100 50 100 150 1
"""
import sys
import random


def gen(W, H, walls, cats, L, seed):
    random.seed(seed)
    g = [['.'] * W for _ in range(H)]
    res = [[False] * W for _ in range(H)]   # zarezerwowane pola trasy
    placed = 0
    tries = 0
    while placed < cats and tries < cats * 200:
        tries += 1
        cr = random.randrange(H)
        cc = random.randrange(W)
        a = random.randint(2, 12)            # noga pozioma (laser -> rog)
        b = random.randint(2, 12)            # noga pionowa (rog -> kot)
        lc = cc - a if random.random() < 0.5 else cc + a
        tr = cr - b if random.random() < 0.5 else cr + b
        if not (0 <= lc < W and 0 <= tr < H):
            continue
        # zbierz wszystkie pola trasy
        cells = []
        lo, hi = (lc, cc) if lc < cc else (cc, lc)
        for c in range(lo, hi + 1):
            cells.append((cr, c))
        ro, rb = (cr, tr) if cr < tr else (tr, cr)
        for r in range(ro, rb + 1):
            cells.append((r, cc))
        # wszystkie wolne i nie zarezerwowane?
        if any(g[r][c] != '.' or res[r][c] for r, c in cells):
            continue
        # ustaw laser, kota; rog zostaje '.' (lustro dolozy solver)
        laser = '>' if lc < cc else '<'
        g[cr][lc] = laser
        g[tr][cc] = 'O'
        for r, c in cells:
            res[r][c] = True
        placed += 1
    # sciany w wolnych, nie zarezerwowanych polach
    wp = 0
    wt = 0
    while wp < walls and wt < walls * 50:
        wt += 1
        r = random.randrange(H)
        c = random.randrange(W)
        if g[r][c] == '.' and not res[r][c]:
            g[r][c] = '#'
            wp += 1
    lines = [f'{W} {H} {L}']
    for row in g:
        lines.append(''.join(row))
    return '\n'.join(lines) + '\n', placed, wp


if __name__ == '__main__':
    a = sys.argv
    W = int(a[1]) if len(a) > 1 else 100
    H = int(a[2]) if len(a) > 2 else 100
    walls = int(a[3]) if len(a) > 3 else 50
    cats = int(a[4]) if len(a) > 4 else 100
    L = int(a[5]) if len(a) > 5 else 150
    seed = int(a[6]) if len(a) > 6 else 1
    out_path = a[7] if len(a) > 7 else None
    text, pc, wc = gen(W, H, walls, cats, L, seed)
    if out_path:
        with open(out_path, 'w', encoding='ascii', newline='\n') as f:
            f.write(text)
        sys.stderr.write(f'koty={pc} sciany={wc} L={L}\n')
    else:
        sys.stdout.write(text)
