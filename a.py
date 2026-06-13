import sys
def runner():
    if len(sys.argv) >= 3:
        with open(sys.argv[1], 'r') as f: data = f.read()
        out_stream = open(sys.argv[2], 'w')
    else:
        data = sys.stdin.buffer.read().decode()
        out_stream = sys.stdout
    lines = data.split('\n')
    W, H, L = (int(x) for x in lines[0].split())
    HW = H * W

    DOT = ord('.')
    WALL = ord('#')
    OO = ord('O')
    SL = ord('/')
    BS = ord('\\')

    grid = bytearray(HW)
    for i in range(H):
        row = lines[i + 1] if i + 1 < len(lines) else ''
        off = i * W
        for j in range(W): grid[off + j] = ord(row[j]) if j < len(row) else DOT

    dirs = {ord('A'): (-1, 0), ord('V'): (1, 0), ord('<'): (0, -1), ord('>'): (0, 1)}
    lasers = []
    targets = []
    for idx in range(HW):
        ch = grid[idx]
        if ch in dirs:
            dr, dc = dirs[ch]
            lasers.append((idx // W, idx % W, dr, dc))
        elif ch == OO: targets.append(idx)

    MAX_STEPS = 4 * HW + 4

    def trace():
        empty_order = []
        empty_ar = bytearray(HW)
        lit_ar = bytearray(HW)
        for lr, lc, dr0, dc0 in lasers:
            dr, dc = dr0, dc0
            r, c = lr + dr, lc + dc
            steps = 0
            while 0 <= r < H and 0 <= c < W:
                steps += 1
                if steps > MAX_STEPS: break
                idx = r * W + c
                ch = grid[idx]
                if ch == WALL: break
                if ch == OO: lit_ar[idx] = 1
                elif ch == SL: dr, dc = -dc, -dr
                elif ch == BS: dr, dc = dc, dr
                elif ch == DOT:
                    if not empty_ar[idx]:
                        empty_ar[idx] = 1
                        empty_order.append(idx)
                r += dr
                c += dc
        return lit_ar, empty_order
    fail_max = {}

    def backtrack(left):
        lit_ar, empty = trace()
        unlit = [t for t in targets if not lit_ar[t]]
        if not unlit: return True
        if left == 0: return False

        key = bytes(grid)
        cached = fail_max.get(key, -1)
        if cached >= left: return False
        urc = [divmod(t, W) for t in unlit]

        def prio(idx):
            r, c = divmod(idx, W)
            return min(abs(r - tr) + abs(c - tc) for tr, tc in urc)

        empty.sort(key=prio)
        for idx in empty:
            if grid[idx] != DOT:continue
            for m in (SL, BS):
                grid[idx] = m
                if backtrack(left - 1): return True
                grid[idx] = DOT
        if left > cached:fail_max[key] = left
        return False

    backtrack(L)

    out = out_stream.write
    out(f"{W} {H} {L}\n")
    for i in range(H):
        out(grid[i * W:(i + 1) * W].decode('ascii'))
        out('\n')
    if out_stream is not sys.stdout: out_stream.close()

if __name__ == '__main__':
    runner()