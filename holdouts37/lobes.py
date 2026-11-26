"""Score diagrams by what makes the good ones good: several separate bright
lobes, black pockets enclosed inside them, and mirror symmetry."""
from collections import deque


def components(grid, val, w, h):
    seen = [[False] * w for _ in range(h)]
    out = []
    for y in range(h):
        for x in range(w):
            if seen[y][x] or grid[y][x] != val:
                continue
            q = deque([(x, y)])
            seen[y][x] = True
            px = []
            while q:
                cx, cy = q.popleft()
                px.append((cx, cy))
                for nx, ny in ((cx + 1, cy), (cx - 1, cy), (cx, cy + 1), (cx, cy - 1)):
                    if 0 <= nx < w and 0 <= ny < h and not seen[ny][nx] and grid[ny][nx] == val:
                        seen[ny][nx] = True
                        q.append((nx, ny))
            out.append(px)
    return out


def score(im):
    g = im.convert('L').resize((96, 144))
    w, h = g.size
    px = g.load()
    on = [[px[x, y] > 60 for x in range(w)] for y in range(h)]
    lobes = [p for p in components(on, True, w, h) if len(p) > 120]
    off = [p for p in components(on, False, w, h) if len(p) > 60]
    holes = [p for p in off if not any(x in (0, w - 1) or y in (0, h - 1) for x, y in p)]
    mirror = sum(1 for y in range(h) for x in range(w // 2) if on[y][x] == on[y][w - 1 - x])
    mirror /= float(h * (w // 2))
    return len(lobes) + 2 * min(len(holes), 6) + 3 * mirror
