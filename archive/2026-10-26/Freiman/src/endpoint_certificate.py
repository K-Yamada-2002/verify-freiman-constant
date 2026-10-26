"""Independent algebraic replay and kernel-destination checking of menus."""
from fractions import Fraction as Q
from anchor_boxes import AnchorUniform
from obstruction_probe import scan


def certify_menu(kernel, a, b, box, target, rows, special_check):
    menu = []
    result = []
    destinations = 0
    for original in rows:
        row = dict(original)
        u, w = tuple(row['u']), tuple(row['w'])
        assert all(d in (1, 2, 3) for d in u + w)
        assert scan(a + u) is not None and scan(b + w) is not None
        l, h = map(Q, row['band'])
        assert 0 <= l <= h <= 1
        menu.append((u, w, f'band_{l}_{1-h}'))
        if row['destination'] != 'kernel':
            assert len(u) + len(w) > 0
            special_check(row)
        else:
            x, y = kernel.side(a, u, box[0]), kernel.side(b, w, box[1])
            assert x is not None and y is not None
            image = box[2][0] * y['growth'][0] / x['growth'][1], box[2][1] * y['growth'][1] / x['growth'][0]
            assert kernel.base ** kernel.low <= image[0] <= image[1] <= kernel.base ** (kernel.high + 1)
            low, high = kernel.index(image[0]), kernel.index(image[1])
            if image[1] == kernel.base ** high:
                high -= 1
            high = max(low, high)
            geometry = x['id'] * kernel.sides + y['id']
            available = []
            for t, p, q in kernel.bands:
                if all(((geometry * kernel.bins + i - kernel.low) * kernel.T + t) in kernel.alive
                       for i in range(low, high + 1)):
                    available.append((p, q, t))
            joined = []
            for p, q, t in sorted(available):
                if joined and p <= joined[-1][1]:
                    joined[-1][1] = max(joined[-1][1], q)
                    joined[-1][2].append(t)
                else:
                    joined.append([p, q, [t]])
            supporting = [component for component in joined if component[0] <= l <= h <= component[1]]
            assert supporting, ('missing_kernel_band', u, w, l, h, low, high)
            types = supporting[0][2]
            destinations += len(types) * (high - low + 1)
            row.update(geometry=geometry, bins=[low, high], types=types)
        result.append(row)
    proof = AnchorUniform(a, b, f'band_{target[0]}_{1-target[1]}', box)
    assert proof.verify(menu), 'uniform_cover_failed'
    return result, {'kernel_memberships': destinations, 'uniform_comparisons': proof.checks}
