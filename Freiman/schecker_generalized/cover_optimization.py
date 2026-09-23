"""Minimum additive cost over uniformly overlapping interval cover chains."""


def minimum_cover_chain(offers, start, end, ge, value):
    """Offers are (lower, upper, tuple-cost); return original offer indices.

    `ge` must compare endpoints throughout the parent domain. Midpoint `value`
    is only a topological ordering; it does not establish uniform overlap.
    Costs count references with multiplicity, not the size of their union.
    """
    order = sorted(range(len(offers)), key=lambda i: value(offers[i][1]))
    distance, previous = {}, {}
    for position, i in enumerate(order):
        lower, upper, weight = offers[i]
        best, parent = None, None
        if value(upper) > value(start)+1e-13 and ge(start, lower) and ge(upper, start):
            best, parent = weight, -1
        for j in order[:position]:
            point = offers[j][1]
            if j in distance and value(upper) > value(point)+1e-13 and ge(point, lower) and ge(upper, point):
                candidate = tuple(a+b for a, b in zip(distance[j], weight))
                if best is None or candidate < best:
                    best, parent = candidate, j
        if best is not None:
            distance[i], previous[i] = best, parent
    endings = [i for i in order if i in distance and ge(offers[i][1], end)]
    if not endings:
        return None
    i = min(endings, key=lambda j: distance[j])
    chain = []
    while i != -1:
        chain.append(i)
        i = previous[i]
    return chain[::-1]
