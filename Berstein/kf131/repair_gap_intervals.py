#!/usr/bin/env python3
"""Cut known gap envelopes out of child intervals and recombine parent covers.

Every resulting rule is checked by the unchanged ScalarVerifier. New clipped
child types remain explicit open obligations; no filled-interval claim follows
from a local cover alone.
"""
import argparse
import copy
from functools import lru_cache
from itertools import product
import json
from pathlib import Path

from exact import F, state_of
from anchored_geometry import ALPHA, B, difference_range, factor_range
from exact import extreme_tail
from scalar_geometry import endpoint_image
from scalar_obstructions import replay, tail_hull, exact_hull, rational_in, discover
from verify_scalar_graph import ScalarVerifier


def rounded(value, grid, up):
    approximate = F(B.coerce(value).decimal(25))*grid
    k = approximate.numerator//approximate.denominator
    while F(k,grid) > value:
        k -= 1
    while F(k+1,grid) <= value:
        k += 1
    return k+int(up and F(k,grid) < value)


@lru_cache(maxsize=1024)
def gap_partition(serialized):
    cert = json.loads(serialized)
    replay(cert)
    node = cert['type']
    states = tuple(map(state_of,node['states']))
    p,t = node['parity'],F(cert['target'])
    parameters = tuple(map(F,cert['parameters']))
    leaves = []
    for row in cert['tree']:
        if row['children']:
            continue
        left,right = tail_hull(states[0],row['u']),tail_hull(states[1],row['v'])
        low = (left[0],right[0] if p > 0 else right[1])
        high = (left[1],right[1] if p > 0 else right[0])
        lo,hi = exact_hull(states,row['u'],row['v'],parameters,p)
        leaves.append((hi < t,low,high))
    return leaves


def gap_envelope(cert, grid, box=None):
    """Outer enclosure of the gap separating the saved lower/upper leaves.

    For any parameter, the lower-side union ends at L and upper-side union
    starts at R. Bounds below imply lower <= L and R <= upper, so any (L,R)
    lies in this envelope. This does NOT say the envelope is entirely empty.
    """
    node = cert['type']
    checker = ScalarVerifier(dict(schema='kf131-scalar-atlas-v1',settings=cert['settings'],nodes=[node]))
    box = checker.box(0) if box is None else box
    p = node['parity']
    lower,upper = [],[]
    for below,low,high in gap_partition(json.dumps(cert,sort_keys=True)):
        if below:
            lower.append(difference_range(high,(ALPHA,ALPHA),*box,p)[0])
        else:
            upper.append(difference_range(low,(ALPHA,ALPHA),*box,p)[1])
    if not lower or not upper:
        raise ValueError('tree does not have two sides')
    return rounded(max(lower),grid,False)-1,rounded(min(upper),grid,True)+1


def subtract(interval, cuts):
    parts = [tuple(interval)]
    for a,b in sorted(cuts):
        if b <= a:
            continue
        new = []
        for lo,hi in parts:
            if hi <= a or b <= lo:
                new.append((lo,hi))
            else:
                if lo < a:
                    new.append((lo,a))
                if b < hi:
                    new.append((b,hi))
        parts = new
    return parts


def library_cover(checker, request, interval, candidates, viable=lambda j: True):
    """Cover a scalar request by existing types valid on its WHOLE box.

    Containment of each parameter box, not just intersection, is required.
    These are coinductive obligations, not assumptions of established filling.
    """
    source = checker.nodes[request]
    box = checker.box(request)
    available = []
    for j in candidates:
        target = checker.nodes[j]
        if target['parity'] != source['parity']:
            continue
        if tuple(map(state_of,target['states'])) != tuple(map(state_of,source['states'])):
            continue
        a,b = target['interval']
        if b <= interval[0] or interval[1] <= a:
            continue
        other = checker.box(j)
        if not all(c <= a <= b <= d for (a,b),(c,d) in zip(box,other)):
            continue
        if viable(j):
            available.append(j)
    current,end = interval
    chosen = []
    while current < end:
        options = [j for j in available if checker.nodes[j]['interval'][0] <= current < checker.nodes[j]['interval'][1]]
        if not options:
            return None
        j = max(options,key=lambda j:checker.nodes[j]['interval'][1])
        chosen.append(j)
        current = checker.nodes[j]['interval'][1]
    return chosen


def library_fragments(checker,requests,interval,pools,viable=lambda j: True):
    """Existing domains can cover only PART of an affine preimage request.

    Such a part is still a useful parent offer. Requiring existing types to
    cover the whole preimage would miss, in particular, central return maps.
    """
    parts = [tuple(interval)]
    for request,candidates in zip(requests,pools):
        n = checker.nodes[request]
        box = checker.box(request)
        available = []
        for j in candidates:
            m = checker.nodes[j]
            if m['parity'] != n['parity'] or tuple(map(state_of,m['states'])) != tuple(map(state_of,n['states'])):
                continue
            if not all(c <= a <= b <= d for (a,b),(c,d) in zip(box,checker.box(j))):
                continue
            a,b = max(interval[0],m['interval'][0]),min(interval[1],m['interval'][1])
            if a < b and viable(j):
                available.append((a,b))
        merged = []
        for a,b in sorted(available):
            if merged and a <= merged[-1][1]:
                merged[-1] = (merged[-1][0],max(b,merged[-1][1]))
            else:
                merged.append((a,b))
        parts = [(max(a,c),min(b,d)) for a,b in parts for c,d in merged if max(a,c) < min(b,d)]
        if not parts:
            break
    return parts


def choose_candidate(available, reusable, prefer_reuse=False):
    """Prefer a genuine finite-library return when requested, retaining progress."""
    def score(item):
        destinations = {j for case in item[1]['cases'] for j in case['destinations']}
        returns = bool(destinations) and destinations <= reusable
        return (prefer_reuse and returns,item[2],item[0][1])
    return max(available,key=score)


def repair(incoming, certificates, grid=1024000000, expand_offers=False, sieve_budget=0, reuse_types=False, whole_depth=0, local_envelopes=False, allow_partial=False, use_library_fragments=False, prefer_reuse=False):
    if whole_depth and not sieve_budget:
        raise ValueError('whole interval proposals require a positive exact sieve budget')
    if incoming.get('generated_moves') and not expand_offers:
        raise ValueError('generated moves require newly assigned intervals: use --expand-offers')
    old_grid = incoming['settings']['grid']
    if grid % old_grid:
        raise ValueError('new grid must refine the old grid')
    scale = grid//old_grid
    settings = dict(incoming['settings'],grid=grid)
    data = dict(schema='kf131-scalar-atlas-v1',settings=settings,nodes=[],roots=[],
                closed_candidate=False,status='local gap repairs; child obligations remain open')
    ids,variants = {},{}
    for old,node in incoming['nodes'].items():
        old = int(old)
        row = copy.deepcopy(node)
        row.update(id=len(data['nodes']),children=[],covered=False,
                   interval=[v*scale for v in node['interval']],source_node=old)
        ids[old] = row['id']
        data['nodes'].append(row)
    checker = ScalarVerifier(data)
    reusable = {j for old,j in ids.items() if old >= 0}
    reuse_pool = {}
    for old,j in ids.items():
        if old >= 0:
            n = data['nodes'][j]
            key = tuple(map(state_of,n['states'])),n['parity'],n['ratio_bin']
            reuse_pool.setdefault(key,[]).append(j)
    bands = []
    for cert in certificates:
        other = ScalarVerifier(dict(schema='kf131-scalar-atlas-v1',settings=cert['settings'],nodes=[cert['type']]))
        # In local mode only geometrically relevant trees need replay/ranges.
        # A used tree is still replayed by gap_envelope on its destination box.
        bands.append((cert,other.box(0),None if local_envelopes else gap_envelope(cert,grid)))
    cuts = {}
    envelope_cache = {}
    def band_on_box(i,cert,box,span):
        if not local_envelopes:
            return span
        key = i,tuple(box)
        if key not in envelope_cache:
            envelope_cache[key] = gap_envelope(cert,grid,box)
        return envelope_cache[key]
    def cuts_for(old):
        if old in cuts:
            return cuts[old]
        j = ids[old]
        node = data['nodes'][j]
        box = checker.box(j)
        states = tuple(map(state_of,node['states']))
        cuts[old] = [band_on_box(i,cert,box,span) for i,(cert,cb,span) in enumerate(bands)
                     if node['parity'] == cert['type']['parity']
                     and states == tuple(map(state_of,cert['type']['states']))
                     and all(max(a,c) <= min(b,d) for (a,b),(c,d) in zip(box,cb))]
        return cuts[old]
    def clipped(old, interval, expand=False):
        j = ids[old]
        original = data['nodes'][j]['interval']
        lo,hi = interval if expand else (max(original[0],interval[0]),min(original[1],interval[1]))
        if lo >= hi:
            return []
        if reuse_types:
            source = data['nodes'][j]
            key = tuple(map(state_of,source['states'])),source['parity'],source['ratio_bin']
            cover = library_cover(checker,j,(lo,hi),reuse_pool.get(key,[]),not_disproved)
            if cover is not None:
                report['reused_requests'] += 1
                return cover
        if [lo,hi] == original:
            return [j]
        key = old,lo,hi
        if key not in variants:
            node = copy.deepcopy(data['nodes'][j])
            node.update(id=len(data['nodes']),interval=[lo,hi],covered=False,children=[])
            variants[key] = node['id']
            data['nodes'].append(node)
        return [variants[key]]
    report = dict(bands=[dict(source_node=c['source_node'],interval=None if s is None else list(s)) for c,_,s in bands],
                  repaired=[],failed=[],candidates=0,cut_edges=0,expanded_offers=expand_offers,
                  sieve_budget=sieve_budget,rejected_edges=0,discovered_obstructions=[],
                  reuse_types=reuse_types,reused_requests=0,whole_depth=whole_depth,local_envelopes=local_envelopes,
                  allow_partial=allow_partial,partial_parents=[],library_fragments=0,
                  candidate_cores=[],prefer_reuse=prefer_reuse)
    viability = {}
    def not_disproved(j):
        if not sieve_budget:
            return True
        n = data['nodes'][j]
        key = (tuple(n['states']),n['parity'],n['ratio_bin'],
               tuple(n.get('ratio_refinement',[0,0])),tuple(n['interval']))
        if key not in viability:
            params = tuple(rational_in(box) for box in checker.box(j))
            a,b = checker.interval(n['interval'])
            viability[key] = True
            def targets():
                # Cheap exact exclusions first; do not construct a large
                # finite outer approximation for an already refuted type.
                yield from (a,b,(a+b)/2,(3*a+b)/4,(a+3*b)/4)
                if whole_depth:
                    from audit_whole_scalar_intervals import sampled_gaps
                    for depth in dict.fromkeys((min(4,whole_depth),whole_depth)):
                        yield from (F(str((lo+hi)/2)) for lo,hi in sampled_gaps(n,params,(a,b),depth)[:16])
            for t in targets():
                if not a <= t <= b:
                    continue
                tree = discover(tuple(map(state_of,n['states'])),n['parity'],params,t,sieve_budget)
                if tree is None:
                    continue
                cert = dict(source_node=n['source_node'],type={k:v for k,v in n.items()
                            if k not in ('id','children','covered')},settings=settings,
                            parameters=list(map(str,params)),target=str(t),tree=tree)
                cert['verification'] = replay(cert)
                report['discovered_obstructions'].append(cert)
                viability[key] = False
                break
        return viability[key]
    hulls,preimages = {},{}
    def initial_hull(old):
        j = ids[old]
        node = data['nodes'][j]
        key = (tuple(node['states']),node['parity'],node['ratio_bin'],
               tuple(node.get('ratio_refinement',[0,0])))
        if key not in hulls:
            sl,sr = map(state_of,node['states'])
            p = node['parity']
            low = (extreme_tail(sl,False)[0],extreme_tail(sr,p<0)[0])
            high = (extreme_tail(sl,True)[0],extreme_tail(sr,p>0)[0])
            lo = difference_range(low,(ALPHA,ALPHA),*checker.box(j),p)[1]
            hi = difference_range(high,(ALPHA,ALPHA),*checker.box(j),p)[0]
            hulls[key] = rounded(lo,grid,True)+1,rounded(hi,grid,False)-1
        return hulls[key]
    def preimage(parent,edge,swap):
        key = parent,tuple(edge['suffixes']),swap
        if key in preimages:
            return preimages[key]
        j = ids[parent]
        rb,sb,hb = checker.box(j)
        p = data['nodes'][j]['parity']
        u,v = edge['suffixes']
        center = endpoint_image(u,v,swap,F(0),rb,sb,hb,p)
        f0,f1 = factor_range(v if swap else u,tuple(sb if swap else rb))
        scales = (hb[0]/f1**2,hb[1]/f0**2) if swap else (1/f1**2,1/f0**2)
        if (p*(-1)**len(v) if swap else (-1)**len(u)) < 0:
            scales = (-scales[1],-scales[0])
        ends = checker.interval(data['nodes'][j]['interval'])
        values = [(t-c)/s for t in ends for c in center for s in scales]
        preimages[key] = rounded(min(values),grid,False)-1,rounded(max(values),grid,True)+1
        return preimages[key]
    for parent in incoming['parents']:
        parent = int(parent)
        seen,candidates = set(),[]
        for rule in incoming['rules']:
            if rule['parent'] != parent:
                continue
            for edge in rule['children']:
                key = json.dumps(edge,sort_keys=True)
                if key in seen:
                    continue
                seen.add(key)
                options = []
                touched = False
                for case in edge['cases']:
                    interval = [v*scale for v in case['interval']]
                    if expand_offers:
                        case = copy.deepcopy(case)
                        # Scalar atoms sharing one parameter box become one
                        # newly assigned interval; no scalar projection shortcut.
                        geometries = {}
                        for old in case['destinations']:
                            n = data['nodes'][ids[old]]
                            key = (tuple(n['states']),n['parity'],n['ratio_bin'],
                                   tuple(n.get('ratio_refinement',[0,0])))
                            geometries.setdefault(key,old)
                        case['destinations'] = list(geometries.values())
                        bounds = [initial_hull(old) for old in case['destinations']]
                        request = preimage(parent,edge,case['swap'])
                        interval = [max(request[0],max(a for a,b in bounds)),
                                    min(request[1],min(b for a,b in bounds))]
                    exclusions = [span for old in case['destinations'] for span in cuts_for(old)]
                    parts = subtract(interval,exclusions) if interval[0] < interval[1] else []
                    touched |= parts != [tuple(interval)]
                    if use_library_fragments:
                        requests = [ids[old] for old in case['destinations']]
                        pools = []
                        for j in requests:
                            n = data['nodes'][j]
                            key = tuple(map(state_of,n['states'])),n['parity'],n['ratio_bin']
                            pools.append(reuse_pool.get(key,[]))
                        fragments = [piece for part in parts for piece in library_fragments(checker,requests,part,pools,not_disproved)]
                        extras = [piece for piece in fragments if piece not in parts]
                        report['library_fragments'] += len(extras)
                        parts = list(dict.fromkeys(parts+extras))
                    options.append([(case,part) for part in parts])
                for combination in product(*options):
                    new = dict(suffixes=edge['suffixes'],cases=[])
                    for case,part in combination:
                        dests = [j for old in case['destinations'] for j in clipped(old,part,expand_offers)]
                        new['cases'].append(dict(swap=case['swap'],interval=list(part),
                                                 destinations=list(dict.fromkeys(dests))))
                    try:
                        core,deps = checker.scalar_child(ids[parent],new)
                    except ValueError:
                        continue
                    if not all(not_disproved(j) for j in deps):
                        report['rejected_edges'] += 1
                        continue
                    candidates.append((core,new,touched,rule['source_rule']))
        report['candidates'] += len(candidates)
        report['candidate_cores'].extend(dict(parent=parent,
            suffixes=edge['suffixes'],interval=[B.coerce(x).record() for x in core])
            for core,edge,_,_ in candidates)
        report['cut_edges'] += sum(c[2] for c in candidates)
        current,end = checker.interval(data['nodes'][ids[parent]]['interval'])
        chosen = []
        while current < end:
            available = [c for c in candidates if c[0][0] <= current < c[0][1]]
            if not available:
                break
            # Prefer trimmed offers when they progress, otherwise bridge using
            # a different saved successor. Positive progress forbids cycles.
            item = choose_candidate(available,reusable,prefer_reuse)
            chosen.append(item)
            current = item[0][1]
        if current < end:
            report['failed'].append(dict(parent=parent,stopped_at=B.coerce(current).record(),
                                        candidates=len(candidates)))
            j = ids[parent]
            start = data['nodes'][j]['interval'][0]
            upper = rounded(current,grid,False)
            if allow_partial and chosen and start < upper:
                original = list(data['nodes'][j]['interval'])
                data['nodes'][j]['interval'] = [start,upper]
                report['partial_parents'].append(dict(parent=parent,original=original,interval=[start,upper]))
                end = F(upper,grid)
        if current >= end:
            j = ids[parent]
            data['nodes'][j].update(covered=True,children=[c[1] for c in chosen])
            verified = checker.local(j)
            data['roots'].append(j)
            report['repaired'].append(dict(parent=parent,certificate_node=j,
                                            trimmed_edges=sum(c[2] for c in chosen),
                                            rules=[c[3] for c in chosen],verification=verified))
        print(json.dumps(dict(parent=parent,covered=current>=end,candidates=len(candidates),
                              trimmed=sum(c[2] for c in chosen))),flush=True)
    # Discard unused exploratory variants but preserve every actual dependency.
    keep = set(data['roots'])
    for j in data['roots']:
        keep.update(checker.local(j)['dependencies'])
    order = sorted(keep)
    renumber = {old:new for new,old in enumerate(order)}
    nodes = []
    for old in order:
        row = copy.deepcopy(data['nodes'][old])
        row['id'] = renumber[old]
        for edge in row['children']:
            for case in edge['cases']:
                case['destinations'] = [renumber[j] for j in case['destinations']]
        nodes.append(row)
    data.update(nodes=nodes,roots=[renumber[j] for j in data['roots']],
                open_nodes=sum(not n['covered'] for n in nodes))
    verify = ScalarVerifier(data)
    report['final_local_checks'] = [verify.local(j) for j in data['roots']]
    for row in report['repaired']:
        row['certificate_node'] = renumber[row['certificate_node']]
        row['verification'] = verify.local(row['certificate_node'])
    report.update(nodes=len(nodes),open_nodes=data['open_nodes'])
    return data,report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('incoming',type=Path)
    ap.add_argument('--obstructions',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--expand-offers',action='store_true')
    ap.add_argument('--sieve-budget',type=int,default=0)
    ap.add_argument('--reuse-types',action='store_true')
    ap.add_argument('--whole-depth',type=int,default=0)
    ap.add_argument('--local-envelopes',action='store_true')
    ap.add_argument('--allow-partial',action='store_true')
    ap.add_argument('--library-fragments',action='store_true')
    ap.add_argument('--prefer-reuse',action='store_true')
    args = ap.parse_args()
    incoming = json.loads(args.incoming.read_text())
    certs = json.loads(args.obstructions.read_text())['obstructions']
    data,report = repair(incoming,certs,expand_offers=args.expand_offers,sieve_budget=args.sieve_budget,
                         reuse_types=args.reuse_types,whole_depth=args.whole_depth,local_envelopes=args.local_envelopes,
                         allow_partial=args.allow_partial,use_library_fragments=args.library_fragments,
                         prefer_reuse=args.prefer_reuse)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    args.output.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(repaired=len(report['repaired']),failed=len(report['failed']),
                         nodes=report['nodes'],open_nodes=report['open_nodes'])),flush=True)


if __name__ == '__main__':
    main()
