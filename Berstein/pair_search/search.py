#!/usr/bin/env python3
"""Numerical search for Gauss--Cantor cylinder pairs below Hall's ray.

Standard library only. Finite hull covers are NOT interior certificates.
All words are written from the central digit outwards, on BOTH sides.
"""
import argparse
from collections import deque
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product, combinations_with_replacement
import json
from pathlib import Path
import time

TAIL = (Q(1, 4), Q(4, 5))

@lru_cache(None)
def cf_bounds(word):
    ends = []
    for x in TAIL:
        for a in reversed(word):
            x = 1 / (int(a) + x)
        ends.append(x)
    return min(ends), max(ends)


def matrix(word):
    a,b,c,d = 1,0,0,1
    for k in map(int, word):
        a,b,c,d = b,a+k*b,d,c+k*d
    return a,b,c,d


class Model:
    def __init__(self, name, alphabet='123', forbidden=()):
        self.name, self.alphabet = name, alphabet
        self.forbidden = tuple(sorted(set(forbidden)))
        if any(w[::-1] not in self.forbidden for w in self.forbidden):
            raise ValueError('This Lagrange reduction requires reversal symmetry')
        if '2' not in alphabet or any(set(w) == {'2'} for w in forbidden):
            raise ValueError('Need the periodic 2 connector')
        states = {''}
        for w in forbidden:
            states.update(w[:k] for k in range(1,len(w)))
        self.states = sorted(states, key=lambda s:(len(s),s))
        self.edges = {}
        for s in self.states:
            edges = []
            for a in alphabet:
                w = s+a
                if any(w.endswith(f) for f in forbidden):
                    continue
                t = max((t for t in self.states if w.endswith(t)), key=len)
                edges.append((a,t))
            self.edges[s] = edges
        self.connectors = {s:self.connector(s) for s in self.states}
        self.bounds = self.tail_bounds(float, 90)

    def connector(self, state):
        # A run longer than every forbidden word must reach the all-2 state.
        reset = '2' * (max(map(len,self.forbidden), default=1)+1)
        queue, seen = deque([(state,'')]), {state}
        while queue:
            s,w = queue.popleft()
            if self.follow(reset,s) is not None:
                return w+reset
            for a,t in self.edges[s]:
                if t not in seen:
                    seen.add(t); queue.append((t,w+a))
        raise ValueError(f'{self.name}: state {state} cannot reach periodic 2')

    def follow(self, word, state=''):
        for a in word:
            state = next((t for k,t in self.edges[state] if k==a), None)
            if state is None:
                return None
        return state

    def tail_bounds(self, cast, iterations):
        lo,hi = cast(1)/cast(4), cast(4)/cast(5)
        bounds = {s:(lo,hi) for s in self.states}
        for _ in range(iterations):
            bounds = {s:(min(1/(cast(a)+bounds[t][1]) for a,t in es),
                         max(1/(cast(a)+bounds[t][0]) for a,t in es))
                      for s,es in self.edges.items()}
        return bounds

    def cylinder(self, word, bounds=None):
        bounds = self.bounds if bounds is None else bounds
        s = self.follow(word)
        if s is None:
            raise ValueError(f'illegal prefix: {word}')
        a,b,c,d = matrix(word)
        x,y = ((a*z+b)/(c*z+d) for z in bounds[s])
        return (word,s,(a,b,c,d),min(x,y),max(x,y))

    def children(self, z, bounds=None):
        bounds = self.bounds if bounds is None else bounds
        word,s,(a,b,c,d),_,_ = z
        for k,t in self.edges[s]:
            m = b,a+int(k)*b,d,c+int(k)*d
            A,B,C,D = m
            x,y = ((A*z+B)/(C*z+D) for z in bounds[t])
            yield (word+k,t,m,min(x,y),max(x,y))

    def cylinders(self, prefix, depth):
        zs = [self.cylinder(prefix)]
        for _ in range(depth):
            zs = [c for z in zs for c in self.children(z)]
        return zs

    def background(self, radius):
        best, witness = Q(0), ''
        # Every legal radius window; no assertion about extendibility is needed
        # for this upper bound (the superset only makes the bound weaker).
        for digits in product(self.alphabet, repeat=2*radius+1):
            w = ''.join(digits)
            if any(f in w for f in self.forbidden):
                continue
            v = int(w[radius])+cf_bounds(w[:radius][::-1])[1]+cf_bounds(w[radius+1:])[1]
            if v>best:
                best,witness = v,w
        return best,witness


def catalogue():
    specs = [
        ('C12','12',()),
        ('F13','123',('13','31')),
        ('F131','123',('131',)),
        ('F131_132','123',('131','132','231')),
        ('F131_133','123',('131','133','331')),
        ('F131_313','123',('131','313')),
        ('F131_121','123',('131','121')),
        ('F131_232','123',('131','232')),
        ('F1312','123',('1312','2131','1313','3131')),
        ('F1313','123',('1313','3131')),
        ('F31313','123',('31313',)),
        ('F13131','123',('13131',)),
        ('C123','123',()),
    ]
    return [Model(*s) for s in specs]


def merge(intervals):
    out=[]
    for lo,hi in sorted(intervals, key=lambda z:(z[0],z[1])):
        if out and lo <= out[-1][1]:
            out[-1][1] = max(out[-1][1],hi)
        else:
            out.append([lo,hi])
    return out


def sum_components(xs, ys, lo=1.1, hi=1.52):
    return merge((max(lo,x[3]+y[3]), min(hi,x[4]+y[4]))
                 for x in xs for y in ys if x[3]+y[3]<hi and x[4]+y[4]>lo)


@lru_cache(None)
def interface_bound(u,v):
    """All noncentral positions at distance <= r, for prefixes of length r.

    Farther windows lie wholly in one legal tail. Here unknown tails are
    bounded universally; the central exception is included explicitly.
    """
    worst = Q(18,5)  # all positions carrying 1 or 2
    for a,b in ((u,v),(v,u)):
        for k,digit in enumerate(a):
            if digit == '3':
                forward = cf_bounds(a[k+1:])[1]
                backward = cf_bounds(a[:k][::-1]+'3'+b)[1]
                worst = max(worst,3+forward+backward)
    return worst


def coverage(m,n,u,v,J,epsilon,budget):
    """Cover fixed J by leaf sum hulls, with width <= epsilon.

    Float-only diagnostic. No tolerance is added to close gaps. Branches
    covered by already accepted leaf hulls can safely be omitted at this scale.
    """
    from bisect import bisect_right
    stack=[(m.cylinder(u),n.cylinder(v))]
    covered=[]; starts=[]; visited=leaves=0; max_width=0.
    while stack and visited<budget:
        x,y=stack.pop(); visited+=1
        lo,hi=x[3]+y[3],x[4]+y[4]
        a,b=max(lo,J[0]),min(hi,J[1])
        if a>b: continue
        i=bisect_right(starts,a)-1
        if i>=0 and covered[i][1]>=b: continue
        if hi-lo<=epsilon:
            leaves+=1; max_width=max(max_width,hi-lo)
            covered=merge(covered+[(a,b)]); starts=[c[0] for c in covered]
        elif x[4]-x[3]>=y[4]-y[3]:
            stack.extend((c,y) for c in m.children(x))
        else:
            stack.extend((x,c) for c in n.children(y))
        if len(covered)==1 and covered[0][0]<=J[0] and covered[0][1]>=J[1]:
            return dict(status='covered_float',visited=visited,leaves=leaves,max_leaf_width=max_width)
    return dict(status='budget_exhausted' if stack else 'gap_float',visited=visited,
                leaves=leaves,max_leaf_width=max_width,components=covered[:20])


def certify_witness(model, word, target_prefix, repeats=100):
    if not word.startswith(target_prefix) or model.follow(word) is None:
        raise ValueError('Illegal witness or wrong cylinder')
    state=model.follow(word)
    if model.follow('2'*max(2,max(map(len,model.forbidden),default=1)),state) is None:
        raise ValueError('Illegal periodic tail')
    return cf_bounds(word+'2'*repeats)


def point_witness(m,n,u,v,target,exponent,budget):
    with localcontext() as ctx:
        ctx.prec=exponent+35
        bounds1=m.tail_bounds(Decimal,4*(exponent+35))
        bounds2=n.tail_bounds(Decimal,4*(exponent+35))
        t=Decimal(target.numerator)/Decimal(target.denominator)
        eps=Decimal(10)**(-exponent)
        stack=[(m.cylinder(u,bounds1),n.cylinder(v,bounds2))]
        visited=0
        while stack and visited<budget:
            x,y=stack.pop(); visited+=1
            lo,hi=x[3]+y[3],x[4]+y[4]
            if not lo<=t<=hi: continue
            if hi-lo<eps/4:
                a=x[0]+m.connectors[x[1]]; b=y[0]+n.connectors[y[1]]
                aa,ab=certify_witness(m,a,u); ba,bb=certify_witness(n,b,v)
                error=max(abs(aa+ba-target),abs(ab+bb-target))
                if error<Q(1,10**exponent):
                    return dict(target=str(target),u=a,v=b,error_upper=str(error),visited=visited)
                return None
            if x[4]-x[3]>=y[4]-y[3]:
                pairs=[(c,y) for c in m.children(x,bounds1)]
            else:
                pairs=[(x,c) for c in n.children(y,bounds2)]
            pairs=[(a,b) for a,b in pairs if a[3]+b[3]<=t<=a[4]+b[4]]
            pairs.sort(key=lambda ab:min(t-ab[0][3]-ab[1][3],ab[0][4]+ab[1][4]-t))
            stack.extend(pairs)
    return None


def run(args):
    start=time.monotonic(); models=catalogue(); byname={m.name:m for m in models}
    backgrounds={m.name:m.background(args.radius) for m in models}
    model_data=[dict(name=m.name,alphabet=m.alphabet,forbidden=m.forbidden,
                     background_bound=str(backgrounds[m.name][0]),
                     background_decimal=float(backgrounds[m.name][0]),
                     maximizing_window=backgrounds[m.name][1],connectors=m.connectors)
                for m in models]
    for d in model_data: print(d['name'],d['background_decimal'],flush=True)
    prefixes={m.name:[''.join(p) for p in product(m.alphabet,repeat=args.radius)
                      if m.follow(''.join(p)) is not None] for m in models}
    cache={}; candidates=[]; examined=eligible=0
    def cylinders(m,u,d):
        key=m.name,u,d
        if key not in cache: cache[key]=m.cylinders(u,d)
        return cache[key]
    for m,n in combinations_with_replacement(models,2):
        bg=max(backgrounds[m.name][0],backgrounds[n.name][0])
        if bg>=Q('4.52'): continue
        local=[]
        for u in prefixes[m.name]:
            for v in prefixes[n.name]:
                if m==n and v<u: continue
                examined+=1
                bound=max(bg,interface_bound(u,v))
                low=max(1.1,float(bound)-3+1e-10)
                if low>=1.52: continue
                x,y=m.cylinder(u),n.cylinder(v)
                if x[4]+y[4]<=low or x[3]+y[3]>=1.52: continue
                eligible+=1
                comps=sum_components(cylinders(m,u,2),cylinders(n,v,2),low,1.52)
                if not comps: continue
                a,b=max(comps,key=lambda z:z[1]-z[0])
                local.append(dict(left=m.name,right=n.name,u=u,v=v,
                                  dominance_bound=str(bound),coarse=[a,b],width=b-a))
        # Retain the best candidate in each 0.02 band, up to six per model pair.
        bins={}
        for c in sorted(local,key=lambda c:-c['width']):
            band=int((3+sum(c['coarse'])/2-4.1)/.02)
            bins.setdefault(band,c)
        shortlist=sorted(bins.values(),key=lambda c:-c['width'])[:args.per_pair]
        for c in shortlist:
            history=[]; lo,hi=c['coarse']
            for depth in (3,4,5):
                comps=sum_components(cylinders(m,c['u'],depth),cylinders(n,c['v'],depth),lo,hi)
                if not comps: break
                a,b=max(comps,key=lambda z:z[1]-z[0])
                history.append(dict(extra_depth=depth,longest=[a,b],width=b-a,components=len(comps)))
                lo,hi=a,b
            if len(history)==3 and hi-lo>1e-7:
                c.update(history=history,interval=[lo+3,hi+3],width=hi-lo,
                         retention=(hi-lo)/(c['coarse'][1]-c['coarse'][0]))
                candidates.append(c)
        print(f'{m.name}+{n.name}: {len(local)} coarse; {len(candidates)} refined total',flush=True)
    # Refine one per distinct model pair first, then distribute over value bands.
    candidates.sort(key=lambda c:-(c['width']*c['retention']))
    selected=[]; seen=set()
    for c in candidates:
        key=(c['left'],c['right'])
        if key not in seen:
            selected.append(c);seen.add(key)
        if len(selected)>=args.verify_count: break
    for c in candidates:
        if len(selected)>=args.verify_count: break
        if c not in selected: selected.append(c)
    args.output.with_suffix('.screen.json').write_text(json.dumps(dict(models=model_data,candidates=candidates),indent=2)+'\n')
    for index,c in enumerate(selected):
        m,n=byname[c['left']],byname[c['right']]
        a,b=c['interval'];mid=(a+b)/2
        width=min(args.window_width,(b-a)/4)
        # Exact decimal rational target interval, independent of binary floats.
        J=[Q(f'{mid-width/2:.12f}')-3,Q(f'{mid+width/2:.12f}')-3]
        if not J[0]+3>Q(c['dominance_bound']):
            raise ValueError('Rounded interval fails dominance')
        c['probe_interval']=[str(x+3) for x in J]
        c['covers']=[dict(epsilon=eps,**coverage(m,n,c['u'],c['v'],list(map(float,J)),eps,args.budget))
                     for eps in args.epsilons]
        witnesses=[]; unresolved=[]
        for k in range(args.points):
            target=J[0]+(J[1]-J[0])*k/(args.points-1)
            w=point_witness(m,n,c['u'],c['v'],target,args.exponent,args.point_budget)
            if w: witnesses.append(w)
            else: unresolved.append(str(target))
        c.update(witnesses=witnesses,unresolved_points=unresolved,
                 probe_status='supported' if all(x['status']=='covered_float' for x in c['covers']) and not unresolved else 'unresolved')
        print(f"probe {index+1}/{len(selected)} {c['left']}+{c['right']} {c['u']}|{c['v']}: {c['probe_status']}",flush=True)
    result=dict(status='Numerical candidates only; no interior or interval inclusion proof',
                config=vars(args)|{'output':str(args.output)},models=model_data,
                examined_prefix_pairs=examined,eligible_prefix_pairs=eligible,
                candidates=candidates,refined_count=len(candidates),probed_count=len(selected),
                elapsed_seconds=time.monotonic()-start)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    write_report(result,args.output.with_suffix('.md'))


def write_report(data,path):
    probed=[c for c in data['candidates'] if 'probe_status' in c]
    supported=sum(c['probe_status']=='supported' for c in probed)
    witness_count=sum(len(c['witnesses']) for c in probed)
    lines=['# Gauss–Cantor 集合対の数値探索','',
           '**内点存在・区間包含の証明ではない。** 禁止語、接頭語、固定小区間の有限スケール検査を列挙する。','',
           f"接頭語対 {data['examined_prefix_pairs']} 組を検査し、支配条件を満たし対象範囲と交わるものは {data['eligible_prefix_pairs']} 組。深さ別の候補は {data['refined_count']} 組、追加検査は {data['probed_count']} 組。",'',
           f"追加検査を全て通過: **{supported} 件**。未通過・未確定: {len(probed)-supported} 件。有理数で検証した点近似: {witness_count} 件（誤差 10^-{data['config']['exponent']} 未満）。",'',
           '`K_A(u)` はモデル A の合法な片側連分数で接頭語 u を持つ集合。表の区間は `3+K_A(u)+K_B(v)` の候補。左右とも中央から外向きに読む。','',
           '|モデル|数字|禁止語|背景 Perron 上界（半径 r）|','|---|---|---|---:|']
    for m in data['models']:
        lines.append(f"|{m['name']}|{m['alphabet']}|{', '.join(m['forbidden']) or 'なし'}|{m['background_decimal']:.12f}|")
    lines+=['','## 固定区間の追加検査','',
            '和凸包被覆は倍精度数値判定。点の近似表示は有理数で独立検証済み。`supported` は指定スケールと指定点数で成功した意味。','',
            '|A, B|u, v|固定区間（3 加算後）|他位置上界|被覆|点近似|判定|',
            '|---|---|---|---:|---|---:|---|']
    for c in data['candidates']:
        if 'covers' not in c: continue
        a,b=map(lambda x:float(Q(x)),c['probe_interval'])
        covers=', '.join(f"{x['epsilon']:g}: {x['status']}" for x in c['covers'])
        lines.append(f"|{c['left']}, {c['right']}|{c['u']}, {c['v']}|[{a:.12f}, {b:.12f}]|{float(Q(c['dominance_bound'])):.10f}|{covers}|{len(c['witnesses'])}/{data['config']['points']}|{c['probe_status']}|")
    lines+=['','## 全ての深さ 5 候補','',
            'この広い区間は最後の有限外側近似の連結成分。上表の固定区間より弱い証拠。保持率は深さ 2 成分に対する深さ 5 成分の長さの比であり、次元・確率ではない。','',
            '|A, B|u, v|有限近似の候補区間|幅|保持率|','|---|---|---|---:|---:|']
    for c in data['candidates']:
        a,b=c['interval']
        lines.append(f"|{c['left']}, {c['right']}|{c['u']}, {c['v']}|[{a:.10f}, {b:.10f}]|{c['width']:.3g}|{c['retention']:.4f}|")
    lines+=['',f"所要時間: {data['elapsed_seconds']:.1f} 秒。設定と全点の有理数検証データは同名 JSON。",'']
    path.write_text('\n'.join(lines))


def replay(path):
    data=json.loads(path.read_text());models={m.name:m for m in catalogue()};count=0
    backgrounds={m.name:m.background(data['config']['radius'])[0] for m in models.values()}
    for saved in data['models']:
        model=models[saved['name']]
        if saved['alphabet']!=model.alphabet or tuple(saved['forbidden'])!=model.forbidden or saved['connectors']!=model.connectors:
            raise ValueError('Model metadata mismatch')
        if Q(saved['background_bound'])!=backgrounds[model.name]:
            raise ValueError('Background bound mismatch')
    for c in data['candidates']:
        if 'witnesses' not in c: continue
        m,n=models[c['left']],models[c['right']]
        J=[Q(x)-3 for x in c['probe_interval']]
        bound=max(backgrounds[m.name],backgrounds[n.name],interface_bound(c['u'],c['v']))
        if bound!=Q(c['dominance_bound']) or not Q('4.1')<=J[0]+3<J[1]+3<=Q('4.52') or not J[0]+3>bound:
            raise ValueError('Invalid Lagrange dominance bound or target interval')
        expected={str(J[0]+(J[1]-J[0])*k/(data['config']['points']-1)) for k in range(data['config']['points'])}
        actual=[w['target'] for w in c['witnesses']]+c['unresolved_points']
        if len(actual)!=len(expected) or set(actual)!=expected: raise ValueError('Missing or duplicate targets')
        for w in c['witnesses']:
            a,b=certify_witness(m,w['u'],c['u']);x,y=certify_witness(n,w['v'],c['v'])
            t=Q(w['target']);error=max(abs(a+x-t),abs(b+y-t))
            if error!=Q(w['error_upper']) or error>=Q(1,10**data['config']['exponent']):
                raise ValueError('Invalid error certificate')
            count+=1
    print(f'Replayed {count} exact rational witness checks')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--radius',type=int,default=4)
    p.add_argument('--per-pair',type=int,default=3)
    p.add_argument('--verify-count',type=int,default=60)
    p.add_argument('--window-width',type=float,default=2e-5)
    p.add_argument('--epsilons',type=float,nargs='+',default=[1e-6,1e-7,1e-8])
    p.add_argument('--budget',type=int,default=200000)
    p.add_argument('--point-budget',type=int,default=20000)
    p.add_argument('--points',type=int,default=21)
    p.add_argument('--exponent',type=int,default=30)
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('results.json'))
    p.add_argument('--replay',type=Path)
    args=p.parse_args()
    if args.replay: replay(args.replay);return
    if args.radius<1 or args.points<2 or not 1<=args.exponent<=50 or args.per_pair<1 or args.verify_count<1 or min(args.epsilons)<1e-12 or args.window_width<=0 or min(args.budget,args.point_budget)<1:
        p.error('Require positive budgets, radius/per-pair/verify-count, points >= 2, exponent 1..50, epsilon >= 1e-12, positive window width')
    run(args)

if __name__=='__main__': main()
