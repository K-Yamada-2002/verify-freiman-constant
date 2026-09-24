#!/usr/bin/env python3
"""Goal-directed finite induction with automatic type refinement/backtracking.

Failed child obligations are split into the regions covered by their current
successors. These regions become new endpoint types and the parent is retried.
No shape count or endpoint-word length is fixed. A finite digit horizon is
certified; terminal intervals are explicitly unproved for infinite filling.
"""
import argparse
import copy
import json
from pathlib import Path

from adaptive_types import (AdaptiveSearch, TypeRegistry, full_labels, ge,
                            lifted, point, simplify, verify_row, word_pair,Q,
                            uniform_width_ratio,label_value)
from invariant_boxes import suffix_pairs, suffix_state,ALL_TYPE_LABELS
from explore import state_of
from search_types import Search


def contains(u,v,outer,inner,regime):
    return ge(u,v,inner[0],outer[0],regime) and ge(u,v,outer[1],inner[1],regime)


class Synthesis:
    def __init__(self,gap_depth=4,max_step=2,regime='all',max_families=2000,seed=None):
        self.search=AdaptiveSearch(gap_depth,max_step=max_step,regime=regime)
        self.regime,self.max_step,self.max_families=regime,max_step,max_families
        self.domains={};self.checked_leaves=set();self.proven={};self.nodes=[]
        self.refinements=[];self.attempts=0
        self.numeric=Search(ratio_bound=20)
        self.seeds={}
        if seed is not None:
            # Seed rules only propose labels and priorities. Every resulting
            # edge and node is proved again in the requested parameter regime.
            if 'partial_local_rules' in seed:
                rows=seed['partial_local_rules']
                for row in rows:verify_row(row,seed['max_step'])
            else:
                verify(seed)
                cases=seed.get('cases',[seed])
                rows=[r for c in cases for r in c['nodes']]
            for row in rows:
                if row['children']:
                    self.seeds.setdefault((row['left_suffix'],row['right_suffix']),[]).append(row)

    def domain(self,key):
        if key not in self.domains:
            if len(self.domains)>=self.max_families:
                raise RuntimeError('family budget reached; saved nodes do not close induction')
            self.domains[key]=(self.search.options(*key[:2]) if key[:2] in self.search.known
                               else (full_labels(*key[:2]),))
        return self.domains[key]

    def offers(self,key):
        u,v,depth=key;left,right=word_pair(u,v)
        offers=[]
        for du,dv in suffix_pairs(suffix_state(left),suffix_state(right),self.max_step):
            childkey=u+du,v+dv,max(0,depth-len(du)-len(dv))
            # Discovery guard against repeatedly lengthening only one side.
            # Its role is search control, not a claim of admissibility.
            if any(not 1/20<=self.numeric.parameters(*word_pair(*childkey[:2],n))[-1]<=20
                   for n in self.search.samples):
                continue
            for pair in self.domain(childkey):
                a,b=(lifted(du,dv,z) for z in pair)
                ep=self.search.ordered(u,v,a,b)
                if ep is not None:
                    offers.append({'key':childkey,'suffixes':(du,dv),
                                   'endpoints':pair,'mapped':ep})
        for seed_id,row in enumerate(self.seeds.get((u,v),())):
            for child in row['children']:
                du,dv=child['suffixes']
                if len(du)+len(dv)>self.max_step:continue
                childkey=u+du,v+dv,max(0,depth-len(du)-len(dv))
                if any(not 1/20<=self.numeric.parameters(*word_pair(*childkey[:2],n))[-1]<=20
                       for n in self.search.samples):continue
                pair=self.search.ordered(*childkey[:2],*(tuple(z) for z in child['endpoints']))
                if pair is None:continue
                if not any(contains(*childkey[:2],z,pair,self.regime) for z in self.domain(childkey)):continue
                ep=self.search.ordered(u,v,*(lifted(du,dv,z) for z in pair))
                if ep is not None:
                    offers.append({'key':childkey,'suffixes':(du,dv),'endpoints':pair,
                                   'mapped':ep,'seed':seed_id})
        return sorted(offers,key=lambda o:point(u,v,o['mapped'][1]),reverse=True)

    def chain(self,key,target,offers):
        """Search all reachable upper endpoints, not just one greedy branch."""
        for seed_id in range(len(self.seeds.get(key[:2],()))):
            indices=[i for i,o in enumerate(offers) if o.get('seed')==seed_id]
            if not indices:continue
            path=self._chain(key,target,[offers[i] for i in indices])
            if path is not None:return tuple(indices[i] for i in path)
        return self._chain(key,target,offers)

    def _chain(self,key,target,offers):
        u,v,_=key;stack=[(target[0],())];seen={target[0]}
        while stack:
            current,path=stack.pop()
            if ge(u,v,current,target[1],self.regime):return path
            next_states=[]
            for i,o in enumerate(offers):
                lo,hi=o['mapped']
                if hi in seen:continue
                if (ge(u,v,current,lo,self.regime) and ge(u,v,hi,current,self.regime)
                        and not ge(u,v,current,hi,self.regime)):
                    seen.add(hi);next_states.append((hi,path+(i,)))
            # A large upper endpoint is tried first; alternatives remain.
            stack.extend(reversed(next_states))
        return None

    def refined_domain(self,key,offers):
        u,v,_=key;old=self.domain(key)
        parts=[]
        for o in offers:
            a,b=(simplify(u,v,z) for z in o['mapped'])
            for lo,hi in old:
                if ge(u,v,a,lo,self.regime):aa=a
                elif ge(u,v,lo,a,self.regime):aa=lo
                else:continue
                if ge(u,v,hi,b,self.regime):bb=b
                elif ge(u,v,b,hi,self.regime):bb=hi
                else:continue
                if ge(u,v,bb,aa,self.regime) and not ge(u,v,aa,bb,self.regime):
                    parts.append((aa,bb))
        parts=sorted(set(parts),key=lambda z:point(u,v,z[0]))
        merged=[]
        for a,b in parts:
            if merged and ge(u,v,merged[-1][1],a,self.regime):
                if ge(u,v,b,merged[-1][1],self.regime):
                    merged[-1]=(merged[-1][0],b)
                    continue
                if ge(u,v,merged[-1][1],b,self.regime) and ge(u,v,a,merged[-1][0],self.regime):
                    continue
            merged.append((a,b))
        # Successfully replayable finite proofs remain usable even if the
        # conservative domain computation drops them through interval ordering.
        for (proved_key,pair),_ in self.proven.items():
            if proved_key==key and not any(contains(u,v,z,pair,self.regime) for z in merged):
                merged.append(pair)
        for pair in merged:self.search.registry.register(pair)
        return tuple(merged)

    def add_node(self,key,target,children):
        u,v,depth=key
        row={'left_suffix':u,'right_suffix':v,'endpoints':target,
             'type':self.search.registry.register(target),'regime':self.regime,
             'remaining_depth':depth,'children':children}
        if children:verify_row(row,self.max_step)
        index=len(self.nodes);self.nodes.append(row);self.proven[key,target]=index
        return index

    def solve(self,key,target):
        if (key,target) in self.proven:return self.proven[key,target]
        u,v,depth=key;self.attempts+=1
        if self.attempts%100==0:
            print('attempts',self.attempts,'families',len(self.domains),
                  'new types',len(self.search.registry.types),'refinements',len(self.refinements),flush=True)
        if depth==0 and key not in self.checked_leaves:
            self.domains[key]=self.search.options(u,v)
            self.checked_leaves.add(key)
        if not any(contains(u,v,z,target,self.regime) for z in self.domain(key)):
            return None
        if depth==0:return self.add_node(key,target,[])
        while True:
            offers=self.offers(key)
            path=self.chain(key,target,offers)
            if path is None:
                previous=self.domain(key)
                revised=self.refined_domain(key,offers)
                if any(contains(u,v,z,target,self.regime) for z in revised):
                    raise AssertionError('refinement unexpectedly retains the failed target')
                self.domains[key]=revised
                self.refinements.append({'family':key,'rejected':target,
                                         'before':previous,'after':revised})
                return None
            children=[]
            for i in path:
                offer=offers[i]
                child=self.solve(offer['key'],offer['endpoints'])
                if child is None:break
                children.append({'node':child,'suffixes':offer['suffixes'],
                                 'endpoints':offer['endpoints'],
                                 'type':self.search.registry.register(offer['endpoints'])})
            else:return self.add_node(key,target,children)

    def certificate(self,root,depth):
        reached=set()
        def visit(i):
            if i in reached:return
            reached.add(i)
            for c in self.nodes[i]['children']:visit(c['node'])
        if root is not None:visit(root)
        indices={old:new for new,old in enumerate(sorted(reached))}
        nodes=[]
        for old in sorted(reached):
            n=dict(self.nodes[old]);n['children']=[dict(c,node=indices[c['node']]) for c in n['children']]
            nodes.append(n)
        result={'status':'exact finite uniform adaptive certificate; terminal filledness UNPROVED',
                'horizon_unit':'total appended digits','depth':depth,'regime':self.regime,
                'max_step':self.max_step,'root':indices.get(root),'nodes':nodes,
                'uniform_width_ratio_bound':21,
                'types':self.search.registry.types,
                'discovery':{'gap_depth':self.search.gap_depth,'samples':self.search.samples,
                             'sampled_width_ratio_bound':20,
                             'attempts':self.attempts,'families':len(self.domains),
                             'leaf_gap_checks':len(self.checked_leaves),
                             'backtracking_refinements':self.refinements,
                             'gap_driven_type_additions':self.search.discoveries}}
        if root is None:
            result['status']='incomplete search; saved local rules are proposals, not a root certificate'
            # Do not discard expensive verified local comparisons when a
            # higher obligation fails or a discovery budget is exhausted.
            result['partial_local_rules']=[]
            for row in self.nodes:
                if not row['children']:continue
                local={k:v for k,v in row.items() if k not in ('type','remaining_depth')}
                local['children']=[{'suffixes':c['suffixes'],'endpoints':c['endpoints']}
                                   for c in row['children']]
                result['partial_local_rules'].append(local)
        return result


def verify(data):
    if 'cases' in data:
        return verify_cases(data)
    assert data['horizon_unit']=='total appended digits'
    assert data['regime'] in ('all','zero','positive')
    assert data['max_step'] in (1,2)
    assert isinstance(data['depth'],int) and data['depth']>=1
    nodes=data['nodes'];root=data['root']
    assert isinstance(root,int) and 0<=root<len(nodes)
    assert nodes[root]['left_suffix']==nodes[root]['right_suffix']==''
    assert tuple(tuple(z) for z in nodes[root]['endpoints'])==full_labels('','')
    assert nodes[root]['remaining_depth']==data['depth']
    reached=set();leaves=0
    def visit(i):
        nonlocal leaves
        if i in reached:return
        reached.add(i);row=nodes[i]
        u,v=row['left_suffix'],row['right_suffix'];depth=row['remaining_depth']
        assert row['regime']==data['regime'] and isinstance(depth,int) and depth>=0
        assert uniform_width_ratio(u,v,data.get('uniform_width_ratio_bound',21),row['regime'])
        a,b=(tuple(z) for z in row['endpoints'])
        assert ge(u,v,b,a,row['regime']) and not ge(u,v,a,b,row['regime'])
        type_index,reflected=row['type']
        assert isinstance(type_index,int) and 0<=type_index<len(data['types'])
        assert isinstance(reflected,bool)
        labels=tuple(tuple(z) for z in data['types'][type_index])
        if reflected:labels=tuple(z[2:]+z[:2] for z in labels)
        assert tuple(sorted((a,b)))==tuple(sorted(labels))
        if not depth:
            assert not row['children'];leaves+=1;return
        assert row['children'];verify_row(row,data['max_step'])
        for child in row['children']:
            j=child['node'];assert isinstance(j,int) and 0<=j<len(nodes)
            target=nodes[j];du,dv=child['suffixes']
            assert target['left_suffix']==u+du and target['right_suffix']==v+dv
            assert target['remaining_depth']==max(0,depth-len(du)-len(dv))
            assert target['endpoints']==child['endpoints']
            visit(j)
    visit(root);assert len(reached)==len(nodes)
    return {'verified_nodes':len(nodes),'verified_edges':sum(len(n['children']) for n in nodes),
            'unproved_terminal_intervals':leaves,
            'selected_types':len({tuple(n['type']) for n in nodes}),
            'uniform_width_ratio_bound':data.get('uniform_width_ratio_bound',21),
            'max_endpoint_word_length':max(len(z[j]) for n in nodes for z in n['endpoints'] for j in (0,2))}


def verify_cases(data):
    """Cover every n>=0 with two independently replayed finite proofs."""
    assert data['regime']=='all'
    assert data['horizon_unit']=='total appended digits'
    cases=data['cases']
    assert len(cases)==2 and {c['regime'] for c in cases}=={'zero','positive'}
    assert all('cases' not in c and c['depth']==data['depth'] for c in cases)
    results={c['regime']:verify(c) for c in cases}
    return {'all_nonnegative_exponents_verified':True,'depth':data['depth'],
            'cases':results,
            'verified_nodes':sum(r['verified_nodes'] for r in results.values()),
            'verified_edges':sum(r['verified_edges'] for r in results.values()),
            'unproved_terminal_intervals':sum(r['unproved_terminal_intervals'] for r in results.values()),
            'uniform_width_ratio_bound':max(r['uniform_width_ratio_bound'] for r in results.values())}


def combine_cases(cases):
    data={'status':'exact finite parameter-case certificate; terminal filledness UNPROVED',
          'horizon_unit':'total appended digits','regime':'all',
          'depth':cases[0]['depth'],'cases':cases}
    data['verification']=verify(data)
    return data


def audit_obstructions(data,obstructions):
    """Report any selected interval that still contains a known exact gap."""
    if 'cases' in data:
        return [dict(row,regime=case['regime']) for case in data['cases']
                for row in audit_obstructions(case,obstructions)]
    from type_certificates import endpoint
    violations=[]
    for i,node in enumerate(data['nodes']):
        u,v=node['left_suffix'],node['right_suffix']
        for row in obstructions:
            if (data['regime']=='positive' and row['n']==0) or (data['regime']=='zero' and row['n']!=0):
                continue
            if (u,v)!=(row['left_suffix'],row['right_suffix']):continue
            left,right=word_pair(u,v,row['n'])
            lo,hi=sorted(endpoint(left,right,z) for z in node['endpoints'])
            a,b=(Q(z['a'],z['b']) for z in row['gap'])
            if max(lo,a)<min(hi,b):
                violations.append({'node':i,'family':[u,v],'obstruction_kind':row['kind']})
    return violations


def summarize_types(data):
    state_types=set();new_nodes=[];new_shapes=set()
    for i,row in enumerate(data['nodes']):
        u,v=row['left_suffix'],row['right_suffix']
        left,right=word_pair(u,v)
        state_types.add((state_of(left),state_of(right),(-1)**(len(left)+len(right)),*row['type']))
        values={label_value(u,v,tuple(z)) for z in row['endpoints']}
        old=False
        for pattern in (full_labels(u,v),)+ALL_TYPE_LABELS[1:]:
            try:match={label_value(u,v,tuple(z)) for z in pattern}
            except ValueError:continue
            if values==match:old=True;break
        if not old:
            new_nodes.append(i);new_shapes.add(row['type'][0])
    return {'shapes_up_to_reflection':len({r['type'][0] for r in data['nodes']}),
            'oriented_shapes':len({tuple(r['type']) for r in data['nodes']}),
            'state_parity_types':len(state_types),
            'nodes_using_endpoints_outside_the_old_eight_shapes':len(new_nodes),
            'new_shape_ids':sorted(new_shapes),'example_new_nodes':new_nodes[:5]}


def compact(data):
    """Keep the replayable proof and compact discovery statistics."""
    out=copy.deepcopy(data)
    used=sorted({r['type'][0] for r in out['nodes']})
    renumber={old:new for new,old in enumerate(used)}
    for row in out['nodes']:
        row['type']=[renumber[row['type'][0]],row['type'][1]]
        for child in row['children']:
            child['type']=[renumber[child['type'][0]],child['type'][1]]
    out['types']=[out['types'][i] for i in used]
    discovery=out['discovery']
    discovery['generated_shapes']=len(data['types'])
    for name in ('backtracking_refinements','gap_driven_type_additions'):
        if isinstance(discovery.get(name),list):
            rows=discovery.pop(name)
            discovery[name+'_count']=len(rows)
            discovery[name+'_examples']=rows[:2]
    return out


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--depth',type=int,default=4)
    ap.add_argument('--gap-depth',type=int,default=4)
    ap.add_argument('--max-step',type=int,choices=(1,2),default=2)
    ap.add_argument('--regime',choices=('all','zero','positive'),default='all')
    ap.add_argument('--max-families',type=int,default=5000)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--verify',type=Path)
    ap.add_argument('--combine',type=Path,nargs=2,metavar=('ZERO','POSITIVE'),
                    help='combine exact n=0 and n>=1 certificates into an all-n certificate')
    ap.add_argument('--seed',type=Path,help='reuse the local rules of an earlier verified certificate')
    ap.add_argument('--trace',type=Path,help='optional full discovery trace, separate from the proof')
    args=ap.parse_args()
    if args.verify:
        print(json.dumps(verify(json.loads(args.verify.read_text())),indent=2));return
    if args.combine:
        data=combine_cases([json.loads(path.read_text()) for path in args.combine])
        if args.output:args.output.write_text(json.dumps(data,indent=2)+'\n')
        print(json.dumps(data['verification'],indent=2));return
    seed=json.loads(args.seed.read_text()) if args.seed else None
    synthesis=Synthesis(args.gap_depth,args.max_step,args.regime,args.max_families,seed)
    failure=None
    try:root=synthesis.solve(('', '',args.depth),full_labels('',''))
    except (RuntimeError,KeyboardInterrupt) as exc:
        root=None;failure=str(exc) or 'search interrupted; partial local rules saved'
    data=synthesis.certificate(root,args.depth)
    data['discovery']['seed']=str(args.seed) if args.seed else None
    if root is not None:
        data['verification']=verify(data)
        data['known_obstruction_violations']=audit_obstructions(data,
            [row for rows in synthesis.search.known.values() for row in rows])
    else:data['failure']=failure or 'root not covered by the current uniform candidates'
    if args.trace:args.trace.write_text(json.dumps(data,indent=2)+'\n')
    data=compact(data)
    if root is not None:data['type_summary']=summarize_types(data)
    if args.output:args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data.get('verification',{'failure':data.get('failure')}),indent=2))


if __name__=='__main__':main()
