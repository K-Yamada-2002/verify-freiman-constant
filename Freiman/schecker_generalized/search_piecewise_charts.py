#!/usr/bin/env python3
"""Repair a failed uniform cover by subdividing its parameter guard only.

All pieces must cover the original target interval. Piece geometries do not
become induction assumptions; dependencies remain proper digit extensions.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from chart_geometry import Domain
from finite_type_game import Game
from learn_small_type_menu import template_labels
from search_chart_types import ChartSearch, engine_hash
from search_cyclic_types import fl
from type_graph_geometry import Cell
from verify_piecewise_charts import FORMAT, PiecewiseVerifier


STATE_FORMAT = 'freiman-piecewise-chart-search-state-v1'


class PiecewiseSearch(ChartSearch):
    def __init__(self, labels, partition_depth=2, **kwargs):
        self.partition_depth = partition_depth
        self.partition_levels, self.seed_rules = {}, {}
        self.partition_statistics = dict(attempts=0, accepted=0, pieces=0, exact_rejected=0,axis_trials=0)
        super().__init__(labels, **kwargs)

    def register(self, domain):
        if domain.base not in self.base_ids:
            c = domain.base
            self.base_ids[c] = len(self.routing.cells)
            self.routing.cells.append(c)
            self.routing.floatcells.append((tuple(map(fl,c.r)), tuple(map(fl,c.s)),
                tuple(map(fl,c.ratio)), tuple(map(fl,c.anchors()))))
        return super().register(domain)

    def axes(self,cid):
        base=self.cells[cid].base
        rb,sb,qb=(tuple(map(fl,b)) for b in (base.r,base.s,base.ratio))
        a,b=map(fl,base.anchors())
        widths=((rb[1]-rb[0])/(1+a*sum(rb)/2),(sb[1]-sb[0])/(1+b*sum(sb)/2),
                (qb[1]-qb[0])/(sum(qb)/2))
        bounds=(base.r,base.s,base.ratio)
        return [i for i in sorted(range(3),key=lambda i:widths[i],reverse=True) if bounds[i][0]!=bounds[i][1]]

    def split(self, cid, axis=None):
        domain = self.cells[cid]
        level = self.partition_levels.get(cid, 0)
        if level >= self.partition_depth:
            return []
        base = domain.base
        if axis is None:
            axes=self.axes(cid)
            if not axes:
                return []
            axis=axes[0]
        bounds = [base.r,base.s,base.ratio]
        low,high = bounds[axis]
        if low == high:
            return []
        middle = (low+high)/2
        result = []
        for bound in ((low,middle),(middle,high)):
            part = list(bounds);part[axis] = bound
            c = Cell(base.states,base.parity,base.high,*part)
            j = self.register(Domain(c,domain.words,domain.high))
            self.partition_levels[j] = max(self.partition_levels.get(j,0),level+1)
            result.append(j)
        return result

    def leaf_plans(self, key, memo=None, try_uniform=True):
        if memo is None:
            memo={}
        if key in memo:
            return memo[key]
        cid,lo,hi = key
        points = self.points(cid)
        # Avoid marking an unregistered geometry probe as a permanent game
        # rejection. These conditions also make further subdivision futile
        # when a sampled point already lies in a gap.
        if not self.ge(cid,points[hi][0],points[lo][0]) or not self.outer_possible(key):
            memo[key]=None
            return None
        proposal = self._plan_once(key,self.game.rejected) if try_uniform else None
        if proposal is not None:
            memo[key]=[(key,proposal)]
            return memo[key]
        for axis in self.axes(cid):
            children=self.split(cid,axis)
            if not children:
                continue
            self.partition_statistics['axis_trials']+=1
            result=[]
            for child in children:
                leaves=self.leaf_plans((child,lo,hi),memo)
                if leaves is None:
                    break
                result.extend(leaves)
            else:
                memo[key]=result
                return result
        memo[key]=None
        return None

    def guarded_proposal(self, key, leaves):
        pieces = [dict(cell=k[0],children=proposal[0]) for k,proposal in leaves]
        dependencies = list(dict.fromkeys(d for _,p in leaves for d in p[1]))
        return dict(pieces=pieces),dependencies

    def planner(self, key, rejected):
        if key in self.seed_rules:
            proposal = self.seed_rules[key]
            if not any(rejected(k) for k in proposal[1]):
                return copy.deepcopy(proposal)
        proposal = super().planner(key,rejected)
        if proposal is not None or key in self.game.permanent_rejections:
            return proposal
        self.partition_statistics['attempts'] += 1
        leaves=self.leaf_plans(key,try_uniform=False)
        if leaves is None:
            return None
        proposal = self.guarded_proposal(key,leaves)
        # Check this implication independently before retaining any helper
        # rule. The test graph's open children are deliberately not assumed
        # filled and its roots are not used as A_n seeds.
        probe = Game([key])
        for child in proposal[1]:
            probe.add(child)
        probe.entries[0].update(status='local',plan=proposal[0],children=[probe.ids[k] for k in proposal[1]])
        try:
            PiecewiseVerifier(self.certificate(probe)).local(0)
        except ValueError:
            self.partition_statistics['exact_rejected'] += 1
            return None
        for helper,p in leaves:
            if helper in proposal[1]:
                self.seed_rules[helper] = p
        self.partition_statistics['accepted'] += 1
        self.partition_statistics['pieces'] += len(leaves)
        return proposal

    def certificate(self, game):
        reached = sorted(game.reachable())
        ids = {j:i for i,j in enumerate(reached)}
        used = {game.keys[j][0] for j in reached}
        for j in reached:
            e = game.entries[j]
            if e['status']=='local' and isinstance(e['plan'],dict):
                used.update(p['cell'] for p in e['plan']['pieces'])
        used = sorted(used); cids = {j:i for i,j in enumerate(used)}
        def edges(plan):
            return [dict(e,destinations=[dict(node=ids[game.ids[d['key']]],swap=d['swap'])
                    for d in e['destinations']]) for e in plan]
        nodes = []
        for j in reached:
            cid,lo,hi = game.keys[j]; entry=game.entries[j]; points=self.points(cid)
            lower,upper=template_labels(self.cells[cid].states,points[lo][2],points[hi][2],self.shape_menu)
            row=dict(cell=cids[cid],lower=lower,upper=upper,children=[])
            if entry['status']=='local':
                if isinstance(entry['plan'],dict):
                    row['pieces']=[dict(cell=cids[p['cell']],children=edges(p['children']))
                                   for p in entry['plan']['pieces']]
                else:
                    row['children']=edges(entry['plan'])
            nodes.append(row)
        return dict(format=FORMAT,cells=[self.cells[i].record() for i in used],nodes=nodes,
                    roots=dict(zip(('zero','positive'),(ids[i] for i in game.roots))),search=game.summary(),
                    partition_statistics=self.partition_statistics)

    def snapshot(self, game, configuration, fingerprint):
        state = super().snapshot(game,configuration,fingerprint)
        state.update(format=STATE_FORMAT,partition_levels=sorted(self.partition_levels.items()),
                     partition_statistics=self.partition_statistics,
                     seed_rules=[dict(key=k,plan=p[0],children=p[1]) for k,p in self.seed_rules.items()])
        return state


def fingerprint():
    here=Path(__file__).parent
    return hashlib.sha256(engine_hash().encode()+(here/'search_piecewise_charts.py').read_bytes()+
                          (here/'verify_piecewise_charts.py').read_bytes()).hexdigest()


def restore(state, depth=2):
    from fractions import Fraction
    old_format=state['format']=='freiman-chart-search-state-v1'
    if not old_format and state['format']!=STATE_FORMAT:
        raise ValueError('unknown saved search format')
    config=dict(state['configuration'])
    config['partition_depth']=config.get('partition_depth',depth)
    for key in ('base','balance'):
        config[key]=Fraction(config[key])
    search=PiecewiseSearch(state['labels'],**config,shape_menu=state['shape_menu'])
    search.cells,search.floatcells,search.domain_ids=[],[],{}
    for d in state['domains']:
        search.register(Domain.read(d))
    search.partition_levels=dict(state.get('partition_levels',[]))
    search.partition_statistics=dict(state.get('partition_statistics',search.partition_statistics))
    search.partition_statistics.setdefault('axis_trials',0)
    for row in state.get('seed_rules',[]):
        plan=copy.deepcopy(row['plan'])
        for edge in plan:
            for dest in edge['destinations']:
                dest['key']=tuple(dest['key'])
        search.seed_rules[tuple(row['key'])]=(plan,list(map(tuple,row['children'])))
    game=Game.restore(state['game']);search.game=game
    search.shape_learning=state['shape_learning']
    search.state_upgrades=list(state.get('state_upgrades',[]))
    for cid,lo,hi in game.keys:
        if not (0<=cid<len(search.cells) and 0<=lo<len(search.points(cid)) and 0<=hi<len(search.points(cid))):
            raise ValueError('invalid saved type index')
    if old_format or state['engine_hash']!=fingerprint():
        all_game=copy.deepcopy(game)
        all_game.roots += [i for i in range(len(game.keys)) if i not in game.roots]
        audit=PiecewiseVerifier(search.certificate(all_game)).audit()
        if audit['failed_rules']:
            raise ValueError('saved local rule failed migration audit')
        search.seed_rules.clear()
        game.permanent_rejections.clear()
        reopened=game.forget_rejections()
        search.state_upgrades.append(dict(previous_hash=state['engine_hash'],new_hash=fingerprint(),
                   verified_local_rules=len(audit['verified_rules']),reopened=reopened))
    return search,game,{k:str(v) if isinstance(v,Fraction) else v for k,v in config.items()}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('state',type=Path)
    ap.add_argument('--partition-depth',type=int,default=2)
    ap.add_argument('--seconds',type=float,default=180)
    ap.add_argument('--max-steps',type=int,default=2000)
    ap.add_argument('--max-types',type=int,default=12000)
    ap.add_argument('--native-executable',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if args.partition_depth<0 or args.seconds<=0 or args.max_steps<=0 or args.max_types<2:
        ap.error('invalid bounds')
    search,game,config=restore(json.loads(args.state.read_text()),args.partition_depth)
    digest=fingerprint()
    if args.native_executable:
        search.native_executable=args.native_executable.resolve()
    def checkpoint(g):
        graph=search.certificate(g)
        graph.update(settings=dict(configuration=config,source_state=str(args.state),engine_hash=digest),
                     state_upgrades=search.state_upgrades)
        graph['search']['closed_supported_types']=len(g.supported())
        def save(path,text):
            temporary=path.with_suffix(path.suffix+'.tmp')
            temporary.write_text(text)
            temporary.replace(path)
        save(args.output,json.dumps(graph,indent=2)+'\n')
        save(args.output.with_suffix('.state.json'),json.dumps(search.snapshot(g,config,digest),separators=(',',':'))+'\n')
        print(json.dumps(dict(search=g.summary(),partition=search.partition_statistics)),flush=True)
    checkpoint(game)
    try:
        game.run(search.planner,max_types=args.max_types,max_steps=game.steps+args.max_steps,
                 seconds=args.seconds,checkpoint=lambda g:checkpoint(g) if g.steps%500==0 else None)
    except KeyboardInterrupt:
        game.stop='interrupted; all open obligations retained'
    finally:
        search.close_native()
    checkpoint(game)
    checker=PiecewiseVerifier(json.loads(args.output.read_text()));audit=checker.audit()
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    print(json.dumps(dict(local=len(audit['verified_rules']),open=len(audit['open_nodes']),failed=len(audit['failed_rules']))),flush=True)
    try:
        result=checker.closed()
    except ValueError as error:
        args.output.with_suffix('.verified.json').unlink(missing_ok=True)
        print(json.dumps(dict(closed=False,reason=str(error))),flush=True)
    else:
        args.output.with_suffix('.verified.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result),flush=True)


if __name__=='__main__':
    main()
