#!/usr/bin/env python3
"""Try certified returns to saved charts, not only roots/self/coarse boxes.

The finite return catalog and its ordering are discovery heuristics. Every
image containment and final local rule is checked independently. Failure is
not nonexistence; the separate universal enumeration checkpoint is unchanged.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path

from chart_geometry import relative_box
from contract_cyclic_domains import domains
from search_cyclic_types import fl
from search_piecewise_charts import PiecewiseSearch, fingerprint, restore
from verify_piecewise_charts import PiecewiseVerifier


class KnownReturnSearch(PiecewiseSearch):
    def initialize_returns(self, cids=None, limit=8):
        self.return_limit = limit
        self.return_catalog = list(cids if cids is not None else
                                   dict.fromkeys(k[0] for k in self.game.keys))
        local = {k[0] for k,e in zip(self.game.keys,self.game.entries) if e['status']=='local'}
        self.return_groups = defaultdict(list)
        for cid in sorted(self.return_catalog, key=lambda i:(i not in local,i)):
            d = self.cells[cid]
            self.return_groups[d.states,d.parity,d.high].append(cid)
        self.return_statistics = dict(candidates=0, exact_checks=0, accepted_routes=0)
        self.moves.cache_clear()
        self.native_geometry.cache_clear()

    def child_routes(self, cid, u, v, high):
        child = self.cells[cid].extend(u,v,high)
        outer = child.outer
        image = (child.states, child.parity, child.high,
                 tuple(map(fl,outer.r)),tuple(map(fl,outer.s)),tuple(map(fl,outer.ratio)))
        accepted = 0
        for swap in (False,True):
            actual = child.exchange() if swap else child
            abox = [tuple(map(fl,b)) for b in domains(actual.outer)]
            for target_id in self.return_groups[actual.states,actual.parity,actual.high]:
                if target_id in (0,1,cid):
                    continue  # The ordinary search already keeps these returns.
                self.return_statistics['candidates'] += 1
                target = self.cells[target_id]
                tbox = self.floatcells[target_id][:3]
                # Only a discovery filter; all selected containments are exact.
                if any(a < lo-1e-12 or b > hi+1e-12
                       for (a,b),(lo,hi) in zip(abox,tbox)):
                    continue
                self.return_statistics['exact_checks'] += 1
                box = relative_box(actual,target)
                if box is not None and all(a<=lo<=hi<=b for (a,b),(lo,hi)
                                          in zip(domains(target.base),domains(box))):
                    self.return_statistics['accepted_routes'] += 1
                    accepted += 1
                    yield image, [(target_id,swap)]
                    if accepted >= self.return_limit:
                        break
            if accepted >= self.return_limit:
                break
        yield from super().child_routes(cid,u,v,high)


def engine_hash():
    return hashlib.sha256(fingerprint().encode()+Path(__file__).read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('state',type=Path)
    ap.add_argument('--seconds',type=float,default=300)
    ap.add_argument('--max-steps',type=int,default=2000)
    ap.add_argument('--max-types',type=int,default=12000)
    ap.add_argument('--return-limit',type=int,default=8)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if min(args.seconds,args.max_steps,args.max_types,args.return_limit)<=0:
        ap.error('positive budgets required')
    state=json.loads(args.state.read_text())
    search,game,config=restore(state)
    search.__class__=KnownReturnSearch
    same=state.get('return_engine_hash')==engine_hash() and state.get('return_limit')==args.return_limit
    if not same:
        game.permanent_rejections.clear()
        game.forget_rejections()
        search.failed_intervals.clear()
        search.seed_rules.clear()
    search.initialize_returns(state.get('return_catalog') if same else None,args.return_limit)
    if same:
        search.return_statistics.update(state['return_statistics'])
    def save():
        graph=search.certificate(game)
        graph['return_statistics']=search.return_statistics
        saved=search.snapshot(game,config,fingerprint())
        saved.update(return_engine_hash=engine_hash(),return_catalog=search.return_catalog,
                     return_limit=args.return_limit,return_statistics=search.return_statistics)
        for path,data in ((args.output,graph),(args.output.with_suffix('.state.json'),saved)):
            temp=path.with_suffix('.tmp')
            temp.write_text(json.dumps(data,separators=(',',':'))+'\n');temp.replace(path)
        print(json.dumps(dict(search=game.summary(),returns=search.return_statistics)),flush=True)
        return graph
    save()
    try:
        game.run(search.planner,seconds=args.seconds,max_steps=game.steps+args.max_steps,
                 max_types=args.max_types,checkpoint=lambda g:save())
    finally:
        search.close_native()
    graph=save();checker=PiecewiseVerifier(graph);audit=checker.audit()
    if audit['failed_rules']:
        raise ValueError('return search failed independent local audit')
    args.output.with_suffix('.audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    try:
        verdict=checker.closed()
    except ValueError as error:
        verdict=dict(closed=False,reason=str(error))
    else:
        args.output.with_suffix('.verified.json').write_text(json.dumps(verdict,indent=2)+'\n')
    print(json.dumps(verdict),flush=True)


if __name__=='__main__':
    main()
