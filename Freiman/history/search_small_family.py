"""Propose <=253*k rectangular predicates inside an existing saved family.

A proposal is NOT a certificate. graph_kernel_reduce must check closure;
rows lost on replay must never be called admissible.
"""
import argparse,json
from pathlib import Path
from layout import DATA


def largest_rectangle(matrix, uncovered=None):
    if not matrix:return None
    width=len(matrix[0]);heights=[0]*width;best=None;area=0
    prefix=None
    if uncovered is not None:
        prefix=[[0]*(width+1)]
        for values in uncovered:
            sums=[0]; running=0
            for col,value in enumerate(values):
                running+=value;sums.append(running+prefix[-1][col+1])
            prefix.append(sums)
    for row,values in enumerate(matrix):
        heights=[h+1 if v else 0 for h,v in zip(heights,values)]
        stack=[]
        for col in range(width+1):
            h=heights[col] if col<width else 0
            start=col
            while stack and stack[-1][1]>h:
                left,height=stack.pop();start=left
                score=height*(col-left) if prefix is None else (
                    prefix[row+1][col]-prefix[row-height+1][col]
                    -prefix[row+1][left]+prefix[row-height+1][left])
                if score>area:area=score;best=(row-height+1,row,left,col-1)
            if not stack or stack[-1][1]<h:stack.append((start,h))
    return best


def propose(source,name,count,overlap=False):
    meta=json.loads((DATA/(source+'.meta.json')).read_text())
    raw=(DATA/(source+'.json.alive.bin')).read_bytes()
    S=len(meta['side_keys']);T=len(meta['types']);B=meta['high']-meta['low']+1
    out=bytearray(len(raw));rows=[]
    for a in range(S):
        for b in range(a,S):
            geom=a*S+b;stop=B//2 if a==b else B
            matrix=[list(raw[(geom*B+k)*T:(geom*B+k+1)*T]) for k in range(stop)]
            uncovered=[row[:] for row in matrix] if overlap else matrix
            # 231 off-diagonal pairs * 4 + 22 diagonal pairs * 3 = 990.
            local_count = min(count, 3) if a == b else count
            for _ in range(local_count):
                rect=largest_rectangle(matrix,uncovered if overlap else None)
                if rect is None:break
                lo,hi,first,last=rect
                rows.append([a,b,lo+meta['low'],hi+meta['low'],first,last])
                for k in range(lo,hi+1):
                    for t in range(first,last+1):
                        uncovered[k][t]=0
                        out[((a*S+b)*B+k)*T+t]=1
                        out[((b*S+a)*B+B-1-k)*T+t]=1
    assert all(not b or a for a,b in zip(raw,out))
    (DATA/(name+'.seed.bin')).write_bytes(out)
    (DATA/(name+'.dat')).write_bytes((DATA/(source+'.dat')).read_bytes())
    (DATA/(name+'.meta.json')).write_text(json.dumps(meta,indent=2)+'\n')
    result={'source':source,'proposal_only':True,'allow_overlap':overlap,'rectangular_conditions':len(rows),
            'represented_states':sum(out),'rows':rows}
    (DATA/(name+'_proposal.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',default='graph_wide');p.add_argument('--name',default='small3')
    p.add_argument('--per-geometry',type=int,default=3);p.add_argument('--overlap',action='store_true');args=p.parse_args()
    propose(args.source,args.name,args.per_geometry,args.overlap)
