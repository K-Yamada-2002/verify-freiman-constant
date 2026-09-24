"""Find gaps in a finite interval sum without materializing all pairs.

Adapted from Berstein/kf131/audit_whole_scalar_intervals.py. This routine is
only used to propose counterexamples; the exact cylinder verifier is unchanged.
Input intervals can also use Fraction for independent algorithm tests.
"""
from bisect import bisect_left,bisect_right


def compact(rows):
    result=[]
    for a,b in sorted(rows):
        if a>b:continue
        if result and a<=result[-1][1]:result[-1]=(result[-1][0],max(b,result[-1][1]))
        else:result.append((a,b))
    return result


def sum_gaps(left,right,target):
    low,high=target
    if high<=low:raise ValueError('nonpositive target interval')
    left,right=compact(left),compact(right)
    if not left or not right:return [(low,high)]
    starts,ends=zip(*right);size=1
    while size<len(right):size*=2
    tree=[-float('inf')]*(2*size)
    for i in range(len(right)-1):tree[size+i]=starts[i+1]-ends[i]
    for i in range(size-1,0,-1):tree[i]=max(tree[2*i],tree[2*i+1])
    def barriers(first,last,width):
        pending=[(1,0,size)]
        while pending:
            i,a,b=pending.pop()
            if b<=first or last<=a or tree[i]<=width:continue
            if b-a==1:yield a
            else:
                mid=(a+b)//2;pending.extend(((2*i+1,mid,b),(2*i,a,mid)))
    covered=[];count=0
    for a,b in left:
        first=bisect_left(ends,low-b);last=bisect_right(starts,high-a)
        if first>=last:continue
        start=first
        for end in barriers(first,last-1,b-a):
            covered.append((max(low,a+starts[start]),min(high,b+ends[end])));count+=1;start=end+1
        covered.append((max(low,a+starts[start]),min(high,b+ends[last-1])));count+=1
        if count>=8192:
            covered=compact(covered);count=0
            if len(covered)==1 and covered[0]==(low,high):return []
    current=low;gaps=[]
    for a,b in compact(covered):
        if current<a:gaps.append((current,a))
        current=max(current,b)
    if current<high:gaps.append((current,high))
    return gaps
