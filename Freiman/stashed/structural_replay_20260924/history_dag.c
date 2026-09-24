/* C89 structural history checker. No heap, floats, symbolic algebra, or
 * depth cutoff. Numeric coverage of the retained intervals is NOT checked.
 * The forbidden-word suffix is tracked with five automaton states; the
 * other-side endpoint suffix additionally distinguishes 1 and 2.
 */
#include <stdio.h>
#include <stdlib.h>

/* 768 bytes of tables on a machine with 16-bit unsigned short. */
static unsigned char rank_table[256]; /* 0 unseen, 255 active, rank + 1 done */
static unsigned short paths[256];
static unsigned short states, edges, counts[4], attempts;
static const unsigned char first[6] = {1,2,3,0,2,3};
static const unsigned char second[6] = {0,0,0,1,1,1};
/* suffix ids: 0=1, 1=2, 2=3, 3=31, 4=313, 5=3131 */
static const signed char advance[6][3] = {
    {0,1,2}, {0,1,2}, {3,1,2}, {0,1,4}, {5,1,2}, {0,1,-1}
};

static void need(int ok, const char *message)
{
    if (!ok) { fprintf(stderr, "FAIL: %s\n", message); exit(1); }
}

/* Encode: other suffix 3 bits, marked suffix 1, parities 2,
 * wider side 1, preceding unreflected one-sided 1 flag 1. */
static unsigned child(unsigned s, unsigned label, unsigned nw, int *valid)
{
    unsigned a=first[label], b=second[label], wide=(s>>6)&1;
    unsigned marked=(s>>3)&1, p0=(s>>4)&1, p1=(s>>5)&1;
    unsigned e0=wide ? b:a, e1=wide ? a:b, other=s&7;
    unsigned ws=wide ? (marked ? 5:4):other, flag;
    int new_other;
    *valid=0;
    if (!a && p0==p1) return 0;
    if (a==3 && (ws==3 || ws==5)) return 0;
    if (e1>1 || (marked && e1)) return 0;
    if (!a && nw!=wide) return 0;
    if (a && !b && (a==2 || a==3) && nw==wide) return 0;
    if (!wide && !e1 && a==1 && !b && (s&128) && nw!=1) return 0;
    new_other=e0 ? advance[other][e0-1]:(int)other;
    if (new_other<0) return 0;
    flag=(!wide && a==1 && !b && nw==wide);
    *valid=1;
    return (unsigned)new_other | ((marked || e1)<<3)
        | ((p0 ^ (e0!=0))<<4) | ((p1 ^ (e1!=0))<<5)
        | (nw<<6) | (flag<<7);
}

static unsigned visit(unsigned s)
{
    unsigned label,nw,t,r=0,v;
    int valid;
    need(rank_table[s]!=255,"cycle");
    if (rank_table[s]) return rank_table[s]-1;
    rank_table[s]=255; ++states;
    for (label=0;label<6;++label) for (nw=0;nw<2;++nw) {
        ++attempts; t=child(s,label,nw,&valid);
        if (valid) { ++edges; v=1+visit(t); if (v>r) r=v; }
    }
    rank_table[s]=(unsigned char)(r+1);
    return r;
}


static void initial_entries(void)
{
    unsigned s,ctx,entry,w,other,marked,root,r,maxrank=0,t,label,nw,p0,p1,idx;
    int valid;
    for (s=0;s<256;++s) { rank_table[s]=0; paths[s]=0; }
    for (s=0;s<4;++s) counts[s]=0;
    states=edges=attempts=0;
    for (ctx=2;ctx<=3;++ctx) for (entry=0;entry<3;++entry)
        for (w=0;w<2;++w) {
            other=entry ? entry:(ctx==3 ? 3:0);
            marked=entry!=0;
            root=other|(marked<<3)|16|(marked<<5)|(w<<6);
            r=visit(root); if (r>maxrank) maxrank=r;
            ++paths[root];
        }
    for (r=maxrank+1;r>0;--r) for (s=0;s<256;++s) {
        if (rank_table[s]!=r) continue;
        p0=(s>>4)&1; p1=(s>>5)&1; w=(s>>6)&1;
        if (s&8) {
            idx=(p0 && p1) ? (w ? 0:1):(w ? 2:3);
            counts[idx]=(unsigned short)(counts[idx]+paths[s]);
        }
        for (label=0;label<6;++label) for (nw=0;nw<2;++nw) {
            t=child(s,label,nw,&valid);
            if (valid) {
                need(rank_table[t]<rank_table[s],"entry nondecreasing rank");
                need(paths[t]<=65535U-paths[s],"entry counter overflow");
                paths[t]=(unsigned short)(paths[t]+paths[s]);
            }
        }
    }
    need(states==31 && edges==86 && maxrank==7,"entry graph cross-check");
    need(counts[0]==224 && counts[1]==34 && counts[2]==114 && counts[3]==34,
         "entry history counts");
    printf("PASS initial DAG: %u states, %u edges, %u steps after entry\n",
           states,edges,maxrank);
    printf("%u entry transition attempts; 406 histories\n",attempts);
    for (s=0;s<256;++s) if (rank_table[s]) {
        printf("ENTRY_NODE %u %u\n",s,rank_table[s]-1);
        for (label=0;label<6;++label) for (nw=0;nw<2;++nw) {
            t=child(s,label,nw,&valid);
            if (valid) printf("ENTRY_EDGE %u %u %u %u\n",s,label,nw,t);
        }
    }
}

int main(void)
{
    unsigned root0=1+16+32, root1=root0+64, maxrank,r,s,label,nw,t;
    unsigned p0,p1,w,idx;
    int valid;
    maxrank=visit(root0); r=visit(root1); if (r>maxrank) maxrank=r;
    paths[root0]=paths[root1]=1;
    for (r=maxrank+1;r>0;--r) for (s=0;s<256;++s) {
        if (rank_table[s]!=r) continue;
        p0=(s>>4)&1; p1=(s>>5)&1; w=(s>>6)&1;
        if ((s&8) && !p1 && p0<=1) {
            idx=p0 ? (w ? 2:3):(w ? 0:1);
            counts[idx]=(unsigned short)(counts[idx]+paths[s]);
        }
        for (label=0;label<6;++label) for (nw=0;nw<2;++nw) {
            t=child(s,label,nw,&valid);
            if (valid) {
                need(rank_table[t]<rank_table[s],"nondecreasing rank");
                need(paths[t]<=65535U-paths[s],"path counter overflow");
                paths[t]=(unsigned short)(paths[t]+paths[s]);
            }
        }
    }
    need(states==28 && edges==74 && maxrank==6,"graph cross-check");
    need(counts[0]==99 && counts[1]==15 && counts[2]==52 && counts[3]==15,
         "history counts");
    printf("PASS structural DAG: %u states, %u edges, %u steps after birth\n",
           states,edges,maxrank);
    printf("%u transition attempts in graph construction\n",attempts);
    printf("Six-context history counts: %u %u %u %u\n",
           6*counts[0],6*counts[1],6*counts[2],6*counts[3]);
    printf("Static tables and counters: %lu bytes (excluding stack/runtime)\n",
           (unsigned long)(sizeof(rank_table)+sizeof(paths)+sizeof(first)+
           sizeof(second)+sizeof(advance)+sizeof(states)+sizeof(edges)+
           sizeof(counts)+sizeof(attempts)));
    for (s=0;s<256;++s) if (rank_table[s]) {
        printf("NODE %u %u\n",s,rank_table[s]-1);
        for (label=0;label<6;++label) for (nw=0;nw<2;++nw) {
            t=child(s,label,nw,&valid);
            if (valid) printf("EDGE %u %u %u %u\n",s,label,nw,t);
        }
    }
    initial_entries();
    return 0;
}
