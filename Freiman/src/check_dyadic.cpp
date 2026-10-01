#define main invariant_program_main
#include "invariant_kernel.cpp"
#undef main
int main(){
 uint64_t seed=462;
 auto rnd=[&](){seed=seed*6364136223846793005ULL+1442695040888963407ULL;return seed;};
 for(int i=0;i<2000;i++){
  Z a=Z(rnd()%(20*D))-10*D,b=Z(rnd()%(20*D))-10*D;
  if(a>b)swap(a,b);
  Z c=1+Z(rnd()%(10*D)),d=1+Z(rnd()%(10*D));if(c>d)swap(c,d);
  I p=mul({a,b},{c,d}),q=divi({a,b},{c,d});
  cout<<a<<" "<<b<<" "<<c<<" "<<d<<" "<<p.l<<" "<<p.h<<" "<<q.l<<" "<<q.h<<"\n";
 }
}
