// Separately coded integer-only C++ implementation of the mixed-radix rules.
// This is not a Lean-certified evaluator. State A=0, B=1; initial head=0.
// Usage: ./verify 100       (exact target 10^100)
//        ./verify 8 slow    (literal 10^8-step comparison).
#include <boost/multiprecision/cpp_int.hpp>
#include <vector>
#include <iostream>
#include <string>
#include <algorithm>
#include <chrono>
#include <climits>
using boost::multiprecision::cpp_int;
struct Tr { int w,d,q; };
const Tr tr[2][5]={{{1,1,1},{-1,0,0},{3,1,0},{2,-1,0},{2,1,1}},{{2,-1,1},{3,-1,0},{4,-1,1},{4,1,0},{0,1,0}}};
struct Edit{int p,v;};
int main(int argc,char**argv){
  cpp_int target=1; int power=argc>1?std::stoi(argv[1]):100;
  if(power<0){std::cerr<<"power must be nonnegative\n";return 2;}
  for(int i=0;i<power;i++)target*=10;
  bool slow=argc>2 && std::string(argv[2])=="slow";
  std::vector<int>a(200000,0);int p=100000,q=0,lo=p,hi=p,m=INT_MAX;
  cpp_int t=0; unsigned long long macro=0,micro=0,epochs=0,leftA=0;
  int minFours=INT_MAX,minDist=INT_MAX;std::vector<Edit> edits;
  auto start=std::chrono::steady_clock::now();std::string status="REACHED_TARGET";
  while(t<target){
    auto v=tr[q][a[p]];
    if(v.w<0){status="HALT";break;}
    bool ok=false;cpp_int cost=0;
    if(q==0 && !slow){
      int i=p;cpp_int k=1;edits.clear();ok=true;
      while(k!=0){
        if(i<0 || i+1>=(int)a.size()){std::cerr<<"macro storage limit\n";return 2;}
        if(a[i]==2){cost+=4*k;k*=3;++i;}
        else if(a[i]==4 && (a[i+1]==2 || a[i+1]==4)){
          cpp_int total=k+(a[i+1]==4?1:0);cpp_int carry=total/2;
          int bit=(total%2).convert_to<int>();edits.push_back({i+1,2+2*bit});
          cost+=3*k+carry;k=carry;i+=2;
        }else{ok=false;break;}
      }
      if(ok && t+cost>target)ok=false;
    }
    if(ok){for(auto e:edits)a[e.p]=e.v;p--;q=1;t+=cost;macro++;}
    else{
      if(v.q==0 && v.d==-1 && p>m){
        ++leftA;int r=p-1,n=0;while(r>=lo && a[r]!=1){n+=(a[r]==4);--r;}
        if(r>=lo){minFours=std::min(minFours,n);minDist=std::min(minDist,p-r);}
      }
      if(v.w==1 && p<m){m=p;epochs++;}
      a[p]=v.w;p+=v.d;q=v.q;++t;++micro;
    }
    lo=std::min(lo,p);hi=std::max(hi,p);
    if(lo<2||hi+2>=(int)a.size()){status="STORAGE_LIMIT";break;}
    if((macro+micro)%1000000==0){
      auto sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
      if(sec>50){status="TIME_LIMIT";break;}
    }
  }
  std::cout<<"{\"status\":\""<<status<<"\",\"t\":\""<<t<<"\",\"p\":"<<p-100000<<",\"q\":"<<q
    <<",\"lo\":"<<lo-100000<<",\"hi\":"<<hi-100000<<",\"macros\":"<<macro<<",\"micro\":"<<micro
    <<",\"epochs\":"<<epochs<<",\"left_A_transitions\":"<<leftA<<",\"minimum_four_count\":"<<minFours
    <<",\"minimum_distance_to_one\":"<<minDist<<",\"tape\":\"";
  for(int i=lo;i<=hi;i++)std::cout<<a[i];
  std::cout<<"\",\"elapsed\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"}\n";
}
