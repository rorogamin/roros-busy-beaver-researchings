// Independently coded C++ event evaluator, not a Lean certificate.
// Build: g++ -O3 -std=c++17 verify_events.cpp -o verify_events
// Usage: ./verify_events 1000   (exactly 10^1000 transitions from blank)
#include <boost/multiprecision/cpp_int.hpp>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
using Z=boost::multiprecision::cpp_int;
struct Tr {int w, d, q;};
const Tr tr[2][5]={{{1,1,1},{-1,0,0},{3,1,0},{2,-1,0},{2,1,1}},
                  {{2,-1,1},{3,-1,0},{4,-1,1},{4,1,0},{0,1,0}}};
int bd(int x){switch(x){case 0:return -1;case 2:return 0;case 3:return 3;case 4:return 1;default:return -99;}}
int td(int x){switch(x){case 3:return 0;case 4:return 1;case 0:return 2;default:return -1;}}
const int enc[3]={3,4,0};
struct Plan {bool ok;Z cost;int end;std::vector<std::pair<int,int>> edits;};
Plan returns(const std::vector<int>& a,int p,Z k){
    Plan out{true,0,p,{}};int j=p;
    while(k!=0){
        if(j+1>=int(a.size())){out.ok=false;break;}
        if(a[j]==2){out.cost+=4*k;k*=3;++j;}
        else if(a[j]==4 && bd(a[j+1])!=-99){
            Z z=k+bd(a[j+1]), q=z/2;
            out.edits.push_back({j+1,2+2*(z%2).convert_to<int>()});
            out.cost+=3*k+q;k=q;j+=2;
        }else{out.ok=false;break;}
    }
    out.end=j;return out;
}
struct Drain {Z cap,cost;int end;std::vector<std::pair<int,int>> edits;};
Drain drain(const std::vector<int>& a,int p){
    std::vector<std::pair<int,int>> tok;int j=p;
    while(j+1<int(a.size())){
        if(a[j]==2){tok.push_back({j,99});++j;}
        else if(a[j]==4 && bd(a[j+1])!=-99){tok.push_back({j,bd(a[j+1])});j+=2;}
        else break;
    }
    Drain out{0,0,j,{}};
    for(auto it=tok.rbegin();it!=tok.rend();++it){
        int pos=it->first,b=it->second;Z c=out.cap;
        if(b==99){int r=(c%3).convert_to<int>();out.cap=c/3;out.cost+=4*out.cap+1+r;out.edits.push_back({pos,enc[r]});}
        else{out.cap=2*c+1-b;if(out.cap<0)out.cap=0;
             out.cost+=3*out.cap+c+2;out.edits.push_back({pos,2});out.edits.push_back({pos+1,(b==3 && c==0)?4:0});}
    }
    return out;
}
std::pair<std::vector<int>,long long> digits(Z n,int width){
    std::vector<int> ds;long long sum=0;
    while(n!=0){int d=(n%3).convert_to<int>();n/=3;ds.push_back(d);sum+=d;}
    ds.resize(std::max(width,int(ds.size())),0);return {ds,sum};
}
int main(int argc,char**argv){
    int power=argc>1?std::stoi(argv[1]):1000;
    if(power<0 || power>100000)throw std::invalid_argument("invalid power");
    bool slow=argc>2 && std::string(argv[2])=="slow";
    Z target=1;for(int i=0;i<power;++i)target*=10;
    if(argc>3 && std::string(argv[2])=="--steps")target=Z(std::string(argv[3]));
    if(target<0)throw std::invalid_argument("negative target");
    int cells=std::max(40000,30*power),origin=cells/2;
    std::vector<int>a(cells,0);int p=origin,q=0,lo=p,hi=p;Z t=0;
    unsigned long long drains=0,batches=0,ret=0,casc=0,sweeps=0,micro=0;
    std::string status="REACHED_TARGET";auto start=std::chrono::steady_clock::now();
    auto setcounter=[&](const std::vector<int>& ds){
        if(p-int(ds.size())-1<2)throw std::runtime_error("counter storage exhausted");
        for(int k=0;k<int(ds.size());++k)a[p-1-k]=enc[ds[k]];
        int front=p-int(ds.size())-1;a[front]=1;lo=std::min(lo,front);
    };
    while(t<target){
        if(p<2 || p+2>=cells)throw std::runtime_error("head storage exhausted");
        Z remaining=target-t;bool done=false;
        if(q==0 && !slow){
            int left=p-1,m=0;long long ds_sum=0;Z value=0,pow3=1;
            while(left>=lo && td(a[left])>=0){int d=td(a[left]);value+=pow3*d;pow3*=3;ds_sum+=d;++m;--left;}
            if(left>=lo && a[left]==1){
                bool grow=left==lo;auto d=drain(a,p);Z cap=d.cap;
                if(d.end+2>=cells)throw std::runtime_error("drain storage exhausted");
                if(d.end>p && (grow || value+cap<pow3)){
                    auto ds=digits(value+cap,m);Z cost=d.cost+2*cap+ds_sum-ds.second+2*(int(ds.first.size())-m);
                    if(cost<=remaining){for(auto e:d.edits)a[e.first]=e.second;setcounter(ds.first);p=d.end;hi=std::max(hi,p);t+=cost;++drains;done=true;}
                }
                if(!done){
                    if(!grow){Z bound=pow3-1-value;if(cap>bound)cap=bound;}
                    Z k=cap;
                    for(int attempt=0;attempt<14 && k>0;++attempt){
                        auto rp=returns(a,p,k);if(!rp.ok)throw std::runtime_error("capacity mismatch");
                        auto ds=digits(value+k,m);Z cost=rp.cost+2*k+ds_sum-ds.second+2*(int(ds.first.size())-m);
                        if(cost<=remaining){for(auto e:rp.edits)a[e.first]=e.second;setcounter(ds.first);hi=std::max(hi,rp.end-1);t+=cost;++batches;done=true;break;}
                        if(attempt<8)k=k*remaining/cost-1;else k/=2;
                    }
                }
            }
            if(!done){auto rp=returns(a,p,1);if(rp.ok && rp.cost<=remaining){for(auto e:rp.edits)a[e.first]=e.second;--p;q=1;lo=std::min(lo,p);hi=std::max(hi,rp.end-1);t+=rp.cost;++ret;done=true;}}
            if(!done){
                int j=p,mode=a[p+1],maxright=p;long long cost=0;std::vector<std::pair<int,int>> edits;
                if(a[j]==0 && mode==0){edits.push_back({j,3});edits.push_back({j+1,2});--j;mode=3;cost=3;maxright=p+1;}
                while(j>=2){
                    if(a[j]==3){edits.push_back({j,2});--j;mode=2;++cost;}
                    else if(a[j]==0 && mode==2){maxright=std::max(maxright,j+1);edits.push_back({j,3});edits.push_back({j+1,4});--j;mode=3;cost+=3;}
                    else if(a[j]==2 && mode==3){maxright=std::max(maxright,j+1);edits.push_back({j,2});edits.push_back({j+1,2});--j;mode=2;cost+=3;}
                    else break;
                }
                if(cost>0 && cost<=remaining){if(j<2)throw std::runtime_error("cascade storage exhausted");for(auto e:edits)a[e.first]=e.second;t+=cost;lo=std::min(lo,j);hi=std::max(hi,maxright);p=j;++casc;done=true;}
            }
            if(!done){
                int j=p;std::vector<std::pair<int,int>> edits;
                while(j+2<cells){
                    if(a[j]==2){edits.push_back({j,3});++j;}
                    else if(a[j]==4 && (a[j+1]==3 || a[j+1]==4)){edits.push_back({j,2});edits.push_back({j+1,a[j+1]==3?4:0});j+=2;}
                    else break;
                }
                if(j>p && j-p<=remaining){for(auto e:edits)a[e.first]=e.second;t+=j-p;p=j;hi=std::max(hi,j);++sweeps;done=true;}
            }
        }else if(q==1 && !slow){
            int j=p;while(j>=lo && (a[j]==0 || a[j]==2))--j;
            // No escape inference: use a literal step at an all-blank left edge.
            if(j<lo)j=lo;
            if(j<p && p-j<=remaining){for(int k=j+1;k<=p;++k)a[k]=a[k]==0?2:4;t+=p-j;p=j;++sweeps;done=true;}
        }
        if(!done){auto s=tr[q][a[p]];if(s.w<0){status="HALT";break;}a[p]=s.w;p+=s.d;q=s.q;++t;++micro;lo=std::min(lo,p);hi=std::max(hi,p);}
    }
    std::cout<<"{\"status\":\""<<status<<"\",\"t\":\""<<t<<"\",\"p\":"<<p-origin<<",\"q\":"<<q<<",\"lo\":"<<lo-origin<<",\"hi\":"<<hi-origin<<",\"tape\":\"";
    for(int j=lo;j<=hi;++j)std::cout<<a[j];
    std::cout<<"\",\"counts\":{\"drains\":"<<drains<<",\"batches\":"<<batches<<",\"returns\":"<<ret<<",\"cascades\":"<<casc<<",\"sweeps\":"<<sweeps<<",\"literal\":"<<micro<<"},\"elapsed\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"}\n";
}
