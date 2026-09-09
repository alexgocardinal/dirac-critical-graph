#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <queue>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

/*
 * Standalone exact audit of candidate60.edgelist.
 *
 * This implementation is deliberately not the DSATUR code used by the Cayley
 * search.  It treats 3-colouring as a finite-domain CSP. Domains are subsets
 * of {0,1,2}; singleton domains are propagated through all neighbours, and a
 * minimum-domain variable is branched on.  A fixed edge receives colours 0,1,
 * which is sound by global colour symmetry.  Exhaustion is a proof of UNSAT.
 */

using namespace std;

struct Graph {
    int n=60;
    array<uint64_t,60> adj{};
    vector<pair<int,int>> edges;
};

static Graph read_graph(const string &path) {
    ifstream f(path);
    if (!f) throw runtime_error("cannot open input");
    Graph g; int x,y; set<pair<int,int>> seen;
    while (f>>x>>y) {
        if (x<0 || x>=60 || y<0 || y>=60 || x==y) throw runtime_error("bad edge");
        if (x>y) swap(x,y);
        if (!seen.insert({x,y}).second) throw runtime_error("duplicate edge");
        g.adj[x] |= 1ULL<<y; g.adj[y] |= 1ULL<<x;
    }
    g.edges.assign(seen.begin(),seen.end());
    return g;
}

struct Solver {
    const Graph *g=nullptr;
    int deleted=-1, eu=-1, ev=-1;
    uint64_t nodes=0, propagations=0;
    array<uint8_t,60> witness{};

    bool has_edge(int x,int y) const {
        if (x==deleted || y==deleted) return false;
        if ((x==eu && y==ev)||(x==ev && y==eu)) return false;
        return (g->adj[x]>>y)&1ULL;
    }

    bool propagate(array<uint8_t,60> &d) {
        bool changed=true;
        while (changed) {
            changed=false;
            for (int v=0;v<g->n;v++) if (v!=deleted && popcount((unsigned)d[v])==1) {
                uint8_t c=d[v];
                uint64_t z=g->adj[v];
                if (v==eu) z&=~(1ULL<<ev);
                if (v==ev) z&=~(1ULL<<eu);
                if (deleted>=0) z&=~(1ULL<<deleted);
                while(z) {
                    int u=countr_zero(z);z&=z-1;
                    if (d[u]==c) return false;
                    if ((d[u]&c) && popcount((unsigned)d[u])>1) {
                        d[u]&=~c; ++propagations; changed=true;
                        if (!d[u]) return false;
                    }
                }
            }
        }
        return true;
    }

    bool dfs(array<uint8_t,60> d) {
        ++nodes;
        if (!propagate(d)) return false;
        int best=-1, best_domain=4, best_degree=-1;
        for (int v=0;v<g->n;v++) if (v!=deleted) {
            int pc=popcount((unsigned)d[v]);
            if (pc<=1) continue;
            int deg=popcount(g->adj[v] & ~(deleted>=0?(1ULL<<deleted):0ULL));
            if (pc<best_domain || (pc==best_domain && deg>best_degree)) {
                best=v;best_domain=pc;best_degree=deg;
            }
        }
        if (best<0) {
            for(int v=0;v<g->n;v++) witness[v]=(v==deleted?255:countr_zero((unsigned)d[v]));
            return true;
        }
        uint8_t choices=d[best];
        while(choices) {
            uint8_t c=choices&-choices;choices^=c;
            auto e=d;e[best]=c;
            if (dfs(e)) return true;
        }
        return false;
    }

    bool solve(const Graph &gg,int del=-1,int x=-1,int y=-1) {
        g=&gg;deleted=del;eu=x;ev=y;nodes=propagations=0;
        array<uint8_t,60>d;d.fill(7);if(del>=0)d[del]=0;
        // Fix the endpoints of any surviving edge to colours 0 and 1.
        pair<int,int> root={-1,-1};
        for(auto e:g->edges) if(has_edge(e.first,e.second)){root=e;break;}
        if(root.first>=0){d[root.first]=1;d[root.second]=2;}
        return dfs(d);
    }
};

static bool check_colouring(const Graph&g,const array<uint8_t,60>&c,int del=-1,int eu=-1,int ev=-1){
    for(int v=0;v<60;v++)if(v!=del && c[v]>2)return false;
    for(auto [x,y]:g.edges){
        if(x==del||y==del||((x==eu&&y==ev)||(x==ev&&y==eu)))continue;
        if(c[x]==c[y])return false;
    }
    return true;
}

static string g6(const Graph&g){
    string s;s.push_back(char(63+g.n));int val=0,k=0;
    for(int j=1;j<g.n;j++)for(int i=0;i<j;i++){
        val=(val<<1)+((g.adj[i]>>j)&1ULL);if(++k==6){s.push_back(char(63+val));val=k=0;}
    }
    if(k) s.push_back(char(63+(val<<(6-k))));
    return s;
}

int main(int argc,char**argv){
    if(argc!=2){cerr<<"usage: verify_candidate60 EDGEFILE\n";return 2;}
    Graph g=read_graph(argv[1]);
    cout<<"order "<<g.n<<" size "<<g.edges.size()<<"\n";
    if(g.edges.size()!=180){cerr<<"FAIL: expected 180 edges\n";return 1;}
    vector<int>deg(60);for(int v=0;v<60;v++)deg[v]=popcount(g.adj[v]);
    cout<<"degrees";for(int d:deg)cout<<" "<<d;cout<<"\n";
    if(!all_of(deg.begin(),deg.end(),[](int d){return d==6;})){
        cerr<<"FAIL: graph is not 6-regular\n";return 1;
    }
    // Connectedness.
    uint64_t seen=1,todo=1;
    while(todo){int v=countr_zero(todo);todo&=todo-1;uint64_t z=g.adj[v]&~seen;seen|=z;todo|=z;}
    cout<<"connected "<<(popcount(seen)==60)<<"\n";
    if(popcount(seen)!=60){cerr<<"FAIL: graph is disconnected\n";return 1;}
    const string expected_g6="{?AA@?OA?G?O?O?G?A??O?@??A??A??@???O??A???G???O???OA??GO??AA???OG??@?O??AD@??AA__?@?k???Oc_??AAQ???GAa_??OB__??O_oO??GGKC??A@@o???O?aP??@?@Ca??A?@SA??A??i_??@?CAg???O??e?_?A??AX???G??Cq???O?A?q???O?@CP???G???L@??A???_gG??O??AAo??@???Cc_??A???Cc_??AC???II??@@???B__??OG??GKC??A?_??_oO??G@??@@o???O";
    const string encoded=g6(g);
    cout<<"graph6 "<<encoded<<"\n";
    if(encoded!=expected_g6){cerr<<"FAIL: graph6 mismatch\n";return 1;}
    Solver s;
    bool base=s.solve(g);
    cout<<"G_3colourable "<<base<<" nodes "<<s.nodes<<" propagations "<<s.propagations<<"\n";
    if(base){cerr<<"FAIL: G is 3-colourable\n";return 1;}
    uint64_t totalvn=0,maxvn=0;array<uint8_t,60> root_witness{};
    for(int v=0;v<60;v++){
        bool ok=s.solve(g,v);totalvn+=s.nodes;maxvn=max(maxvn,s.nodes);
        bool valid=ok&&check_colouring(g,s.witness,v);
        if(v==0)root_witness=s.witness;
        if(!valid){cerr<<"FAIL vertex "<<v<<"\n";return 1;}
    }
    cout<<"all_vertex_deletions_three_colourable 60/60"
        <<" total_nodes "<<totalvn<<" max_nodes "<<maxvn<<"\n";
    uint64_t totalen=0,maxen=0;int idx=0;
    for(auto [x,y]:g.edges){
        bool ok=s.solve(g,-1,x,y);totalen+=s.nodes;maxen=max(maxen,s.nodes);
        bool valid=!ok || check_colouring(g,s.witness,-1,x,y);
        ++idx;
        if(ok){
            cerr<<"FAIL critical edge "<<x<<" "<<y<<" witness_valid "<<valid<<"\n";
            return 1;
        }
    }
    cout<<"all_edge_deletions_non_three_colourable "<<idx<<"/180"
        <<" total_nodes "<<totalen<<" max_nodes "<<maxen<<"\n";
    array<int,3> split{};
    uint64_t z=g.adj[0];while(z){int u=countr_zero(z);z&=z-1;++split[root_witness[u]];}
    cout<<"root_neighbour_colour_split "<<split[0]<<","<<split[1]<<","<<split[2]<<"\n";
    if(split!=array<int,3>{2,2,2}){cerr<<"FAIL: root split is not 2+2+2\n";return 1;}
    cout<<"RESULT PASS: chi=4; vertex-critical; critical_edges=0; q3=2\n";
    return 0;
}
