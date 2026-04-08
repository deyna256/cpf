#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef pair<ll,int> pli;
const ll INF=1e18;

// ─── Dijkstra ─────────────────────────────────────────────────────────────────
// Когда: кратчайшие пути из одной вершины, неотрицательные веса
// O((V+E) log V)
vector<ll> dijkstra(int s, vector<vector<pair<int,ll>>>& g){
    int n=g.size(); vector<ll> d(n,INF); d[s]=0;
    priority_queue<pli,vector<pli>,greater<>> pq;
    pq.push({0,s});
    while(!pq.empty()){
        auto [dv,v]=pq.top(); pq.pop();
        if(dv>d[v]) continue;
        for(auto [u,w]:g[v]) if(d[v]+w<d[u]){ d[u]=d[v]+w; pq.push({d[u],u}); }
    }
    return d;
}

// ─── Bellman-Ford ─────────────────────────────────────────────────────────────
// Когда: отрицательные веса, обнаружение отрицательных циклов
// O(VE)
struct Edge { int u,v; ll w; };
vector<ll> bellmanFord(int s, int n, vector<Edge>& edges){
    vector<ll> d(n,INF); d[s]=0;
    for(int i=0;i<n-1;i++)
        for(auto& e:edges)
            if(d[e.u]!=INF) d[e.v]=min(d[e.v],d[e.u]+e.w);
    // проверка отрицательного цикла: если после n-1 итераций ещё можно расслабить — цикл есть
    return d;
}

// ─── Floyd-Warshall ───────────────────────────────────────────────────────────
// Когда: все пары кратчайших путей, маленький граф (V <= 500)
void floydWarshall(vector<vector<ll>>& d){
    int n=d.size();
    for(int k=0;k<n;k++) for(int i=0;i<n;i++) for(int j=0;j<n;j++)
        if(d[i][k]!=INF&&d[k][j]!=INF) d[i][j]=min(d[i][j],d[i][k]+d[k][j]);
}
// Инициализация: d[i][i]=0, d[i][j]=w(i,j) или INF

// ─── Topological Sort (Kahn BFS) ─────────────────────────────────────────────
// Когда: порядок задач с зависимостями, DAG, обнаружение цикла в ориентированном графе
vector<int> topoSort(int n, vector<vector<int>>& g){
    vector<int> indeg(n,0);
    for(int v=0;v<n;v++) for(int u:g[v]) indeg[u]++;
    queue<int> q; for(int i=0;i<n;i++) if(!indeg[i]) q.push(i);
    vector<int> order;
    while(!q.empty()){
        int v=q.front(); q.pop(); order.push_back(v);
        for(int u:g[v]) if(!--indeg[u]) q.push(u);
    }
    return order; // если order.size()!=n — в графе есть цикл
}

// ─── SCC (Kosaraju) ───────────────────────────────────────────────────────────
// Когда: сильно связные компоненты, конденсация графа, 2-SAT
vector<int> scc(int n, vector<vector<int>>& g){
    vector<vector<int>> rg(n);
    for(int v=0;v<n;v++) for(int u:g[v]) rg[u].push_back(v);
    vector<int> order, comp(n,-1); vector<bool> vis(n,false);
    function<void(int)> dfs1=[&](int v){ vis[v]=true; for(int u:g[v]) if(!vis[u]) dfs1(u); order.push_back(v); };
    function<void(int,int)> dfs2=[&](int v,int c){ comp[v]=c; for(int u:rg[v]) if(comp[u]==-1) dfs2(u,c); };
    for(int i=0;i<n;i++) if(!vis[i]) dfs1(i);
    int c=0; for(int i=n-1;i>=0;i--) if(comp[order[i]]==-1) dfs2(order[i],c++);
    return comp; // comp[v] — номер SCC; SCC в порядке топологической сортировки конденсации
}

// ─── Мосты и точки сочленения (Tarjan) ───────────────────────────────────────
// Когда: надёжность сети, двусвязные компоненты, критические рёбра/вершины
vector<pair<int,int>> bridges;
vector<int> artPoints;

void findBridges(int n, vector<vector<pair<int,int>>>& g){ // g[v]={u, edge_id}
    vector<int> disc(n,-1), low(n);
    int timer=0;
    function<void(int,int)> dfs=[&](int v,int pe){
        disc[v]=low[v]=timer++;
        for(auto [u,eid]:g[v]){
            if(eid==pe) continue;
            if(disc[u]==-1){
                dfs(u,eid);
                low[v]=min(low[v],low[u]);
                if(low[u]>disc[v]) bridges.push_back({v,u});
            } else low[v]=min(low[v],disc[u]);
        }
    };
    for(int i=0;i<n;i++) if(disc[i]==-1) dfs(i,-1);
}

void findAP(int n, vector<vector<int>>& g){
    vector<int> disc(n,-1), low(n); vector<bool> ap(n,false);
    int timer=0;
    function<void(int,int)> dfs=[&](int v,int p){
        disc[v]=low[v]=timer++; int children=0;
        for(int u:g[v]){
            if(disc[u]==-1){
                children++; dfs(u,v); low[v]=min(low[v],low[u]);
                if(p==-1&&children>1) ap[v]=true;
                if(p!=-1&&low[u]>=disc[v]) ap[v]=true;
            } else if(u!=p) low[v]=min(low[v],disc[u]);
        }
    };
    for(int i=0;i<n;i++) if(disc[i]==-1) dfs(i,-1);
    for(int i=0;i<n;i++) if(ap[i]) artPoints.push_back(i);
}

// ─── LCA (Binary Lifting) ─────────────────────────────────────────────────────
// Когда: наименьший общий предок, расстояние между вершинами дерева
struct LCA {
    int n, LOG; vector<vector<int>> up; vector<int> dep;
    LCA(int n, vector<vector<int>>& g, int root=0):
        n(n), LOG(20), up(LOG,vector<int>(n,-1)), dep(n,0){
        function<void(int,int)> dfs=[&](int v,int p){
            up[0][v]=p;
            for(int i=1;i<LOG;i++) up[i][v]=(up[i-1][v]==-1)?-1:up[i-1][up[i-1][v]];
            for(int u:g[v]) if(u!=p){ dep[u]=dep[v]+1; dfs(u,v); }
        };
        dfs(root,root);
    }
    int lca(int u, int v){
        if(dep[u]<dep[v]) swap(u,v);
        int diff=dep[u]-dep[v];
        for(int i=0;i<LOG;i++) if((diff>>i)&1) u=up[i][u];
        if(u==v) return u;
        for(int i=LOG-1;i>=0;i--) if(up[i][u]!=up[i][v]){ u=up[i][u]; v=up[i][v]; }
        return up[0][u];
    }
    int dist(int u, int v){ return dep[u]+dep[v]-2*dep[lca(u,v)]; }
};

// ─── MST (Kruskal) ────────────────────────────────────────────────────────────
// Когда: минимальное остовное дерево, задачи на сортировку рёбер
struct KEdge { int u,v; ll w; };
ll kruskal(int n, vector<KEdge>& edges){
    sort(edges.begin(),edges.end(),[](auto& a,auto& b){ return a.w<b.w; });
    vector<int> p(n); iota(p.begin(),p.end(),0);
    function<int(int)> find=[&](int x){ return p[x]==x?x:p[x]=find(p[x]); };
    ll cost=0; int cnt=0;
    for(auto& e:edges){
        int pu=find(e.u), pv=find(e.v);
        if(pu!=pv){ p[pu]=pv; cost+=e.w; cnt++; }
        if(cnt==n-1) break;
    }
    return cost;
}

// ─── MST (Prim) ───────────────────────────────────────────────────────────────
// Когда: плотный граф (E ~ V²), MST на матрице смежности
ll prim(int n, vector<vector<pair<int,ll>>>& g){
    vector<ll> key(n,INF); vector<bool> inMST(n,false); key[0]=0;
    priority_queue<pli,vector<pli>,greater<>> pq; pq.push({0,0});
    ll cost=0;
    while(!pq.empty()){
        auto [d,v]=pq.top(); pq.pop();
        if(inMST[v]) continue; inMST[v]=true; cost+=d;
        for(auto [u,w]:g[v]) if(!inMST[u]&&w<key[u]){ key[u]=w; pq.push({w,u}); }
    }
    return cost;
}

// ─── Dinic (Max Flow) ────────────────────────────────────────────────────────
// Когда: максимальный поток, минимальный разрез, паросочетание в двудольном графе
struct Dinic {
    struct Edge { int to,rev; ll cap; };
    int n; vector<vector<Edge>> g; vector<int> d,cur;
    Dinic(int n): n(n), g(n), d(n), cur(n){}
    void addEdge(int u, int v, ll cap){
        g[u].push_back({v,(int)g[v].size(),cap});
        g[v].push_back({u,(int)g[u].size()-1,0});
    }
    bool bfs(int s, int t){
        fill(d.begin(),d.end(),-1); d[s]=0;
        queue<int> q; q.push(s);
        while(!q.empty()){ int v=q.front(); q.pop(); for(auto& e:g[v]) if(e.cap>0&&d[e.to]<0){ d[e.to]=d[v]+1; q.push(e.to); } }
        return d[t]>=0;
    }
    ll dfs(int v, int t, ll pushed){
        if(v==t) return pushed;
        for(int& i=cur[v];i<(int)g[v].size();i++){
            auto& e=g[v][i];
            if(e.cap<=0||d[e.to]!=d[v]+1) continue;
            ll tr=dfs(e.to,t,min(pushed,e.cap));
            if(tr>0){ e.cap-=tr; g[e.to][e.rev].cap+=tr; return tr; }
        }
        return 0;
    }
    ll maxflow(int s, int t){
        ll flow=0;
        while(bfs(s,t)){ fill(cur.begin(),cur.end(),0); while(ll f=dfs(s,t,INF)) flow+=f; }
        return flow;
    }
};

// ─── Min-Cost Max-Flow (MCMF) ─────────────────────────────────────────────────
// Когда: минимальная стоимость потока, назначение задач (Hungarian через MCMF)
struct MCMF {
    struct Edge { int to,rev; ll cap,cost; };
    int n; vector<vector<Edge>> g;
    MCMF(int n): n(n), g(n){}
    void addEdge(int u, int v, ll cap, ll cost){
        g[u].push_back({v,(int)g[v].size(),cap,cost});
        g[v].push_back({u,(int)g[u].size()-1,0,-cost});
    }
    pair<ll,ll> minCostFlow(int s, int t, ll maxf=INF){
        ll flow=0, cost=0;
        while(flow<maxf){
            vector<ll> d(n,INF); vector<bool> inq(n,false); vector<int> prev(n,-1),preve(n,-1);
            d[s]=0; queue<int> q; q.push(s); inq[s]=true;
            while(!q.empty()){
                int v=q.front(); q.pop(); inq[v]=false;
                for(int i=0;i<(int)g[v].size();i++){
                    auto& e=g[v][i];
                    if(e.cap>0&&d[v]+e.cost<d[e.to]){ d[e.to]=d[v]+e.cost; prev[e.to]=v; preve[e.to]=i; if(!inq[e.to]){inq[e.to]=true;q.push(e.to);} }
                }
            }
            if(d[t]==INF) break;
            ll pushf=maxf-flow;
            for(int v=t;v!=s;v=prev[v]) pushf=min(pushf,g[prev[v]][preve[v]].cap);
            for(int v=t;v!=s;v=prev[v]){ g[prev[v]][preve[v]].cap-=pushf; g[v][g[prev[v]][preve[v]].rev].cap+=pushf; }
            flow+=pushf; cost+=pushf*d[t];
        }
        return {flow,cost};
    }
};

// ─── Двудольное паросочетание (Kuhn) ─────────────────────────────────────────
// Когда: максимальное паросочетание в двудольном графе, покрытие вершинами
struct Kuhn {
    int n,m; vector<vector<int>> g; vector<int> match; vector<bool> used;
    Kuhn(int n,int m): n(n),m(m),g(n),match(m,-1),used(n){}
    void addEdge(int u,int v){ g[u].push_back(v); }
    bool dfs(int v){ for(int u:g[v]) if(!used[u]){ used[u]=true; if(match[u]==-1||dfs(match[u])){ match[u]=v; return true; } } return false; }
    int solve(){ int res=0; for(int v=0;v<n;v++){ fill(used.begin(),used.end(),false); if(dfs(v)) res++; } return res; }
};

// ─── Euler Path / Circuit (Hierholzer) ───────────────────────────────────────
// Когда: обход всех рёбер ровно по одному разу (задачи на Эйлеров путь/цикл)
// Граф неориентированный: каждая вершина чётной степени → цикл; ровно 2 нечётных → путь
vector<int> eulerPath(int start, vector<vector<pair<int,int>>>& g){ // g[v]={u, edge_id}
    int m=0; for(auto& adj:g) m+=adj.size(); m/=2;
    vector<bool> usedEdge(m,false);
    vector<int> path, ptr(g.size(),0);
    stack<int> st; st.push(start);
    while(!st.empty()){
        int v=st.top();
        bool found=false;
        while(ptr[v]<(int)g[v].size()){
            auto [u,eid]=g[v][ptr[v]++];
            if(!usedEdge[eid]){ usedEdge[eid]=true; st.push(u); found=true; break; }
        }
        if(!found){ path.push_back(v); st.pop(); }
    }
    reverse(path.begin(),path.end()); return path;
}

// ─── 2-SAT ────────────────────────────────────────────────────────────────────
// Когда: выполнимость конъюнкции дизъюнктов из 2 литералов; OR-условия на булевых переменных
// Переменная i: прямая = 2i, отрицание = 2i+1
struct TwoSat {
    int n; vector<vector<int>> g;
    TwoSat(int n): n(n), g(2*n){}
    // a OR b: если !a то b, если !b то a
    void addClause(int a, bool na, int b, bool nb){
        g[2*a+(na?0:1)].push_back(2*b+(nb?1:0));
        g[2*b+(nb?0:1)].push_back(2*a+(na?1:0));
    }
    // переменная a = val (принудительно)
    void forceTrue(int a, bool val){ addClause(a,!val,a,!val); }

    vector<int> comp; vector<int> order; vector<bool> vis;
    void dfs1(int v){ vis[v]=true; for(int u:g[v]) if(!vis[u]) dfs1(u); order.push_back(v); }
    void dfs2(int v,int c){ comp[v]=c; for(int u:g[v]) if(comp[u]==-1) dfs2(u,c); }

    // Возвращает пустой вектор если невыполнима, иначе решение
    vector<bool> solve(){
        vis.assign(2*n,false); order.clear();
        for(int i=0;i<2*n;i++) if(!vis[i]) dfs1(i);
        // строим обратный граф
        vector<vector<int>> rg(2*n);
        for(int v=0;v<2*n;v++) for(int u:g[v]) rg[u].push_back(v);
        comp.assign(2*n,-1); int c=0;
        for(int i=2*n-1;i>=0;i--){
            int v=order[i];
            if(comp[v]==-1){
                // dfs по rg
                function<void(int,int)> f=[&](int v,int c){ comp[v]=c; for(int u:rg[v]) if(comp[u]==-1) f(u,c); };
                f(v,c++);
            }
        }
        vector<bool> res(n);
        for(int i=0;i<n;i++){
            if(comp[2*i]==comp[2*i+1]) return {}; // противоречие
            res[i]=comp[2*i]>comp[2*i+1];
        }
        return res;
    }
};

int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);
}
