#include <bits/stdc++.h>
using namespace std;

// ─── LIS — O(n log n) ─────────────────────────────────────────────────────────
// Когда: длиннейшая возрастающая подпоследовательность, задачи на упорядочение
// Возвращает длину LIS. Для нестрогого: замени lower_bound на upper_bound
int lis(vector<int>& a) {
    vector<int> d;
    for(int x:a){
        auto it=lower_bound(d.begin(),d.end(),x);
        if(it==d.end()) d.push_back(x);
        else *it=x;
    }
    return d.size();
}
// Восстановление LIS:
vector<int> lisRestore(vector<int>& a) {
    int n=a.size(); vector<int> d,pos(n),from(n,-1),idx;
    for(int i=0;i<n;i++){
        auto it=lower_bound(d.begin(),d.end(),a[i]);
        pos[i]=it-d.begin();
        if(it==d.end()) d.push_back(a[i]),idx.push_back(i);
        else { d[pos[i]]=a[i]; idx[pos[i]]=i; }
        if(pos[i]>0) from[i]=idx[pos[i]-1];
    }
    vector<int> res; int cur=idx[d.size()-1];
    while(cur!=-1){ res.push_back(a[cur]); cur=from[cur]; }
    reverse(res.begin(),res.end()); return res;
}

// ─── Knapsack ─────────────────────────────────────────────────────────────────
// 0/1 Knapsack: каждый предмет берём не более 1 раза
// Когда: оптимальный выбор предметов с весовым ограничением
vector<long long> knapsack01(vector<int>& w, vector<long long>& v, int W) {
    vector<long long> dp(W+1,0);
    for(int i=0;i<(int)w.size();i++)
        for(int j=W;j>=w[i];j--)
            dp[j]=max(dp[j],dp[j-w[i]]+v[i]);
    return dp; // dp[W] — максимальная стоимость
}

// Unbounded Knapsack: каждый предмет можно брать сколько угодно раз
// Когда: размен монет, задачи с повторяющимися предметами
vector<long long> knapsackUnbound(vector<int>& w, vector<long long>& v, int W) {
    vector<long long> dp(W+1,0);
    for(int j=1;j<=W;j++)
        for(int i=0;i<(int)w.size();i++)
            if(w[i]<=j) dp[j]=max(dp[j],dp[j-w[i]]+v[i]);
    return dp;
}

// ─── Digit DP ─────────────────────────────────────────────────────────────────
// Когда: подсчёт чисел от L до R с каким-то свойством (сумма цифр, делимость, ...)
// Пример: количество чисел в [0, n] с суммой цифр == target
// Адаптируй state под задачу
string digitN;
int digitTarget;
map<tuple<int,int,bool,bool>,long long> digitMemo;

long long digitDp(int pos, int sum, bool tight, bool started) {
    if(sum<0) return 0;
    if(pos==(int)digitN.size()) return (started && sum==digitTarget) ? 1 : 0;
    auto key=make_tuple(pos,sum,tight,started);
    auto it=digitMemo.find(key); if(it!=digitMemo.end()) return it->second;
    int lim=tight?digitN[pos]-'0':9;
    long long res=0;
    for(int d=0;d<=lim;d++)
        res+=digitDp(pos+1,started?sum-d:sum,tight&&d==lim,started||d>0);
    return digitMemo[key]=res;
}
long long countDigit(long long n, int target) {
    digitN=to_string(n); digitTarget=target; digitMemo.clear();
    return digitDp(0,target,true,false);
}
// Использование: countDigit(R,t) - countDigit(L-1,t)

// ─── SOS DP (Sum over Subsets) ────────────────────────────────────────────────
// Когда: для каждой маски найти сумму/max по всем подмаскам; AND-свёртки, покрытия
// f[mask] = сумма a[sub] для всех sub ⊆ mask
vector<long long> sosDp(vector<long long>& a, int BITS) {
    int N=1<<BITS;
    vector<long long> f(a.begin(),a.end());
    for(int i=0;i<BITS;i++)
        for(int mask=0;mask<N;mask++)
            if(mask>>i&1) f[mask]+=f[mask^(1<<i)];
    return f;
}

// ─── Interval DP ──────────────────────────────────────────────────────────────
// Когда: оптимальное разбиение отрезка (умножение матриц, игры на отрезке, разбиение строки)
// dp[l][r] — оптимальный ответ для отрезка [l,r]
// Пример: минимальная стоимость умножения матриц (размеры в массиве sz)
long long matChain(vector<int>& sz) {
    int n=sz.size()-1;
    vector<vector<long long>> dp(n,vector<long long>(n,0));
    for(int len=2;len<=n;len++)
        for(int l=0;l+len-1<n;l++){
            int r=l+len-1;
            dp[l][r]=1e18;
            for(int k=l;k<r;k++)
                dp[l][r]=min(dp[l][r],dp[l][k]+dp[k+1][r]+(long long)sz[l]*sz[k+1]*sz[r+1]);
        }
    return dp[0][n-1];
}

// ─── DP на дереве + Rerooting ─────────────────────────────────────────────────
// Когда: задачи на деревьях где ответ в каждой вершине зависит от поддерева/всего дерева
// Шаблон rerooting: dp1[v] — ответ для поддерева, dp2[v] — ответ для всего дерева
// Пример: сумма расстояний от каждой вершины до всех остальных
const int MAXN=200005;
vector<int> children[MAXN];
long long dp1[MAXN], dp2[MAXN]; // dp1=сумма в поддереве, dp2=ответ с учётом всего дерева
int sz[MAXN];

void dfs1(int v, int p) {
    sz[v]=1; dp1[v]=0;
    for(int u:children[v]) if(u!=p){
        dfs1(u,v);
        dp1[v]+=dp1[u]+sz[u];
        sz[v]+=sz[u];
    }
}
void dfs2(int v, int p, int n) {
    for(int u:children[v]) if(u!=p){
        // dp2[u] = dp2[v] + (n - sz[u]) - sz[u]  (для суммы расстояний)
        dp2[u]=dp2[v]+(n-sz[u])-sz[u];
        dfs2(u,v,n);
    }
}
// Инициализация: dfs1(0,-1); dp2[0]=dp1[0]; dfs2(0,-1,n);
// Ответ для v: dp2[v] + dp1[v]  (для суммы расстояний)

// ─── Convex Hull Trick (CHT) ──────────────────────────────────────────────────
// Когда: dp[i] = min/max(dp[j] + f(j)*g(i)) — оптимизирует O(n²) до O(n log n) или O(n)
// Предположение: прямые добавляются в порядке убывания/возрастания наклона
struct CHT {
    struct Line { long long m, b; long long eval(long long x){ return m*x+b; } };
    deque<Line> hull;
    bool bad(Line l1, Line l2, Line l3){
        return (__int128)(l3.b-l1.b)*(l1.m-l2.m) <= (__int128)(l2.b-l1.b)*(l1.m-l3.m);
    }
    void add(long long m, long long b){ // добавляй в порядке убывания m для min
        Line l={m,b};
        while(hull.size()>=2 && bad(hull[hull.size()-2],hull.back(),l)) hull.pop_back();
        hull.push_back(l);
    }
    long long query(long long x){ // запрос минимума (монотонный x — удаляй front)
        while(hull.size()>=2 && hull[0].eval(x)>=hull[1].eval(x)) hull.pop_front();
        return hull.front().eval(x);
    }
};

// ─── Li Chao Tree ─────────────────────────────────────────────────────────────
// Когда: CHT с произвольным порядком добавления прямых и запросов
struct LiChao {
    struct Line { long long m,b; long long eval(long long x){ return m*x+b; } };
    struct Node { Line line; int l,r; };
    vector<Node> t; long long lo, hi;
    LiChao(long long lo, long long hi): lo(lo), hi(hi) {
        t.push_back({{0,(long long)2e18},-1,-1});
    }
    void add(int v, long long l, long long r, Line line){
        long long mid=(l+r)/2;
        bool left=line.eval(l)<t[v].line.eval(l);
        bool mid_=line.eval(mid)<t[v].line.eval(mid);
        if(mid_) swap(t[v].line,line);
        if(l==r) return;
        if(left!=mid_){
            if(t[v].l==-1){ t.push_back({{0,(long long)2e18},-1,-1}); t[v].l=t.size()-1; }
            add(t[v].l,l,mid,line);
        } else {
            if(t[v].r==-1){ t.push_back({{0,(long long)2e18},-1,-1}); t[v].r=t.size()-1; }
            add(t[v].r,mid+1,r,line);
        }
    }
    void add(long long m, long long b){ add(0,lo,hi,{m,b}); }
    long long query(int v, long long l, long long r, long long x){
        long long res=t[v].line.eval(x), mid=(l+r)/2;
        if(l==r) return res;
        if(x<=mid && t[v].l!=-1) res=min(res,query(t[v].l,l,mid,x));
        if(x>mid  && t[v].r!=-1) res=min(res,query(t[v].r,mid+1,r,x));
        return res;
    }
    long long query(long long x){ return query(0,lo,hi,x); }
};

// ─── Divide & Conquer DP ──────────────────────────────────────────────────────
// Когда: dp[i][j] = min(dp[i-1][k] + cost(k,j)) и opt[i][j] <= opt[i][j+1]
// (монотонность оптимального разбиения) — O(n² log n) → O(n log n)
// cost(l,r) нужно реализовать под задачу
vector<vector<long long>> dcDp;
auto dcCost=[](int l,int r)->long long{ return 0; }; // заменить под задачу

void dcSolve(int layer, int lo, int hi, int optLo, int optHi, vector<long long>& prev, vector<long long>& cur){
    if(lo>hi) return;
    int mid=(lo+hi)/2, opt=optLo;
    cur[mid]=LLONG_MAX;
    for(int k=optLo;k<=min(mid,optHi);k++){
        long long val=(prev[k]==LLONG_MAX)?LLONG_MAX:prev[k]+dcCost(k,mid);
        if(val<cur[mid]){ cur[mid]=val; opt=k; }
    }
    dcSolve(layer,lo,mid-1,optLo,opt,prev,cur);
    dcSolve(layer,mid+1,hi,opt,optHi,prev,cur);
}

int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);
}
