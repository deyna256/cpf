#include <bits/stdc++.h>
using namespace std;
typedef long long ll;

// ─── DSU (Union-Find) ─────────────────────────────────────────────────────────
// Когда: компоненты связности, MST (Kruskal), offline LCA, динамическая связность
struct DSU {
    vector<int> p, rnk; vector<int> sz;
    DSU(int n): p(n), rnk(n,0), sz(n,1) { iota(p.begin(),p.end(),0); }
    int find(int x){ return p[x]==x?x:p[x]=find(p[x]); }
    bool unite(int a, int b){
        a=find(a); b=find(b); if(a==b) return false;
        if(rnk[a]<rnk[b]) swap(a,b);
        p[b]=a; sz[a]+=sz[b];
        if(rnk[a]==rnk[b]) rnk[a]++;
        return true;
    }
    bool same(int a,int b){ return find(a)==find(b); }
    int size(int a){ return sz[find(a)]; }
};

// ─── Fenwick Tree (BIT) ───────────────────────────────────────────────────────
// Когда: prefix sums с точечными обновлениями, инверсии, порядковые статистики
struct BIT {
    int n; vector<ll> t;
    BIT(int n): n(n), t(n+1,0){}
    void update(int i, ll v){ for(i++;i<=n;i+=i&-i) t[i]+=v; }
    ll query(int i){ ll s=0; for(i++;i>0;i-=i&-i) s+=t[i]; return s; }
    ll query(int l, int r){ return query(r)-( l?query(l-1):0); } // [l,r]
};

// 2D BIT
// Когда: 2D prefix sums с обновлениями (прямоугольные запросы)
struct BIT2D {
    int n,m; vector<vector<ll>> t;
    BIT2D(int n,int m): n(n),m(m),t(n+1,vector<ll>(m+1,0)){}
    void update(int x,int y,ll v){ for(int i=x+1;i<=n;i+=i&-i) for(int j=y+1;j<=m;j+=j&-j) t[i][j]+=v; }
    ll query(int x,int y){ ll s=0; for(int i=x+1;i>0;i-=i&-i) for(int j=y+1;j>0;j-=j&-j) s+=t[i][j]; return s; }
    ll query(int x1,int y1,int x2,int y2){ // [x1,x2]x[y1,y2]
        return query(x2,y2)-( x1?query(x1-1,y2):0)-(y1?query(x2,y1-1):0)+(x1&&y1?query(x1-1,y1-1):0);
    }
};

// ─── Segment Tree (точечное обновление, range query) ─────────────────────────
// Когда: range min/max/sum/gcd без range update; если нужен range update — см. lazy_seg_tree.cpp
template<class T, class F=function<T(T,T)>>
struct SegTree {
    int n; vector<T> t; T id; F op;
    SegTree(int n, T id, F op): n(n), t(2*n,id), id(id), op(op){}
    void build(vector<T>& a){ for(int i=0;i<n;i++) t[i+n]=a[i]; for(int i=n-1;i>0;i--) t[i]=op(t[2*i],t[2*i+1]); }
    void update(int i,T v){ t[i+=n]=v; for(i>>=1;i>0;i>>=1) t[i]=op(t[2*i],t[2*i+1]); }
    T query(int l,int r){ // [l,r]
        T lo=id,hi=id;
        for(l+=n,r+=n+1;l<r;l>>=1,r>>=1){
            if(l&1) lo=op(lo,t[l++]);
            if(r&1) hi=op(t[--r],hi);
        }
        return op(lo,hi);
    }
};
// Использование: SegTree<int> st(n, INT_MAX, [](int a,int b){return min(a,b);});

// ─── Sparse Table (RMQ, O(n log n) build, O(1) query) ────────────────────────
// Когда: статичный массив, много запросов min/max/gcd (без обновлений)
struct SparseTable {
    vector<vector<int>> t; vector<int> log2_;
    SparseTable(vector<int>& a){
        int n=a.size(); int LOG=__lg(n)+1;
        t.assign(LOG,vector<int>(n)); t[0]=a;
        log2_.resize(n+1); log2_[1]=0;
        for(int i=2;i<=n;i++) log2_[i]=log2_[i/2]+1;
        for(int j=1;j<LOG;j++)
            for(int i=0;i+(1<<j)<=n;i++)
                t[j][i]=min(t[j-1][i],t[j-1][i+(1<<(j-1))]);
    }
    int query(int l,int r){ int k=log2_[r-l+1]; return min(t[k][l],t[k][r-(1<<k)+1]); }
};

// ─── Implicit Treap ───────────────────────────────────────────────────────────
// Когда: операции на отрезках с произвольными вставками/удалениями/разворотами;
//        замена std::rope, реализация deque с merge/split
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
struct Treap {
    struct Node {
        int val, pri, sz; bool rev;
        Node *l, *r;
        Node(int v): val(v), pri(rng()), sz(1), rev(false), l(nullptr), r(nullptr){}
    };
    Node* root=nullptr;

    int sz(Node* t){ return t?t->sz:0; }
    void upd(Node* t){ if(t) t->sz=1+sz(t->l)+sz(t->r); }
    void push(Node* t){
        if(t&&t->rev){
            swap(t->l,t->r);
            if(t->l) t->l->rev^=1;
            if(t->r) t->r->rev^=1;
            t->rev=false;
        }
    }
    // split по размеру: l имеет k элементов
    pair<Node*,Node*> split(Node* t, int k){
        if(!t) return {nullptr,nullptr};
        push(t);
        if(sz(t->l)>=k){ auto [l,r]=split(t->l,k); t->l=r; upd(t); return {l,t}; }
        else { auto [l,r]=split(t->r,k-sz(t->l)-1); t->r=l; upd(t); return {t,r}; }
    }
    Node* merge(Node* l, Node* r){
        if(!l) return r; if(!r) return l;
        push(l); push(r);
        if(l->pri>r->pri){ l->r=merge(l->r,r); upd(l); return l; }
        else { r->l=merge(l,r->l); upd(r); return r; }
    }
    void insert(int pos, int val){ // вставить val на позицию pos (0-indexed)
        auto [l,r]=split(root,pos);
        root=merge(merge(l,new Node(val)),r);
    }
    void erase(int pos){
        auto [l,r]=split(root,pos);
        auto [_,rr]=split(r,1);
        root=merge(l,rr);
    }
    void reverse(int l, int r){ // разворот отрезка [l,r]
        auto [a,b]=split(root,l);
        auto [c,d]=split(b,r-l+1);
        c->rev^=1;
        root=merge(a,merge(c,d));
    }
    int kth(int k){ // k-й элемент (0-indexed)
        Node* t=root;
        while(t){ push(t); int ls=sz(t->l); if(ls==k) return t->val; if(ls>k) t=t->l; else { k-=ls+1; t=t->r; } }
        return -1;
    }
};

// ─── Persistent Segment Tree ──────────────────────────────────────────────────
// Когда: k-й минимум на отрезке, offline запросы к версиям массива
struct PersistSeg {
    struct Node { int l,r,cnt; };
    vector<Node> t; vector<int> roots;
    int n; // размер координатного сжатия
    PersistSeg(int n): n(n){ t.push_back({0,0,0}); roots.push_back(0); }

    int build(int l,int r){ // не обязательно, можно начать с пустого корня
        int v=t.size(); t.push_back({0,0,0});
        if(l==r) return v;
        int m=(l+r)/2; t[v].l=build(l,m); t[v].r=build(m+1,r); return v;
    }
    int update(int prev, int l, int r, int pos){
        int v=t.size(); t.push_back(t[prev]); t[v].cnt++;
        if(l==r) return v;
        int m=(l+r)/2;
        if(pos<=m) t[v].l=update(t[prev].l,l,m,pos);
        else       t[v].r=update(t[prev].r,m+1,r,pos);
        return v;
    }
    void add(int pos){ roots.push_back(update(roots.back(),0,n-1,pos)); }

    // k-й по величине на отрезке версий [ql..qr] (1-indexed версии)
    int kth(int ql, int qr, int k){
        int u=roots[ql-1], v=roots[qr], l=0, r=n-1;
        while(l<r){
            int m=(l+r)/2, cnt=t[t[v].l].cnt-t[t[u].l].cnt;
            if(cnt>=k){ u=t[u].l; v=t[v].l; r=m; }
            else { k-=cnt; u=t[u].r; v=t[v].r; l=m+1; }
        }
        return l; // возвращает индекс в сжатых координатах
    }
};

// ─── Trie ─────────────────────────────────────────────────────────────────────
// Когда: поиск/подсчёт строк по префиксу, XOR-задачи (XOR trie на битах числа)
struct Trie {
    vector<array<int,26>> ch; vector<int> cnt;
    Trie(){ ch.push_back({}); ch[0].fill(-1); cnt.push_back(0); }
    void insert(const string& s){
        int v=0;
        for(char c:s){
            int x=c-'a';
            if(ch[v][x]==-1){ ch[v][x]=ch.size(); ch.push_back({}); ch.back().fill(-1); cnt.push_back(0); }
            v=ch[v][x]; cnt[v]++;
        }
    }
    int count(const string& s){ // сколько строк имеют s как префикс
        int v=0;
        for(char c:s){ int x=c-'a'; if(ch[v][x]==-1) return 0; v=ch[v][x]; }
        return cnt[v];
    }
};

// XOR Trie (для задач на максимальный XOR)
// Когда: максимальный XOR пары в массиве, запросы вида max(a[i] XOR x)
struct XorTrie {
    vector<array<int,2>> ch; vector<int> cnt;
    XorTrie(){ ch.push_back({}); ch[0].fill(-1); cnt.push_back(0); }
    void insert(int x, int BITS=30){
        int v=0;
        for(int i=BITS;i>=0;i--){
            int b=(x>>i)&1;
            if(ch[v][b]==-1){ ch[v][b]=ch.size(); ch.push_back({}); ch.back().fill(-1); cnt.push_back(0); }
            v=ch[v][b]; cnt[v]++;
        }
    }
    int maxXor(int x, int BITS=30){
        int v=0, res=0;
        for(int i=BITS;i>=0;i--){
            int b=(x>>i)&1, want=1-b;
            if(ch[v][want]!=-1){ res|=(1<<i); v=ch[v][want]; }
            else if(ch[v][b]!=-1) v=ch[v][b];
            else break;
        }
        return res;
    }
};

// ─── Mo's Algorithm ───────────────────────────────────────────────────────────
// Когда: offline запросы на отрезках, когда добавить/удалить элемент O(1) или O(log n)
// Сложность: O((n+q)*sqrt(n))
struct Mo {
    int n; vector<array<int,3>> queries; // {l,r,idx}
    Mo(int n): n(n){}
    void add(int l, int r, int idx){ queries.push_back({l,r,idx}); }
    // Использование: mo.solve([&](int i){...}, [&](int i){...}, [&](int i){...}, [&](int i){...}, [&]()->int{...}, ans);
    template<class F1,class F2,class F3,class F4,class F5,class T>
    void solve(F1 addL, F2 addR, F3 remL, F4 remR, F5 getAns, vector<T>& ans){
        int block=max(1,(int)sqrt(n));
        sort(queries.begin(),queries.end(),[&](auto& a,auto& b){
            int ba=a[0]/block, bb=b[0]/block;
            if(ba!=bb) return ba<bb;
            return (ba&1)?a[1]>b[1]:a[1]<b[1];
        });
        int l=0,r=-1;
        for(auto& q:queries){
            while(r<q[1]) addR(++r);
            while(l>q[0]) addL(--l);
            while(r>q[1]) remR(r--);
            while(l<q[0]) remL(l++);
            ans[q[2]]=getAns();
        }
    }
};

int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);
}
