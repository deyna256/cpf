#include <bits/stdc++.h>
using namespace std;

// ─── Z-функция ────────────────────────────────────────────────────────────────
// Когда: поиск паттерна в тексте, подсчёт вхождений, периоды строки
vector<int> zFunc(const string& s) {
    int n=s.size(); vector<int> z(n,0); z[0]=n;
    for(int i=1,l=0,r=0;i<n;i++){
        if(i<r) z[i]=min(r-i,z[i-l]);
        while(i+z[i]<n && s[z[i]]==s[i+z[i]]) z[i]++;
        if(i+z[i]>r) l=i, r=i+z[i];
    }
    return z;
}
// Поиск pattern в text: строим s = pattern + "#" + text, ищем z[i] == pattern.size()

// ─── Polynomial Hashing ───────────────────────────────────────────────────────
// Когда: быстрое сравнение подстрок, поиск палиндромов, сравнение циклических сдвигов
// Double hash снижает вероятность коллизии до ~0
const long long MOD1=1e9+7, MOD2=1e9+9, BASE1=131, BASE2=137;
struct Hasher {
    int n; vector<long long> h1,h2,p1,p2;
    Hasher(const string& s): n(s.size()),h1(n+1),h2(n+1),p1(n+1),p2(n+1){
        p1[0]=p2[0]=1;
        for(int i=0;i<n;i++){
            h1[i+1]=(h1[i]*BASE1+s[i])%MOD1;
            h2[i+1]=(h2[i]*BASE2+s[i])%MOD2;
            p1[i+1]=p1[i]*BASE1%MOD1;
            p2[i+1]=p2[i]*BASE2%MOD2;
        }
    }
    // hash подстроки [l,r] (0-indexed, включительно)
    pair<long long,long long> get(int l, int r){
        long long v1=(h1[r+1]-h1[l]*p1[r-l+1]%MOD1+MOD1*2)%MOD1;
        long long v2=(h2[r+1]-h2[l]*p2[r-l+1]%MOD2+MOD2*2)%MOD2;
        return {v1,v2};
    }
};

// ─── Manacher (все палиндромы) ────────────────────────────────────────────────
// Когда: длиннейший палиндром, подсчёт палиндромных подстрок, все центры палиндромов
// d1[i] — длина нечётных палиндромов с центром i, d2[i] — чётных
pair<vector<int>,vector<int>> manacher(const string& s) {
    int n=s.size();
    vector<int> d1(n),d2(n);
    // нечётные
    for(int i=0,l=0,r=-1;i<n;i++){
        int k=(i>r)?1:min(d1[l+r-i],r-i+1);
        while(i-k>=0&&i+k<n&&s[i-k]==s[i+k]) k++;
        d1[i]=k--; if(i+k>r) l=i-k,r=i+k;
    }
    // чётные
    for(int i=0,l=0,r=-1;i<n;i++){
        int k=(i>r)?0:min(d2[l+r-i+1],r-i+1);
        while(i-k-1>=0&&i+k<n&&s[i-k-1]==s[i+k]) k++;
        d2[i]=k--; if(k>=0&&i+k>r) l=i-k-1,r=i+k;
    }
    return {d1,d2};
    // палиндром нечётной длины с центром i: s[i-d1[i]+1..i+d1[i]-1]
    // палиндром чётной длины с центром между i-1 и i: длина 2*d2[i]
}

// ─── Suffix Array + LCP (O(n log n)) ─────────────────────────────────────────
// Когда: поиск подстрок, наидлиннейшая общая подстрока, подсчёт уникальных подстрок
struct SuffixArray {
    int n; vector<int> sa, rank_, lcp;
    SuffixArray(const string& s): n(s.size()), sa(n), rank_(n), lcp(n) {
        iota(sa.begin(),sa.end(),0);
        for(int i=0;i<n;i++) rank_[i]=s[i];
        for(int gap=1;;gap<<=1){
            auto cmp=[&](int a,int b){
                if(rank_[a]!=rank_[b]) return rank_[a]<rank_[b];
                int ra=a+gap<n?rank_[a+gap]:-1;
                int rb=b+gap<n?rank_[b+gap]:-1;
                return ra<rb;
            };
            sort(sa.begin(),sa.end(),cmp);
            vector<int> tmp(n); tmp[sa[0]]=0;
            for(int i=1;i<n;i++) tmp[sa[i]]=tmp[sa[i-1]]+(cmp(sa[i-1],sa[i])?1:0);
            rank_=tmp;
            if(rank_[sa[n-1]]==n-1) break;
        }
        // LCP (алгоритм Касаи)
        vector<int> inv(n); for(int i=0;i<n;i++) inv[sa[i]]=i;
        for(int i=0,k=0;i<n;i++){
            if(inv[i]==0){k=0;continue;}
            int j=sa[inv[i]-1];
            while(i+k<n&&j+k<n&&s[i+k]==s[j+k]) k++;
            lcp[inv[i]]=k; if(k) k--;
        }
    }
    // Число уникальных подстрок: n*(n+1)/2 - sum(lcp)
    long long countUnique(){
        long long res=(long long)n*(n+1)/2;
        for(int x:lcp) res-=x;
        return res;
    }
};

// ─── Aho-Corasick ─────────────────────────────────────────────────────────────
// Когда: поиск множества паттернов в тексте, подсчёт вхождений каждого паттерна
struct AhoCorasick {
    vector<array<int,26>> go;
    vector<int> fail, out; // out[v] — индекс паттерна (или -1)
    AhoCorasick(){ go.push_back({}); go[0].fill(-1); fail.push_back(0); out.push_back(-1); }

    int addPattern(const string& s, int id) {
        int cur=0;
        for(char c:s){
            int ch=c-'a';
            if(go[cur][ch]==-1){
                go[cur][ch]=go.size();
                go.push_back({}); go.back().fill(-1);
                fail.push_back(0); out.push_back(-1);
            }
            cur=go[cur][ch];
        }
        out[cur]=id; return cur;
    }

    void build(){
        queue<int> q;
        for(int c=0;c<26;c++){
            if(go[0][c]==-1) go[0][c]=0;
            else { fail[go[0][c]]=0; q.push(go[0][c]); }
        }
        while(!q.empty()){
            int v=q.front(); q.pop();
            if(out[v]==-1) out[v]=out[fail[v]]; // суффиксная ссылка на совпадение
            for(int c=0;c<26;c++){
                if(go[v][c]==-1) go[v][c]=go[fail[v]][c];
                else { fail[go[v][c]]=go[fail[v]][c]; q.push(go[v][c]); }
            }
        }
    }

    // Обход текста: возвращает для каждой позиции индекс найденного паттерна (или -1)
    vector<int> search(const string& text){
        int cur=0; vector<int> res;
        for(char c:text){
            cur=go[cur][c-'a'];
            res.push_back(out[cur]);
        }
        return res;
    }
};

// ─── Suffix Automaton (SAM) ───────────────────────────────────────────────────
// Когда: наидлиннейшая общая подстрока двух строк, подсчёт вхождений подстроки,
//        число различных подстрок, LCS нескольких строк
struct SAM {
    struct State { int len, link; map<char,int> next; };
    vector<State> st; int last;
    SAM(){ st.push_back({0,-1,{}}); last=0; }
    void extend(char c){
        int cur=st.size(); st.push_back({st[last].len+1,-1,{}});
        int p=last;
        while(p!=-1&&!st[p].next.count(c)){ st[p].next[c]=cur; p=st[p].link; }
        if(p==-1) st[cur].link=0;
        else {
            int q=st[p].next[c];
            if(st[p].len+1==st[q].len) st[cur].link=q;
            else {
                int clone=st.size(); st.push_back({st[p].len+1,st[q].link,st[q].next});
                while(p!=-1&&st[p].next.count(c)&&st[p].next[c]==q){ st[p].next[c]=clone; p=st[p].link; }
                st[q].link=st[cur].link=clone;
            }
        }
        last=cur;
    }
    void build(const string& s){ for(char c:s) extend(c); }
};

int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);
}
