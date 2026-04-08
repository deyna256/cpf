#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef vector<vector<ll>> Mat;

// ─── GCD / Extended GCD ───────────────────────────────────────────────────────
// Когда: НОД, обратный элемент по модулю, уравнение ax+by=gcd(a,b)
ll gcd(ll a, ll b) { return b?gcd(b,a%b):a; }
ll lcm(ll a, ll b) { return a/gcd(a,b)*b; }

// Расширенный: возвращает gcd, x и y такие что a*x + b*y = gcd(a,b)
ll extgcd(ll a, ll b, ll &x, ll &y) {
    if(!b){ x=1; y=0; return a; }
    ll x1,y1; ll g=extgcd(b,a%b,x1,y1);
    x=y1; y=x1-(a/b)*y1; return g;
}

// Обратный элемент a по mod m (существует только если gcd(a,m)=1)
ll modinv(ll a, ll m) { ll x,y; extgcd(a,m,x,y); return (x%m+m)%m; }

// ─── Комбинаторика с предподсчётом ───────────────────────────────────────────
// Когда: nCr mod p, перестановки, количество путей — при многих запросах
const ll MOD=1e9+7;
const int MAXF=2000005;
ll fact[MAXF], inv_fact[MAXF];

void precompFact(){
    fact[0]=1;
    for(int i=1;i<MAXF;i++) fact[i]=fact[i-1]*i%MOD;
    inv_fact[MAXF-1]=modinv(fact[MAXF-1],MOD);
    for(int i=MAXF-2;i>=0;i--) inv_fact[i]=inv_fact[i+1]*(i+1)%MOD;
}

ll C(int n, int k) {
    if(k<0||k>n) return 0;
    return fact[n]%MOD*inv_fact[k]%MOD*inv_fact[n-k]%MOD;
}
ll P(int n, int k) { // перестановки A(n,k)
    if(k<0||k>n) return 0;
    return fact[n]%MOD*inv_fact[n-k]%MOD;
}

// ─── Теорема Лукаса (Lucas) ───────────────────────────────────────────────────
// Когда: C(n,k) mod p для очень больших n, но маленького простого p
ll lucasC(ll n, ll k, ll p){
    if(k==0) return 1;
    return lucasC(n/p,k/p,p)*C(n%p,k%p)%p;
}

// ─── Числа Каталана ──────────────────────────────────────────────────────────
// Когда: правильные скобочные последовательности, BST, триангуляции полигонов
// Cat(n) = C(2n,n)/(n+1)
ll catalan(int n){ return C(2*n,n)%MOD*modinv(n+1,MOD)%MOD; }

// ─── Включения-исключения ─────────────────────────────────────────────────────
// Когда: подсчёт элементов с хотя бы одним / ни одним из свойств
// |A∪B∪C| = |A|+|B|+|C| - |A∩B| - |A∩C| - |B∩C| + |A∩B∩C|
// Шаблон по маскам для k свойств:
ll inclusionExclusion(vector<ll>& cnt) { // cnt[mask] = |пересечение свойств в маске|
    int k=cnt.size(); ll res=0;
    for(int mask=1;mask<(1<<k);mask++){
        ll sign=(__builtin_popcount(mask)%2)?1:-1;
        res+=sign*cnt[mask];
    }
    return res;
}

// ─── Числа Стирлинга 2-го рода ────────────────────────────────────────────────
// Когда: разбиение n элементов на k непустых групп
// S(n,k) = k*S(n-1,k) + S(n-1,k-1)
vector<vector<ll>> stirling2(int n){
    vector<vector<ll>> S(n+1,vector<ll>(n+1,0)); S[0][0]=1;
    for(int i=1;i<=n;i++)
        for(int j=1;j<=i;j++)
            S[i][j]=(j*S[i-1][j]+S[i-1][j-1])%MOD;
    return S;
}

// ─── Matrix Exponentiation ────────────────────────────────────────────────────
// Когда: числа Фибоначчи за O(log n), линейные рекуррентности, подсчёт путей в графе
Mat mul(const Mat& A, const Mat& B, ll mod){
    int n=A.size(); Mat C(n,vector<ll>(n,0));
    for(int i=0;i<n;i++) for(int k=0;k<n;k++) if(A[i][k])
        for(int j=0;j<n;j++) C[i][j]=(C[i][j]+A[i][k]*B[k][j])%mod;
    return C;
}
Mat matpow(Mat A, ll p, ll mod){
    int n=A.size(); Mat R(n,vector<ll>(n,0));
    for(int i=0;i<n;i++) R[i][i]=1; // единичная
    for(;p;p>>=1){ if(p&1) R=mul(R,A,mod); A=mul(A,A,mod); }
    return R;
}
// Фибоначчи: [[1,1],[1,0]]^n => fib(n)

// ─── CRT (Китайская теорема об остатках) ─────────────────────────────────────
// Когда: x ≡ r1 (mod m1), x ≡ r2 (mod m2), ... — найти x (mod lcm)
// Возвращает {x, m} — решение x ≡ r (mod m), или {0,0} если несовместимо
pair<ll,ll> crt(ll r1, ll m1, ll r2, ll m2){
    ll x,y; ll g=extgcd(m1,m2,x,y);
    if((r2-r1)%g!=0) return {0,0};
    ll lcm=m1/g*m2;
    ll ans=(r1+(r2-r1)/g%( m2/g)*x%( m2/g)*m1)%lcm;
    return {(ans%lcm+lcm)%lcm, lcm};
}

// ─── NTT (Number Theoretic Transform) ────────────────────────────────────────
// Когда: умножение полиномов по модулю, свёртки — точнее FFT (нет float ошибок)
const ll NTTMOD=998244353, g_ntt=3; // g — первообразный корень

ll pw(ll a, ll b, ll mod){ ll r=1; a%=mod; for(;b;b>>=1){if(b&1)r=r*a%mod;a=a*a%mod;} return r; }

void ntt(vector<ll>& a, bool inv){
    int n=a.size();
    for(int i=1,j=0;i<n;i++){
        int bit=n>>1;
        for(;j&bit;bit>>=1) j^=bit;
        j^=bit; if(i<j) swap(a[i],a[j]);
    }
    for(int len=2;len<=n;len<<=1){
        ll w=inv?pw(g_ntt,NTTMOD-1-(NTTMOD-1)/len,NTTMOD):pw(g_ntt,(NTTMOD-1)/len,NTTMOD);
        for(int i=0;i<n;i+=len){
            ll wn=1;
            for(int j=0;j<len/2;j++){
                ll u=a[i+j], v=a[i+j+len/2]*wn%NTTMOD;
                a[i+j]=(u+v)%NTTMOD; a[i+j+len/2]=(u-v+NTTMOD)%NTTMOD;
                wn=wn*w%NTTMOD;
            }
        }
    }
    if(inv){ ll ni=pw(n,NTTMOD-2,NTTMOD); for(auto& x:a) x=x*ni%NTTMOD; }
}
vector<ll> polyMul(vector<ll> a, vector<ll> b){
    int res=a.size()+b.size()-1,n=1;
    while(n<res) n<<=1;
    a.resize(n); b.resize(n);
    ntt(a,false); ntt(b,false);
    for(int i=0;i<n;i++) a[i]=a[i]*b[i]%NTTMOD;
    ntt(a,true); a.resize(res); return a;
}

// ─── Miller-Rabin + Pollard's rho ────────────────────────────────────────────
// Когда: проверка простоты больших чисел, факторизация за O(n^1/4)
ll mulmod(ll a, ll b, ll m){ return (__int128)a*b%m; }

bool millerRabin(ll n, ll a){
    if(n%a==0) return n==a;
    ll d=n-1; int r=0;
    while(d%2==0) d>>=1, r++;
    ll x=pw(a,d,n);
    if(x==1||x==n-1) return true;
    for(int i=0;i<r-1;i++){ x=mulmod(x,x,n); if(x==n-1) return true; }
    return false;
}
bool isPrime(ll n){
    if(n<2) return false;
    for(ll a:{2,3,5,7,11,13,17,19,23,29,31,37}) if(!millerRabin(n,a)) return false;
    return true;
}

ll pollardRho(ll n){
    if(n%2==0) return 2;
    ll x=rand()%(n-2)+2, y=x, c=rand()%(n-1)+1, d=1;
    while(d==1){ x=( mulmod(x,x,n)+c)%n; y=(mulmod(y,y,n)+c)%n; y=(mulmod(y,y,n)+c)%n; d=gcd(abs(x-y),n); }
    return d==n?pollardRho(n):d;
}
map<ll,int> factorize(ll n){
    map<ll,int> res;
    function<void(ll)> f=[&](ll n){
        if(n==1) return;
        if(isPrime(n)){res[n]++;return;}
        ll d=n;
        while(d==n) d=pollardRho(n);
        f(d); f(n/d);
    };
    f(n); return res;
}

int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);
    precompFact();
}
