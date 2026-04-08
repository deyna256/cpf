#include <bits/stdc++.h>
using namespace std;

typedef double ld;
const ld EPS = 1e-9;
const ld PI = acos((ld)-1);

// ─── Point ────────────────────────────────────────────────────────────────────
// Когда: базовая структура для любой 2D геометрии; cross=знак поворота, dot=угол/проекция
struct P {
    ld x, y;
    P(ld x=0, ld y=0): x(x), y(y) {}
    P operator+(P o) const { return {x+o.x, y+o.y}; }
    P operator-(P o) const { return {x-o.x, y-o.y}; }
    P operator*(ld t) const { return {x*t, y*t}; }
    bool operator<(P o) const { return x<o.x || (x==o.x && y<o.y); }
    bool operator==(P o) const { return fabs(x-o.x)<EPS && fabs(y-o.y)<EPS; }
    ld dot(P o) const { return x*o.x + y*o.y; }
    ld cross(P o) const { return x*o.y - y*o.x; }
    ld norm() const { return sqrt(x*x + y*y); }
    ld norm2() const { return x*x + y*y; }
    P rot90() const { return {-y, x}; }
    P rot(ld a) const { return {x*cos(a)-y*sin(a), x*sin(a)+y*cos(a)}; }
    P unit() const { ld n=norm(); return {x/n, y/n}; }
};

ld dist(P a, P b) { return (a-b).norm(); }
int sign(ld x) { return (x>EPS)-(x<-EPS); }

// ─── Line / Segment ───────────────────────────────────────────────────────────
// Когда: пересечения прямых/отрезков, расстояния, проверка коллинеарности
struct Line { P a, b; }; // направление: b-a

// Пересечение прямых (точка). Вернёт false если параллельны.
bool lineIntersect(P a, P b, P c, P d, P &res) {
    ld d1 = (b-a).cross(d-c);
    if (fabs(d1) < EPS) return false;
    ld t = (c-a).cross(d-c) / d1;
    res = a + (b-a)*t;
    return true;
}

// Расстояние от точки p до прямой (a,b)
ld distToLine(P p, P a, P b) {
    return fabs((b-a).cross(p-a)) / (b-a).norm();
}

// Проекция p на прямую (a,b)
P projLine(P p, P a, P b) {
    P d = b-a;
    return a + d * (d.dot(p-a) / d.norm2());
}

// Расстояние от точки p до отрезка [a,b]
ld distToSeg(P p, P a, P b) {
    if ((b-a).dot(p-a) <= 0) return dist(p,a);
    if ((a-b).dot(p-b) <= 0) return dist(p,b);
    return distToLine(p,a,b);
}

// Пересекаются ли отрезки [a,b] и [c,d]
bool segIntersect(P a, P b, P c, P d) {
    ld d1=(b-a).cross(c-a), d2=(b-a).cross(d-a);
    ld d3=(d-c).cross(a-c), d4=(d-c).cross(b-c);
    if (sign(d1)*sign(d2)<0 && sign(d3)*sign(d4)<0) return true;
    // коллинеарные случаи
    auto onSeg=[](P p, P a, P b){
        return min(a.x,b.x)<=p.x+EPS && p.x<=max(a.x,b.x)+EPS
            && min(a.y,b.y)<=p.y+EPS && p.y<=max(a.y,b.y)+EPS;
    };
    if (!sign(d1) && onSeg(c,a,b)) return true;
    if (!sign(d2) && onSeg(d,a,b)) return true;
    if (!sign(d3) && onSeg(a,c,d)) return true;
    if (!sign(d4) && onSeg(b,c,d)) return true;
    return false;
}

// ─── Polygon ──────────────────────────────────────────────────────────────────
// Когда: площадь/периметр фигуры, принадлежность точки полигону, целые точки (Пик)
ld polyArea(vector<P>& p) {
    ld s = 0;
    int n = p.size();
    for (int i=0;i<n;i++) s += p[i].cross(p[(i+1)%n]);
    return fabs(s)/2;
}

// Периметр
ld polyPerimeter(vector<P>& p) {
    ld s=0; int n=p.size();
    for(int i=0;i<n;i++) s+=dist(p[i],p[(i+1)%n]);
    return s;
}

// Точка внутри полигона (ray casting). 0=снаружи, 1=внутри, -1=на границе
int pointInPoly(P pt, vector<P>& p) {
    int n=p.size(), cnt=0;
    for(int i=0;i<n;i++){
        P a=p[i], b=p[(i+1)%n];
        if(distToSeg(pt,a,b)<EPS) return -1;
        if((a.y<=pt.y)!=(b.y<=pt.y)){
            ld t=(pt.y-a.y)/(b.y-a.y);
            if(pt.x < a.x + t*(b.x-a.x)) cnt++;
        }
    }
    return cnt&1;
}

// ─── Convex Hull (Andrew's monotone chain) — O(n log n) ──────────────────────
// Когда: выпуклая оболочка множества точек; основа для calipers, half-plane, диаметра
vector<P> convexHull(vector<P> pts) {
    int n=pts.size(); if(n<2) return pts;
    sort(pts.begin(),pts.end());
    pts.erase(unique(pts.begin(),pts.end()),pts.end());
    n=pts.size();
    vector<P> h;
    // lower
    for(auto& p:pts){
        while(h.size()>=2 && (h.back()-h[h.size()-2]).cross(p-h[h.size()-2])<=0)
            h.pop_back();
        h.push_back(p);
    }
    // upper
    int lo=h.size()+1;
    for(int i=n-2;i>=0;i--){
        while((int)h.size()>=lo && (h.back()-h[h.size()-2]).cross(pts[i]-h[h.size()-2])<=0)
            h.pop_back();
        h.push_back(pts[i]);
    }
    h.pop_back();
    return h;
}

// ─── Closest pair — O(n log n) ────────────────────────────────────────────────
// Когда: минимальное расстояние между точками из набора
ld closestPairRec(vector<P>& p, int l, int r) {
    if(r-l<=3){
        ld d=1e18;
        for(int i=l;i<r;i++) for(int j=i+1;j<r;j++) d=min(d,dist(p[i],p[j]));
        sort(p.begin()+l,p.begin()+r,[](P a,P b){return a.y<b.y;});
        return d;
    }
    int m=(l+r)/2; ld mx=p[m].x;
    ld d=min(closestPairRec(p,l,m),closestPairRec(p,m,r));
    vector<P> strip;
    inplace_merge(p.begin()+l,p.begin()+m,p.begin()+r,[](P a,P b){return a.y<b.y;});
    for(int i=l;i<r;i++) if(fabs(p[i].x-mx)<d) strip.push_back(p[i]);
    for(int i=0;i<(int)strip.size();i++)
        for(int j=i+1;j<(int)strip.size()&&strip[j].y-strip[i].y<d;j++)
            d=min(d,dist(strip[i],strip[j]));
    return d;
}
ld closestPair(vector<P> p) {
    sort(p.begin(),p.end());
    return closestPairRec(p,0,p.size());
}

// ─── Circle ───────────────────────────────────────────────────────────────────
// Когда: пересечения окружностей, площадь перекрытия, касательные из точки
struct Circle { P c; ld r; };

// Точек пересечения двух окружностей: 0/1/2/-1(совпадают)
int circleCircleIntersect(Circle c1, Circle c2, P &p1, P &p2) {
    ld d=dist(c1.c,c2.c);
    if(d<EPS) return fabs(c1.r-c2.r)<EPS ? -1 : 0;
    if(d>c1.r+c2.r+EPS || d<fabs(c1.r-c2.r)-EPS) return 0;
    ld a=(c1.r*c1.r-c2.r*c2.r+d*d)/(2*d);
    ld h=sqrt(max((ld)0, c1.r*c1.r-a*a));
    P mid=c1.c+(c2.c-c1.c)*(a/d);
    P perp=(c2.c-c1.c).rot90()*(h/d);
    p1=mid+perp; p2=mid-perp;
    return fabs(h)<EPS ? 1 : 2;
}

// Площадь пересечения двух окружностей
ld circleCircleArea(Circle c1, Circle c2) {
    ld d=dist(c1.c,c2.c);
    if(d>=c1.r+c2.r) return 0;
    if(d+c2.r<=c1.r) return PI*c2.r*c2.r;
    if(d+c1.r<=c2.r) return PI*c1.r*c1.r;
    ld a1=2*acos((d*d+c1.r*c1.r-c2.r*c2.r)/(2*d*c1.r));
    ld a2=2*acos((d*d+c2.r*c2.r-c1.r*c1.r)/(2*d*c2.r));
    return 0.5*(c1.r*c1.r*(a1-sin(a1))+c2.r*c2.r*(a2-sin(a2)));
}

// Касательные из внешней точки p к окружности c (возвращает точки касания)
vector<P> circleTangents(Circle c, P p) {
    ld d=dist(c.c,p);
    if(d<c.r-EPS) return {};
    ld a=acos(min((ld)1,c.r/d));
    P dir=(p-c.c).unit();
    return {c.c+dir.rot(a)*c.r, c.c+dir.rot(-a)*c.r};
}

// ─── Прочее ───────────────────────────────────────────────────────────────────
// Когда: вспомогательные функции — углы, выпуклость, целые точки на границе (Пик)
ld angle(P a, P b) { return acos(max((ld)-1,min((ld)1,a.dot(b)/(a.norm()*b.norm())))); }

// Является ли полигон выпуклым (CCW)
bool isConvex(vector<P>& p) {
    int n=p.size();
    for(int i=0;i<n;i++)
        if((p[(i+1)%n]-p[i]).cross(p[(i+2)%n]-p[(i+1)%n])<-EPS) return false;
    return true;
}

// Формула Пика: S = I + B/2 - 1  =>  I = S - B/2 + 1
// B = число граничных целых точек = sum gcd(|dx|,|dy|) по рёбрам
long long boundaryPoints(vector<P>& p) {
    long long b=0; int n=p.size();
    for(int i=0;i<n;i++){
        long long dx=llround(p[(i+1)%n].x-p[i].x);
        long long dy=llround(p[(i+1)%n].y-p[i].y);
        b+=__gcd(abs(dx),abs(dy));
    }
    return b;
}

// ─── Полярная сортировка ──────────────────────────────────────────────────────
// Сортировка точек по полярному углу относительно origin (CCW от оси X)
// Точки в верхней полуплоскости идут раньше нижней
int half(P p) { return p.y<-EPS || (fabs(p.y)<EPS && p.x<-EPS); }
bool polarCmp(P a, P b) {
    if(half(a)!=half(b)) return half(a)<half(b);
    ld c=a.cross(b);
    if(fabs(c)>EPS) return c>0;
    return a.norm2()<b.norm2();
}
// Использование: sort(pts.begin(), pts.end(), polarCmp);
// Если нужна сортировка относительно точки o: вычесть o из всех точек

// ─── Winding Number (точка в полигоне) ───────────────────────────────────────
// Возвращает winding number: 0=снаружи, !=0 внутри, -1=на границе
// Надёжнее ray casting для вырожденных случаев
int windingNumber(P pt, vector<P>& p) {
    int n=p.size(), w=0;
    for(int i=0;i<n;i++){
        P a=p[i], b=p[(i+1)%n];
        if(distToSeg(pt,a,b)<EPS) return -1;
        if(a.y<=pt.y){
            if(b.y>pt.y && (b-a).cross(pt-a)>0) w++;
        } else {
            if(b.y<=pt.y && (b-a).cross(pt-a)<0) w--;
        }
    }
    return w;
}

// ─── Point in Convex Polygon — O(log n) ──────────────────────────────────────
// Полигон должен быть CCW, вершина 0 — самая левая нижняя
// Возвращает: 1=внутри, 0=снаружи, -1=на границе
int pointInConvex(P pt, vector<P>& p) {
    int n=p.size();
    if(n==1) return (pt==p[0]) ? -1 : 0;
    if(n==2) return distToSeg(pt,p[0],p[1])<EPS ? -1 : 0;
    if((pt-p[0]).cross(p[1]-p[0])<-EPS) return 0;
    if((pt-p[0]).cross(p[n-1]-p[0])>EPS) return 0;
    // бинарный поиск сектора
    int lo=1, hi=n-1;
    while(hi-lo>1){
        int mid=(lo+hi)/2;
        if((pt-p[0]).cross(p[mid]-p[0])>=0) lo=mid; else hi=mid;
    }
    ld c=(p[lo+1]-p[lo]).cross(pt-p[lo]);
    if(fabs(c)<EPS) return -1;
    return c>0 ? 1 : 0;
}

// ─── Rotating Calipers — диаметр выпуклой оболочки ───────────────────────────
// Возвращает квадрат диаметра (максимальное расстояние между точками hull)
ld convexDiameter(vector<P> h) {
    int n=h.size();
    if(n==1) return 0;
    if(n==2) return (h[0]-h[1]).norm2();
    ld res=0;
    for(int i=0,j=1;i<n;i++){
        P a=h[i], b=h[(i+1)%n];
        while((b-a).cross(h[(j+1)%n]-h[j]) > 0) j=(j+1)%n;
        res=max(res,max((a-h[j]).norm2(),(b-h[j]).norm2()));
    }
    return res; // реальный диаметр = sqrt(res)
}

// ─── Half-Plane Intersection ──────────────────────────────────────────────────
// Полуплоскость: левая сторона от луча a->b (т.е. (b-a).cross(p-a) >= 0)
struct HP { P a, b; ld angle; };

HP makeHP(P a, P b) { return {a, b, atan2(b.y-a.y, b.x-a.x)}; }

bool hpLeft(HP h, P p) { return (h.b-h.a).cross(p-h.a) > -EPS; }

P hpIntersect(HP h1, HP h2) {
    P res; lineIntersect(h1.a,h1.b,h2.a,h2.b,res); return res;
}

bool hpBad(HP h1, HP h2, HP h3) {
    return !hpLeft(h3, hpIntersect(h1,h2));
}

// Пересечение набора полуплоскостей — возвращает выпуклый полигон (или пустой)
// Вход: вектор полуплоскостей. Выход: вершины результирующего полигона CCW.
vector<P> halfPlaneIntersection(vector<HP> hps) {
    sort(hps.begin(),hps.end(),[](HP a,HP b){
        if(fabs(a.angle-b.angle)>EPS) return a.angle<b.angle;
        return (b.b-b.a).cross(a.a-b.a)>0; // при одинаковом угле — левее
    });
    // убираем дубли по направлению
    vector<HP> h;
    for(auto& hp:hps)
        if(h.empty()||fabs(hp.angle-h.back().angle)>EPS) h.push_back(hp);
    int n=h.size();
    deque<HP> dh; deque<P> dp;
    dh.push_back(h[0]); dh.push_back(h[1]);
    dp.push_back(hpIntersect(h[0],h[1]));
    for(int i=2;i<n;i++){
        while(dp.size()&&!hpLeft(h[i],dp.back())) { dp.pop_back(); dh.pop_back(); }
        while(dp.size()&&!hpLeft(h[i],dp.front())) { dp.pop_front(); dh.pop_front(); }
        dh.push_back(h[i]);
        dp.push_back(hpIntersect(dh[dh.size()-2],dh.back()));
    }
    while(dp.size()&&!hpLeft(dh.front(),dp.back())) { dp.pop_back(); dh.pop_back(); }
    while(dp.size()&&!hpLeft(dh.back(),dp.front())) { dp.pop_front(); dh.pop_front(); }
    if(dh.size()<3) return {};
    dp.push_back(hpIntersect(dh.back(),dh.front()));
    return vector<P>(dp.begin(),dp.end());
}

// ─── Line-Circle intersection ─────────────────────────────────────────────────
// Точки пересечения прямой (a,b) с окружностью c
// Возвращает 0, 1 или 2 точки
vector<P> lineCircleIntersect(P a, P b, Circle c) {
    P d=b-a, f=a-c.c;
    ld A=d.norm2(), B=2*f.dot(d), C=f.norm2()-c.r*c.r;
    ld disc=B*B-4*A*C;
    if(disc<-EPS) return {};
    disc=max((ld)0,disc);
    ld t1=(-B-sqrt(disc))/(2*A), t2=(-B+sqrt(disc))/(2*A);
    if(fabs(disc)<EPS) return {a+d*t1};
    return {a+d*t1, a+d*t2};
}

// ─── Центры треугольника ──────────────────────────────────────────────────────
// Описанная окружность (circumcenter)
P circumcenter(P a, P b, P c) {
    P res;
    lineIntersect((a+b)*0.5, (a+b)*0.5+(b-a).rot90(),
                  (b+c)*0.5, (b+c)*0.5+(c-b).rot90(), res);
    return res;
}
ld circumradius(P a, P b, P c) { return dist(a,circumcenter(a,b,c)); }

// Вписанная окружность (incenter)
P incenter(P a, P b, P c) {
    ld la=dist(b,c), lb=dist(a,c), lc=dist(a,b);
    return (a*la+b*lb+c*lc)*(1/(la+lb+lc));
}
ld inradius(P a, P b, P c) {
    ld s=(dist(a,b)+dist(b,c)+dist(c,a))/2;
    return polyArea(*(new vector<P>{a,b,c}))/s;
}

// Центроид (центр масс)
P centroid(P a, P b, P c) { return (a+b+c)*(1.0/3); }

// Ортоцентр
P orthocenter(P a, P b, P c) {
    P res;
    lineIntersect(a, a+(c-b).rot90(), b, b+(c-a).rot90(), res);
    return res;
}

// ─── 3D Геометрия ─────────────────────────────────────────────────────────────
struct P3 {
    ld x,y,z;
    P3(ld x=0,ld y=0,ld z=0):x(x),y(y),z(z){}
    P3 operator+(P3 o) const { return {x+o.x,y+o.y,z+o.z}; }
    P3 operator-(P3 o) const { return {x-o.x,y-o.y,z-o.z}; }
    P3 operator*(ld t) const { return {x*t,y*t,z*t}; }
    ld dot(P3 o) const { return x*o.x+y*o.y+z*o.z; }
    P3 cross(P3 o) const { return {y*o.z-z*o.y, z*o.x-x*o.z, x*o.y-y*o.x}; }
    ld norm() const { return sqrt(x*x+y*y+z*z); }
    ld norm2() const { return x*x+y*y+z*z; }
    P3 unit() const { ld n=norm(); return {x/n,y/n,z/n}; }
};

ld dist3(P3 a, P3 b) { return (a-b).norm(); }

// Расстояние от точки p до прямой (a, направление d)
ld distToLine3(P3 p, P3 a, P3 d) {
    return d.cross(p-a).norm()/d.norm();
}

// Расстояние от точки p до плоскости (нормаль n, точка a)
ld distToPlane(P3 p, P3 a, P3 n) {
    return fabs(n.dot(p-a))/n.norm();
}

// Пересечение луча (orig, dir) с плоскостью (нормаль n, точка a)
// Возвращает t такое что orig+dir*t — точка пересечения
bool rayPlane(P3 orig, P3 dir, P3 a, P3 n, ld &t) {
    ld denom=n.dot(dir);
    if(fabs(denom)<EPS) return false;
    t=n.dot(a-orig)/denom;
    return true;
}

// Объём тетраэдра (a,b,c,d)
ld tetraVolume(P3 a, P3 b, P3 c, P3 d) {
    return fabs((b-a).dot((c-a).cross(d-a)))/6;
}

// ─── main (пример) ────────────────────────────────────────────────────────────
int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);
    // Пример: площадь полигона
    int n; cin>>n;
    vector<P> poly(n);
    for(auto& p:poly) cin>>p.x>>p.y;
    cout << fixed << setprecision(10) << polyArea(poly) << "\n";
}
