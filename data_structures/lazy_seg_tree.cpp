#include "bits/stdc++.h"
using namespace std;

struct lazy_seg_tree{
    int64_t n;
    vector<int64_t> lazy, sum;
    
    lazy_seg_tree(int64_t n) : n(n), sum(4*n), lazy(4*n) {}

    void apply(int64_t v, int64_t val, int64_t len){
        sum[v]+=val*len;
        lazy[v]+=val;
    }

    void push(int64_t v, int64_t tree_l, int64_t tree_r){
        if (lazy[v] == 0) return;
        int64_t mid = (tree_l+tree_r)/2;
        apply(2*v, lazy[v], mid - tree_l+1);
        apply(2*v+1, lazy[v], tree_r - mid);
        lazy[v] = 0;
    }
    void pull(int64_t v){
        sum[v] = sum[2*v]+sum[2*v+1];
    }

    void build(vector<int64_t>& arr, int64_t v, int64_t tree_l, int64_t tree_r){
        if (tree_l == tree_r){
            sum[v] = arr[tree_l];
            return;
        }
        int64_t mid = (tree_l+tree_r)/2;
        build(arr, 2*v, tree_l, mid);
        build(arr, 2*v+1, mid+1, tree_r);
        pull(v);
    }
    void update(int64_t v, int64_t tree_l, int64_t tree_r, int64_t l, int64_t r, int64_t val){
        if (l>r) return;
        if (l == tree_l and r == tree_r) {apply(v, val, tree_r - tree_l +1); return;}
        push(v, tree_l, tree_r);
        int64_t mid = (tree_l+tree_r)/2;
        update(2*v, tree_l, mid, l, min(mid, r), val);
        update(2*v+1, mid+1, tree_r, max(mid+1, l), r, val);
        pull(v);
    }

    int64_t query_sum(int64_t v, int64_t tree_l, int64_t tree_r, int64_t l, int64_t r){
        if (l>r) return 0;
        if (l<=tree_l and tree_r<= r) return sum[v];
        push(v, tree_l, tree_r);
        int64_t mid = (tree_l+tree_r)/2;
        return query_sum(2*v, tree_l,mid, l, min(mid, r))+query_sum(2*v+1, mid+1, tree_r, max(mid+1, l), r);
    }

    int64_t query(int64_t l, int64_t r){
        return query_sum(1, 0, n-1, l,r);
    }
};