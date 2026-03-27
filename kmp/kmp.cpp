#include "bits/stdc++.h"
using namespace std;

vector<int64_t> prefix_function(string s){
    int64_t n = s.size();
    vector<int64_t> pi(n);
    for (int i = 1;i<n;i++){
        int64_t j = pi[i-1];
        while (j>0 and s[i]!=s[j]){
            j = pi[j-1];
        }
        if (s[i] == s[j]) j++;
        pi[i] = j;
    }
    return pi;
}

vector<int64_t> kmp(string text, string pattern){
    string s = pattern+"#"+text;
    vector<int64_t> pi = prefix_function(s);
    vector<int64_t> ans;
    for (int i = pattern.size()+1;i<s.size();i++){
        if (pi[i] == pattern.size()) ans.push_back(i-2*pattern.size);
    }
    return ans;
}