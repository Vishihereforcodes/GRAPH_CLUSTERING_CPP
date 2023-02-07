
  /* PROGRAM FOR CLUSTERING AN UNDIRECTED GRAPH
  %
  % Author: Vishal Kumar (sg.vishalkumar17@gmail.com)
  % Written Date:   Nov / 2022
  % Description: The algorithm uses the Quality function by Girvan-Newman to implement the clustering.
            ->   quality function Q = (conn_edges(cluster1,cluster2)/m)-(dccluster[cluster1]*dccluster[cluster2])/(m*m);
                 where conn_edges(C1,C2) returns the number of connecting edges between cluster C1 and cluster C2
                 and dccluster[C1] stores the sum of degrees of each vertex in cluster C1.
                 At every step, only those clusters are merged which give highest rise to the quality value Q.

  %  To input a graph,  Just run the program and give input.
                        OR
  %                     1) Change the value of m in line 31 to the number of edges in the graph.
  %                     2) Change the value of V in line 32 to the number of vertices in the graph.
  %                     3) Enter the edges in edges_t edges[] in line 139.
  */

//***************************************** Template Begins ********************************************//
// Header Files
#include<iostream>
#include <filesystem>
#include<iomanip>
#include<algorithm>
#include<vector>
#include<utility>
#include<set>
#include<unordered_set>
#include<list>
#include<iterator>
#include<deque>
#include<queue>
#include<stack>
#include<set>
#include<bitset>
#include<thread>
#include<tuple>
#include<random>
#include<map>
#include<unordered_map>
#include<stdio.h>
#include<complex>
#include<math.h>
#include<cstring>
#include <fstream>
#include <climits>
#include<chrono>
#include<string>
#include "ext/pb_ds/assoc_container.hpp"
#include "ext/pb_ds/tree_policy.hpp"
// Header Files End
 
using namespace std;
using namespace __gnu_pbds;
// find_by_order(k)  returns iterator to kth element starting from 0;
// order_of_key(k) returns count of elements strictly smaller than k;
template<class T> using ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update> ;
 
template<class key, class value, class cmp = std::less<key>> using ordered_map = tree<key, value, cmp, rb_tree_tag, tree_order_statistics_node_update>;

#define FASTIO ios_base::sync_with_stdio(false);cin.tie(NULL);cout.tie(NULL)
#define endl "\n"
#define ll long long
#define ULL unsigned long long
#define umap unordered_map
#define uset unordered_set
#define lb lower_bound
#define ub upper_bound
#define ts(num) to_string(num)
#define fo(i,a,b) for(int i=a;i<=b;i++)
#define all(v) (v).begin(),(v).end()
#define all1(v) (v).begin()+1,(v).end()
#define allr(v) (v).rbegin(),(v).rend()
#define allr1(v) (v).rbegin()+1,(v).rend()
#define sort0(v) sort(all(v))
#define bpcnt(x) __builtin_popcount(x)      // count the number of set bits
#define bpcntll(x) __builtin_popcount(x)
#define bpar(x) __builtin_parity(x)         // returns true(1) if the number has odd parity
#define bparll(x) __builtin_parity(x)
#define bclz(x) __builtin_clz(x)            // count the leading zero of the integer (before set bit)
typedef pair<int, int> pii;
typedef vector<int> vi;
typedef vector<ll> vll;
typedef pair<ll, ll> pll;
#define sz(x) (ll)x.size()
#define all(a)  a.begin(),a.end()
#define newl cout<<"\n"
#define space cout<<" "
#define pb push_back
#define ppb pop_back
#define mkp make_pair
#define inf 1000000000000000005
const ll M = 1e9 + 7;
const int N = 1e5 + 100;

ll inv(ll i) {if (i == 1) return 1; return (M - ((M / i) * inv(M % i)) % M) % M;}
 
ll mod_mul(ll a, ll b) {a = a % M; b = b % M; return (((a * b) % M) + M) % M;}
 
ll mod_add(ll a, ll b) {a = a % M; b = b % M; return (((a + b) % M) + M) % M;}
 
ll gcd(ll a, ll b) { if (b == 0) return a; return gcd(b, a % b);}
 
ll ceil_div(ll a, ll b) {return a % b == 0 ? a / b : a / b + 1;}
 
ll pwr(ll a, ll b) {a %= M; ll res = 1; while (b > 0) {if (b & 1) res = res * a % M; a = a * a % M; b >>= 1;} return res;}
//****************************Template Ends*******************************//

//------------------------------------------------------------------------------------------------------------------------------------------//
// Sieve Eranthoses for Prime. Time Complexity : O(N * log(log(N)))
vector<bool> isPrime(1e6 + 7, true);
void seive(){
    isPrime[0] = isPrime[1] = false;
    for(int i = 2; i * i <= 1e6 + 7; ++i){
        if(isPrime[i]){
            for(int j = i * i; j <= 1e6 + 7; j += i)
                isPrime[j] = false;
        }
    }
}
//----------------------------------------------** CLUSTERING OF GRAPH - CPP CODE **---------------------------------------------------------//
int m = 77, V = 34;

typedef pair< int ,int > pii;

struct edge_t {
    unsigned long first, second;
};

priority_queue<pair<double, pii>> PQ;

set<int> CLUSTER[100000], adj[10000];
set<int> :: iterator itr1, itr2, itr3, itr4;

int cckcluster[10000], lccluster[10000], dccluster[10000], mindegree[10000];

int cluster_size, vcount;
int id[10000], no_of_edges[10000], dfschk[10000];

//-----------------------------------------------------------------------------------------------------------------------//
void dfs(int u){
    if(dfschk[u]) return;
    dfschk[u] = true;
    for(set<int> :: iterator itrset = adj[u].begin(); itrset != adj[u].end(); itrset++){
        dfs(*itrset);
    }
}
//-----------------------------------------------------------------------------------------------------------------------//
int conn_edges(int i,int j){
    int x, y, ctr = 0;
    for(itr3 = CLUSTER[i].begin(); itr3 != CLUSTER[i].end(); itr3++){
        x = (*itr3);
        for(itr4 = CLUSTER[j].begin(); itr4 != CLUSTER[j].end(); itr4++){
            y = (*itr4);
            if(adj[x].find(y) != adj[x].end()){
                ++ctr;
            }
        }
    }
    return ctr;
}
//------------------------------------------------------------------------------------------------------------------------//
void merge_cluster(int i,int j) {
        int x, y;
        double temp;
        cluster_size++;

        lccluster[cluster_size] = lccluster[i] + lccluster[j];
        lccluster[cluster_size] += conn_edges(i, j);
        dccluster[cluster_size] = dccluster[i] + dccluster[j];

        CLUSTER[cluster_size].insert(all(CLUSTER[i]));
        CLUSTER[cluster_size].insert(all(CLUSTER[j]));

        CLUSTER[i].erase(all(CLUSTER[i]));
        CLUSTER[j].erase(all(CLUSTER[j]));

        for(itr1 = CLUSTER[cluster_size].begin(); itr1 != CLUSTER[cluster_size].end(); itr1++){
            x = (*itr1);
            id[x] = cluster_size;
        }

        for(itr1 = CLUSTER[cluster_size].begin(); itr1 != CLUSTER[cluster_size].end(); itr1++){
            x = (*itr1);
            for(itr2 = adj[x].begin(); itr2 != adj[x].end(); itr2++){
                y = (*itr2);
                if(id[y] != cluster_size){
                    temp = (1.0 * conn_edges(cluster_size,id[y]) / m) - (1.0 * dccluster[cluster_size] * dccluster[id[y]]) / (2.0 * m * m);
                    if(temp > 0.0){  
                        PQ.push({temp, {cluster_size, id[y]}});
                    }
                }
            }
        }
        cckcluster[j] = 0;                // j is not a cluster now
        cckcluster[i] = 0;                // i is not a cluster now
        cckcluster[cluster_size] = 1;     // new cluster is marked
}
//---------------------------------------------------------------------------------------------------------------------//
double update_quality(){
    double quality = 0.0;
    for(int i = 1;i <= V; ++i){
        if(cckcluster[i]){
            quality += (double)(1.0 * lccluster[i] / m) - (double)((1.0 * dccluster[i] * dccluster[i]) / (4.0 * m * m));
        }
    }
    return quality;
}

//----------------------------------------------------------------------------------------------------------------------//

int main() {
    int sz, x, y, i, j, k, maximum, rem;
    char op;

    edge_t saved[] = {{17,6}, {17,7},{6,7},{6,11},{6,1},{7,1},{7,5},{5,1},{5,11},{11,1},{1,4},{1,13},{1,20},{1,14},{1,2},{1,3},{1,8},{1,18},{1,12},{1,22},{1,9},{1,32},
    {13,4},{4,3},{4,2},{4,14},{4,8},{22,2},{18,2},{20,34},{20,2},{2,14},{2,3},{2,31},{2,8},{8,3},{14,34},{14,3},{3,29},{3,28},{3,33},{3,9},{3,10},{10,34},{31,34},{31,33},{31,9},
    {9,33},{29,34},{29,32},{32,34},{32,33},{32,26},{32,25},{25,26},{25,28},{26,24},{28,34},{28,24},{24,30},{24,33},{24,34},{34,19},{34,21},{34,30},{34,16},{34,27},{34,15},
    {34,23},{33,19},{33,21},{33,30},{33,16},{33,15},{33,23},{30,27},{34,9}};

    edge_t edges[10000];

    cout << "Do you want to give a fresh input? ('Y' or 'N'): ";
    cin >> op;

    do{
        if(op == 'Y' || op == 'y'){
        cout << "Enter the number of vertices: ";
        cin >> V;
        cout << "Enter the number of edges: ";
        cin >> m;
        cout << "Enter edges: ";
            for(i = 0; i < m; ++i){
                cout << "Enter vertices of edge: " << i + 1;
                cin>> x >> y;
                edges[i].first = x;
                edges[i].first = y;
            }
        }
        else if(op == 'N' || op == 'n'){
            for(i = 0; i < m; ++i){
                edges[i].first = saved[i].first;
                edges[i].second = saved[i].second;
            }
        }
        else {
            cout << "Wrong input !! Try again";
            cin >> op;
        }
    }while(op != 'y' && op != 'Y' && op != 'n' && op != 'N');

    for(i = 0; i < m; ++i){
        adj[edges[i].first].insert(edges[i].second);
        adj[edges[i].second].insert(edges[i].first);
    }

    for(i = 1; i <= V; ++i){
        no_of_edges[i] = adj[i].size();
    }

//  DFS CHECK:
    vcount=0;
    dfs(1);
    for(i = 1; i <= V; i++)
        if(dfschk[i]) ++vcount;

    if(vcount != V) { cout<< "Only "<< vcount << " vertices hit. Not conected"; return (0); }
    else { cout<< "\n Graph is connected"; newl; newl; }
        

    // Make initial clusters
    for(i = 1; i <= V; ++i){
        cckcluster[i] = 1;
        id[i] = i;
        lccluster[i] = 0;                 // lc=0 initially
        dccluster[i] = adj[i].size();     // dc for a cluster of 1 node=degree of the vertex
        CLUSTER[i].insert(i);
    }

    double temp, quality, val = 0.0;

    for(i = 0; i < m; ++i){
        x = edges[i].first;
        y = edges[i].second;

        temp = (1.0 / m) - (1.0 * dccluster[x] * dccluster[y]) / (2.0 * m * m);
        if(temp > 0.0){
            PQ.push({temp, {x, y}});
        }
    }

    quality = update_quality();
    cout << "Initial Q = " << quality << endl;

    pair<double, pii> ELEMENT;

    cluster_size = V;

    while(!PQ.empty()){
        ELEMENT = PQ.top();
        PQ.pop();

        val = ELEMENT.first;
        x = ELEMENT.second.first;
        y = ELEMENT.second.second;
        if((x != y) && cckcluster[x] && cckcluster[y]){
            quality + =val;
            merge_cluster(x,y);
        }

    }

    cout << "\n";     // Display the clustering
    j = 0;
    vcount = 0;

    for(i = 1; i <= cluster_size; i++){
        if(cckcluster[i]){
                j++;
                cout << " \n CLUSTER : { \n   ";
            for(itr1 = CLUSTER[i].begin(); itr1 != CLUSTER[i].end(); itr1++){
                cout << (*itr1) << ",";
                vcount++;
            }
            cout << "\n }";
        }
    }

    cout << " \nVertices covered = " << vcount; newl;
    cout << " \nNumber of Clusters = " << j; newl;
    cout << " Final Q = " << quality << "\n";
}
//--------------------------------------------------------** THE END **----------------------------------------------------------------//
