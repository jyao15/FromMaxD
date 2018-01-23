#include <vector>
#include <list>
#include <map>
#include <set>
#include <deque>
#include <queue>
#include <stack>
#include <bitset>
#include <algorithm>
#include <functional>
#include <numeric>
#include <utility>
#include <sstream>
#include <iostream>
#include <iomanip>
#include <cstdio>
#include <cmath>
#include <cstdlib>
#include <cctype>
#include <string>
#include <cstring>
#include <ctime>
#include <string.h>

using namespace std;

typedef long long int64;
typedef unsigned long long uint64;
#define two(X) (1<<(X))
#define twoL(X) (((int64)(1))<<(X))
#define contain(S,X) (((S)&two(X))!=0)
#define containL(S,X) (((S)&twoL(X))!=0)
const double pi=acos(-1.0);
const double eps=1e-11;
template<class T> inline void checkmin(T &a,T b){if(b<a) a=b;}
template<class T> inline void checkmax(T &a,T b){if(b>a) a=b;}
template<class T> inline T sqr(T x){return x*x;}
typedef pair<int,int> ipair;
#define SIZE(A) ((int)A.size())
#define LENGTH(A) ((int)A.length())
#define MP(A,B) make_pair(A,B)
#define PB(X) push_back(X)
typedef vector<int> VI;


int source_group=0,target_group=1;


int n,m,c;      // node number and edge number in original graph
int *degree,**graph;
int *area;

void load_area(string filename)  // set global variable area
{
	area=new int[n];
	FILE *f=fopen(filename.c_str(),"r");
	for (int i=0;i<n;i++) fscanf(f,"%d",&area[i]);
	fclose(f);
}

void load_graph(string filename)  // set global variable degree and graph
{
	FILE *f=fopen(filename.c_str(),"r");
	fscanf(f,"%d%d",&n,&m);
	int *e_list=new int[m+m];
	for (int i=0;i<m+m;i++) fscanf(f,"%d",&e_list[i]);
	degree=new int[n];
	for (int i=0;i<n;i++) degree[i]=0;
	for (int i=0;i<m+m;i++) 
		if (e_list[i]!=e_list[i^1]) // ignore self-loops
			degree[e_list[i]]++;
	graph=new int* [n];
	for (int i=0;i<n;i++) graph[i]=new int[degree[i]];
	for (int i=0;i<n;i++) degree[i]=0;
	for (int i=0;i<m+m;i++) if (e_list[i]!=e_list[i^1]) graph[e_list[i]][degree[e_list[i]]++]=e_list[i^1];
	delete[] e_list;
	fclose(f);
}

int myrandom()
{
	int v1=rand()&32767;
	int v2=rand()&32767;
	return (v1<<15)|v2;
}

int myrandom(int n)
{
	return myrandom()%n;
}

VI get_community_kernel(int mask) // mask is binary 00..010..00
{
	VI ret;
	vector<pair<int, int> > q;
	for (int i = 0; i < n; ++i)
		if ((area[i] & mask) == mask)
			q.push_back(MP(degree[i], i));  // make pair for sorting
	sort(q.begin(), q.end());
	reverse(q.begin(), q.end());
	for (int i = 0; i < SIZE(q) / 1; ++i)  // choose top 1% users (with highest degrees) in this area
		ret.push_back(q[i].second);
	return ret;
}

const int maxnode=7000000+5;
const int maxedge=60000000+5;
const int oo=1000000000;

int node,src,dest,edge_number;               // these variables are all about the newly created graph
int head[maxnode],point[maxedge],next_[maxedge],flow[maxedge],capa[maxedge];  // capa is not residual
int dist[maxnode],Q[maxnode],work[maxnode];
bool dsave[maxnode];
int prev_flow[maxedge];

void init(int _node,int _src,int _dest)
{
	node=_node;
	src=_src;
	dest=_dest;
	for (int i=0;i<node;i++) head[i]=-1;
	edge_number=0;
}
void addedge(int u,int v,int c1,int c2)
{
	point[edge_number]=v,capa[edge_number]=c1,flow[edge_number]=0,next_[edge_number]=head[u],head[u]=(edge_number++); // head and next_ compose a list for every node in the new graph
	point[edge_number]=u,capa[edge_number]=c2,flow[edge_number]=0,next_[edge_number]=head[v],head[v]=(edge_number++);
}
void remove_last_edge()
{
	edge_number -= 1;
	head[edge_number]=next_[edge_number];
	head[edge_number+1]=next_[edge_number+1];
}
bool dinic_bfs()
{
	for (int i=0;i<node;i++) dist[i]=-1;
	dist[src]=0;
	int sizeQ=0;
	Q[sizeQ++]=src;   // Q is the nodes in the level graph, sizeQ is its size
	for (int cl=0;cl<sizeQ;cl++)
		for (int k=Q[cl],i=head[k];i>=0;i=next_[i])
			if (flow[i]<capa[i] && dist[point[i]]<0)  // dsave == false: user have been chosen in the top-k
			{
				dist[point[i]]=dist[k]+1;
				Q[sizeQ++]=point[i];
			}
	return dist[dest]>=0;
}
int dinic_dfs(int x,int exp)
{
	if (x==dest) return exp;
	int res=0;
	for (int &i=work[x];i>=0;i=next_[i])
	{
		int v=point[i],tmp;  // v is a node, i is an edge
		if (flow[i]<capa[i] && dist[v]==dist[x]+1 && (tmp=dinic_dfs(v,min(exp,capa[i]-flow[i])))>0)
		{
			flow[i]+=tmp;
			flow[i^1]-=tmp;
			res+=tmp;
			exp-=tmp;
			if (exp==0) break;  // <=? never happen?
		}
	}
	return res;
}
int dinic_flow()
{
	int result=0;
	while (dinic_bfs())
	{
		for (int i=0;i<node;i++) work[i]=head[i];  // maybe redundant
		result+=dinic_dfs(src,oo);  // oo is a big enough number
	}
	return result;
}

void load_community_kernels(string filename,vector<VI> &kernels)
{
	FILE *f=fopen(filename.c_str(),"r");
	int size;
	while (fscanf(f,"%d",&size)!=-1)
	{
		VI a;
		int t;
		for (int i=0;i<size;i++) { fscanf(f,"%d",&t); a.push_back(t); }
		kernels.push_back(a);
	}
	fclose(f);
}

VI get_common(VI a,VI b)
{
	VI c;
	sort(a.begin(),a.end());
	sort(b.begin(),b.end());
	for (int i=0,j=0;i<SIZE(a) && j<SIZE(b);)
		if (a[i]==b[j])
		{
			c.push_back(a[i]);
			i++;
			j++;
		}
		else if (a[i]<b[j])
			i++;
		else
			j++;
	return c;
}

void build_network(vector<VI>& kernels, VI& candidates)
{
	//printf("DEBUG : build_network : ");  // c:SIZE(kernels)
	init(n+2,n,n+1);
	set<int> S1,S2;
	for (int j=0;j<SIZE(kernels[source_group]);j++) S1.insert(kernels[source_group][j]);
	for (int j=0;j<SIZE(kernels[target_group]);j++) S2.insert(kernels[target_group][j]);

	if (SIZE(S1)==0 || SIZE(S2)==0) return;
	for (int i=0;i<n;i++) for (int j=0;j<degree[i];j++) if (i<graph[i][j]) addedge(i,graph[i][j],1,1);
	for (set<int>::iterator it=S1.begin();it!=S1.end();++it) if (S2.find(*it)==S2.end()) addedge(src,(*it),n,0);  // *it is in (S1-S2)
	for (set<int>::iterator it=S2.begin();it!=S2.end();++it) if (S1.find(*it)==S1.end()) addedge((*it),dest,n,0);  // *it is in (S2-S1)

	for (set<int>::iterator it=S1.begin();it!=S1.end();++it)
	{
		for (int j=0;j<degree[*it];j++)
		{
			int v=graph[*it][j];
			if ((S1.find(v) == S1.end()) && S2.find(v) == S2.end()) candidates.push_back(v);
		}
	}
	//printf("node = %d   edge = %d\n",node,edge_number);
}

int max_flow(int added_node,int *prev_flow=NULL)
{
	if (prev_flow!=NULL) for (int i=0;i<edge_number;i++) flow[i]=prev_flow[i];
	else for (int i=0;i<edge_number;i++) flow[i]=0;
	if (added_node>=0) addedge(src,added_node,n,0);
	int ret=dinic_flow();
	if (added_node>=0) remove_last_edge();
	return ret;
}
/*
int get_multi_cut(vector<VI> &kernels,bool *save)
{
	build_network(kernels);
	int ret=max_flow(kernels,save);
	return ret;
}
*/
ipair pick_candidate(VI &candidates)  // the only function that changes (bool *save)
{
	int old_flow=max_flow(-1);
	for (int i=0;i<edge_number;i++) prev_flow[i]=flow[i];
	int maxflow=old_flow,best_key=-1;
	//printf("%d",SIZE(candidates));
	for (int i=0;i<SIZE(candidates);i++)
	{
		int key=candidates[i];
		printf("calculating candidate %d\n",i);
		int tmp=max_flow(key,prev_flow);
		if (tmp>maxflow) maxflow=tmp,best_key=key; 
	}
	//printf("\n");
	candidates.erase(std::remove(candidates.begin(), candidates.end(), best_key), candidates.end());
	return MP(maxflow,best_key);
}

int main(int argc,char **args)
{
	string graph_file="debug_graph.txt";
	string community_file="debug_community.txt";
	vector<int> area;
	for (int i=0;i<2;i++) area.push_back(pow(2,i));
	int size=2;
	/*
	for (int i=1;i+1<argc;i++) if (args[i][0]=='-')
		if (args[i][1]=='g')
			graph_file=args[i+1];
		else if (args[i][1]=='c')
			community_file=args[i+1];
		else if (args[i][1]=='a')
			area.push_back(atoi(args[i+1]));
		else if (args[i][1]=='k')
			size=atoi(args[i+1]);
	*/
	load_graph(graph_file);
	load_area(community_file); 
	vector<VI> kernels;
	for (int i=0;i<SIZE(area);i++) kernels.push_back(get_community_kernel(area[i]));
	if (SIZE(kernels)<2)
	{
		printf("ERROR : we should have at least 2 communities.");
		return 0;
	}
	for (int i=0;i<SIZE(kernels);i++) if (SIZE(kernels[i])==0)
	{
		printf("Community %d is too small.",i);
		return 0;
	}
	c=SIZE(kernels);
	bool *added=new bool[n];
	for (int i=0;i<n;i++) added[i]=false;
	VI mycandidates;
	build_network(kernels,mycandidates);
	//int *sflow=new int[n];
	//ipair *q=new ipair[n];
	for (int step=0;step<size;step++)  // size is k in "finding top-k users ..."
	{
		//for (int i=0;i<n;i++) sflow[i]=0;
		//max_flow(added);
		/*
		for (int i=0;i<n;i++) for (int k=head[i];k>=0;k=next_[k]) if (flow[k]>0) sflow[i%n]+=flow[k]; // sflow is the flow for each node in the original graph
		for (int i=0;i<n;i++)
			if (!save[i])
				q[i]=MP(-1,i); 
			else
				q[i]=MP(sflow[i]+degree[i],i);
		sort(q,q+n);
		reverse(q,q+n);
		vector<int> candidates;
		for (int i=0;i<n;i++) 
		{
			if (save[q[i].second] && SIZE(candidates)<size) 
			{
				candidates.push_back(q[i].second);
			}
		}
		*/
		ipair ret=pick_candidate(mycandidates);
		//printf("STEP %2d %d\n",step,ret.first);
		printf("%d\n",ret.second);
		//printf("%d %d\n",ret.first,ret.second);
	}
	//delete[] sflow;
	//delete[] q;
	return 0;
}

