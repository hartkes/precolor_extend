
// graph.h
// This is a C++ library for dealing with undirected graphs.
// The library is contained in one header file to enable use of inline functions.

// Copyright 2015-16, Stephen G. Hartke
// Licensed under the GPL version 3.


/////////////////////////////////////////////////////////////////////////////
// Helper functions for dealing with colex order.
/////////////////////////////////////////////////////////////////////////////


inline
int binomial2(int n)
{
    return ((n*n)-n)/2;  // this is the fastest calculation, faster than those below
    //return (n*(n-1))/2;
    //return (n*(n-1))>>1;  // /2 is faster than >>1; the compiler must be able to deal with /2 better???
    //return ((n*n)-n)>>1;
}


inline
int pair_to_index(int i, int j)
    // return the index of the pair (i,j) in colex order
{
    // NOTE: We can replace the if statement with bit manipulation techniques for computing min and max.
    // See for instance http://graphics.stanford.edu/~seander/bithacks.html#IntegerMinOrMax
    
    /*
     * 2016-07-10  Something is wrong with this code when i and j are out of order!
    register int d;
    d=(j-i) & ((j-i)>>(sizeof(int)*8-1));  // d=j-i if j<i and 0 otherwise; the signed right shift fills in the sign bit
    return binomial2(j+d)+i+d;
    */
    //*
    if (i<j)
        return binomial2(j)+i;
    else
        return binomial2(i)+j;
    //*/
}


inline
int pair_sorted_to_index(int i, int j)
    // return the index of the pair (i,j) in colex order; we assume that i<j
{
    return binomial2(j)+i;
}


inline
void index_to_pair(int index, int *i, int *j)
{
    // we need to fill in the code that will unrank a pair.
    // it should use the sqrt function to invert the binomial coefficient
    ;
}


/////////////////////////////////////////////////////////////////////////////
// The main class for undirected graphs.
/////////////////////////////////////////////////////////////////////////////


class UndirectedGraph
    // This base class is for undirected graphs without loops.
    // The adjacency matrix can hold 0,1 values, or arbitrary integers.
{
public:
    int n;  // the number of vertices; -1 if unallocated
    int nchoose2;  // binomial(n,2)
    int *adj;  // the adjacency matrix
            // The adacency matrix is stored as a one-dimensional array of integers of length nchoose2, sorted in colex order.

    UndirectedGraph();  // create an unallocated graph, n=-1
    UndirectedGraph(int n);  // create an empty graph with n vertices
    UndirectedGraph(char *g6);  // create a graph from the given graph6 string
    UndirectedGraph(UndirectedGraph *G, int k);  // create an induced subgraph of G on the vertices 0..k-1
    ~UndirectedGraph();
    
    virtual void allocate(int n);
    virtual void deallocate();

    void zero_adj();
    void read_graph6_string(char *g6);
    void write_graph6_string(char *g6, int length);
    void print_adj_matrix();
    
    void set_adj(int i, int j, int val);
    void set_adj_sorted(int i, int j, int val);
    int get_adj(int i, int j);
    int get_adj_sorted(int i, int j);
};


UndirectedGraph::UndirectedGraph()  // create an unallocated graph, n=-1
{
    n=-1;
}


UndirectedGraph::UndirectedGraph(int n)  // create an empty graph with n vertices
{
    this->n=-1;
    allocate(n);  // We want to call allocate in case a derived class needs to setup additional data structures.
    zero_adj();
}


UndirectedGraph::UndirectedGraph(char *g6)  // create a graph from the given graph6 string
{
    read_graph6_string(g6);
}


UndirectedGraph::UndirectedGraph(UndirectedGraph *G, int k)  // create an induced subgraph of G on the vertices 0..k-1
{
    this->n=-1;
    allocate(k);
    
    // We need to copy the adjacencies from G to the new graph.
    // By the magic of colex order, this is the first nchoose2 elements of the adj matrix.
    for (int index=nchoose2-1; index>=0; index--)  // counting down is faster because the condition is testing against 0
        adj[index]=G->adj[index];
}


UndirectedGraph::~UndirectedGraph()
{
    deallocate();
}


void UndirectedGraph::allocate(int n)
    // allocate is a virtual method so that derived classes can handle allocating data structures
{
    if (this->n!=n)
    {
        if (this->n>=0)  // deallocate previous data structures
            this->UndirectedGraph::~UndirectedGraph();
        this->n=n;
        nchoose2=binomial2(n);
        adj=new int[nchoose2];
    }
    //else  // n has not changed and the data structures are already allocated
    //    ;  // nothing to do
}


void UndirectedGraph::deallocate()
    // deallocate is a virtual method so that derived classes can handle deallocating data structures
{
    if (n>=0)  // the graph has allocated data
    {
        delete[] adj;
        
        n=-1;  // data structures have been deallocated
    }
}


inline
void UndirectedGraph::zero_adj()
{
    int index;
    for (index=nchoose2-1; index>=0; index--)  // counting down is faster because the condition is testing against 0
        adj[index]=0;
}


void UndirectedGraph::read_graph6_string(char *g6)
    // Reads in graph6 format, details of the format can be found at Brendan McKay's webpage:
    // http://cs.anu.edu.au/~bdm/data/formats.txt
{
    char *cur;  // the current character in the string that we're considering
    int gn;  // the number of vertices in the graph in g6
    int val,mask;
    int i,j;
    
    cur=g6;
    if (*cur==126)  // the graph has at least 63 vertices
    {
        cur++;  // advance past the first 126
        if (*cur==126)  // the graph has at least 258048 vertices
        {
            cur++;  // advance past the second 126
            gn=*cur-63;
            for (i=1; i<6; i++)  // 6 6-bit words for n
            {
                cur++;
                gn<<=6;
                gn+=*cur-63;
            }
        }
        else  // the graph has between 63 and 258047 vertices
        {
            gn=*cur-63;
            for (i=1; i<3; i++)  // 3 6-bit words for n
            {
                cur++;
                gn<<=6;
                gn+=*cur-63;
            }
        }
    }
    else  // the graph has at most 62 vertices.
        gn=*cur-63;
    cur++;  // move past the information on the number of vertices
    
    allocate(gn);  // this also sets this->n to gn
    
    // read in the adjacency matrix
    val=*cur-63;
    mask=1<<5;  // start with the high bit
    for (j=0; j<gn; j++)  // adj matrix is bit packed in colex order in graph6 format
        for (i=0; i<j; i++)
        {
            set_adj_sorted(i,j,(val&mask)!=0);  // test whether that bit is nonzero
            mask>>=1;
            if (!mask)  // mask has become 0
            {
                cur++;
                val=*cur-63;
                mask=1<<5;
            }
        }
}


void UndirectedGraph::write_graph6_string(char *g6, int length)
    // Writes graph6 format into the string at g6.
    // The buffer string g6 has the length indicated.
    // The string is then zero terminated.
{
    char *cur;  // the current character in the string that we're considering
    long int val,mask;  // we assume that long int is at least 64 bits
    int i,j;
    
    if (9+(n+5)/6>length)
    {
        printf("Output string too short, length=%d but %d needed.\n",length,9+(n+5)/6);
        exit(2);
    }
    
    
    cur=g6;
    if (n<=62)
    {
        *cur=n+63;
        cur++;
    }
    else if (n<=258047)
    {
        *cur=126;
        cur++;
        
        mask=63<<12;
        for (i=12; i>=0; i-=6)  // 3 6-bit words for n
        {
            *cur=((n&mask)>>i)+63;
            mask>>=6;
            cur++;
        }
    }
    else  // if (n<=68719476735)
    {
        *cur=126;
        cur++;
        *cur=126;
        cur++;
        
        mask=((long int)63)<<30;
        for (i=30; i>=0; i-=6)  // 6 6-bit words for n
        {
            *cur=((n&mask)>>i)+63;
            mask>>=6;
            cur++;
        }
    }
    
    // output the adjacency matrix
    val=0;
    mask=1<<5;  // start with the high bit
    for (j=0; j<n; j++)  // adj matrix is bit packed in colex order in graph6 format
        for (i=0; i<j; i++)
        {
            val<<=1;
            val|=get_adj_sorted(i,j)!=0;  // can remove the inequality test if we know the adjacency matrix is only 0s and 1s
            mask>>=1;
            
            if (!mask)  // mask has become 0
            {
                *cur=val+63;
                cur++;
                val=0;
                mask=1<<5;
            }
        }
    
    if (mask!=1<<5)
        // some bits are in val that still need to be outputted
    {
        *cur=val+63;
        cur++;
    }
    
    *cur=0;  // zero terminated
}


void UndirectedGraph::print_adj_matrix()
{
    int i,j;

    printf("Graph has %d vertices.\n",n);
    
    // print column headings, mod 100
    for (j=0; j<n; j++)
        if (j%10==0)
            printf(" %1d",(j/10)%10);
        else
            printf("  ");
    printf("\n");
    
    // print column headings, mod 10
    for (j=0; j<n; j++)
        printf(" %1d",j%10);
    printf("\n");
    
    for (i=0; i<n; i++)
    {
        for (j=0; j<n; j++)
            if (0 && j<=i)
                printf("  ");
            else
                //printf(" %1d",get_adj_sorted(i,j));
                printf(" %1d",get_adj(i,j));  // not sorted if the entire adjacency matrix
            
        // print vertex names at the end of the rows
        printf(" >%2d",i);
        
        printf("\n");
    }
}


/////////////////////////////////////////////////////////////////////////////
// Routines for getting and setting adjacencies.
// Note there are two versions of each routine based on whether it's
// guaranteed that the pair i,j is sorted (i<j).
/////////////////////////////////////////////////////////////////////////////


inline
void UndirectedGraph::set_adj(int i, int j, int val)
{
    adj[pair_to_index(i,j)]=val;
}


inline
void UndirectedGraph::set_adj_sorted(int i, int j, int val)
{
    adj[pair_sorted_to_index(i,j)]=val;
}


inline
int UndirectedGraph::get_adj(int i, int j)
{
    if (i==j)  // we do not have loops
        return 0;
    else
        return adj[pair_to_index(i,j)];
}


inline
int UndirectedGraph::get_adj_sorted(int i, int j)
{
    return adj[pair_sorted_to_index(i,j)];
}


