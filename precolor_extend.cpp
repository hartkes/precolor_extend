
// precolor_extend.cpp
// C++ program to determine if every precoloring of a graph extends to a full proper coloring.
// Copyright 2016 by Stephen Hartke.
// Licensed under the GPL version 3.


// We read lines in from stdin.
// Each line should have the format "7,5,graph6", where 7 is the maximum number of colors to use, and 5 is the number of colors to precolor.  Note that there cannot be spaces.
// If a line starts with '>', then it is treated as a comment.

// Each line presents a precoloring extension problem for a specific graph.  We attempt to precolor (properly) the vertices 0..num_verts_to_precolor-1, and then see if the coloring extends to the rest of the vertices.

/* Command line parameters can be used for parallelization.
 * The system used is inspired by that used in Brendan McKay's geng and in Brinkmann and McKay's plantri.
 * -m specifies a modulus, and the search tree is split into roughly m pieces to examine.
 * This is done by chopping the search tree at a given height (given by the variable splitlevel), 
 * counting the nodes (ie, precolorings) at that level, and only expanding those with the specified residue.
 * 
 * One advantage is that modulo classes work as expected, in that 1 (mod 4) and 3 (mod 4) gives 1 (mod 2).
 * Note that there's a limit to this, as the number of nodes on the level being split is only 100*modulus.
 * 
 * Note that we make some assumptions here:
 * the splitlevel must be less than the number of vertices to precolor (why?  it seems it would be okay otherwise).
 * 
 * If m is really large compared to the number of precolorings, then splitlevel is set to the last precolored vertex.
 * If the modulus is larger than the number of nodes at that level, the last residues (up to mod-1) are the ones that are actually examined, 
 * since we start counting at the mod-1 and count down.
 * 
 */


#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>  // to use getopt to parse the command line
#include <time.h>  // for reporting runtime
#include "graph.h"


#ifdef USE128BITS
    typedef unsigned __int128 BIT_MASK;  // 128-bits, should work with both gcc and Clang
#else
    typedef unsigned long long int BIT_MASK;  // we want a 64-bit unsigned integer for bit masks
#endif

void print_binary(BIT_MASK x, int num_bits)
{
    int i;
    for (i=0; i<num_bits; i++)
    {
        printf("%1d",(int)(x&1));  // print the low bit first
        x>>=1;
    }
}

void print_long(long long int x, int width)
{
    char suffix[]=" tmbtqqssond";
        // the first letter of thousands, million, billion, trillion, etc
    char buffer[width];
    int pos;  // position in the buffer
    int last_digit;
    int digit_count;
    int negative;  // flag to indicate if x is negative
    
    for (pos=0; pos<width; pos++)
        buffer[pos]=' ';  // put spaces in
    
    if (x==0)
        buffer[width-1]='0';
    else
    {
        negative=0;  // flag
        if (x<0)
        {
            negative=1;
            x=-x;
        }
        
        digit_count=0;
        pos=width-1;
        while ((x>0) && (pos>=0))  // digits still remaining and we haven't filled the buffer
        {
            last_digit=x%10;
            x/=10;
            
            digit_count++;
            if ( ((digit_count%3)==1) && (digit_count>1) )
            {
                buffer[pos]=suffix[digit_count/3];
                pos--;
                if (pos<0)
                    break;
            }
            buffer[pos]='0'+last_digit;
            pos--;
        }
        
        if ( (negative) && (pos>=0) )
            buffer[pos]='-';
    }
    
    //for (pos=0; pos<width; pos++)
    //    printf("%c",buffer[pos]);
    
    printf("%.*s",width,buffer);  // how to print a fixed-length char array (a string should be null terminated)
}


long long int verify
          (int max_num_colors, int num_verts_to_precolor, UndirectedGraph* G,
           int res, int mod, int splitlevel,
           BIT_MASK vertices_in_orbit_with_previous,
           long long int *count_precolorings_to_return  // to be returned out
          )
{
    int n=G->n;  // the total number of vertices in the graph
    int *c=new int[n];  // the color on each vertex
    int *max_color_to_try=new int[n];
    int v;  // the current vertex
    int i,j;
    int good_color_found;  // flag indicating if c[v] is a valid color for v
    int num_precolorings_that_dont_extend=0;  // count of precolorings that do not extend to proper colorings
    long long int count_precolorings=0;  // number of precolorings checked; long long is 64-bits
    
    int odometer;  // for parallelization; keeps track of the number of nodes of the search tree at level splitlevel
    
    // We will color the vertices with the colors 1..max_num_colors, but counting down.
    // In the loop, we attempt to color the vertex with the color c[v].
    // Decrementing the color will occur later if c[v] is not valid for v.
    
    
    // We deal with symmetry of colors in the following naive way:
    // We assume that vertex 0 is colored 1.
    // max_color_to_try[v] means that on vertex v, try using colors 1..max_color_to_try[v], but in reverse order.
    //FIXME: Correct the following description.
    // When assigning a color to v, we will start with max_color_to_try[v].
    // Note that max_color_to_try[v] is always <= max_num_colors, but also satisfies (if possible) max_color_to_try[v]=max(c[0],c[1],...,c[v-1])+1.
    
    
    // We use bit masks to speed up testing if neighbors of v are colored with the proposed c[v].
    BIT_MASK *nbrhd_mask=new BIT_MASK[n];  // a bit mask indicating the (previous) neighbors of each vertex
    BIT_MASK *color_mask=new BIT_MASK[max_num_colors+1];  // 1-indexed by color; we still need c[v] to index the color_mask array
            // the v-th bit of color_mask[i] indicates if v is colored with color i.
    BIT_MASK cur_mask;  // a single bit set in the position corresponding to the current vertex, v
    BIT_MASK mask_extended_vertices;  // a mask to clear the colors on vertices beyond the precolored vertices
    BIT_MASK mask_first_n_bits;  // mask with first n positions set; used to test with cur_mask when v<n
    BIT_MASK mask_skip_max_color_to_try;  // mask with bits set for positions *after* the first vertex v where c[v]==max_num_colors
    BIT_MASK mask_bit_set_splitlevel;  // mask with one bit set in position splitlevel
    
    
    //printf("Initializing bit masks...\n");
    // the low bit (0th bit) of a bit mask corresponds to vertex 0, and then in increasing order
    for (v=0; v<n; v++)
    {
        nbrhd_mask[v]=0;
        for (i=v-1; i>=0; i--)
        {
            nbrhd_mask[v]<<=1;
            nbrhd_mask[v]|=(BIT_MASK)G->get_adj_sorted(i,v);  // set the low bit if i and v are adjacent
        }
        /*
        printf("nbrhd_mask[%2d]=",v);
        print_binary(nbrhd_mask[v],sizeof(nbrhd_mask)*8);
        printf("\n");
        //*/
    }
    //printf("Done initializing neighborhood bit masks.\n");
    for (i=max_num_colors; i>0; i--)
        color_mask[i]=0;
    mask_extended_vertices=(((BIT_MASK)1)<<(num_verts_to_precolor-1))-1;  // also clear bit num_verts_to_precolor-1
    /*
    printf("mask_extended_vertices=");
    print_binary(mask_extended_vertices,sizeof(mask_extended_vertices)*8);
    printf("\n");
    printf("Done initializing color bit masks.\n");
    //*/
    
    // initialization
    c[0]=1;  // we can assume that vertex 0 is colored 1
    max_color_to_try[0]=1;
    cur_mask=(BIT_MASK)1;  // bit set in 0th position
    color_mask[1]|=cur_mask;  // the low bit (vertex 0) is set for color 1
    
    v=1;  // we'll actually start with vertex 1
    cur_mask<<=1;
    max_color_to_try[v]=2;
    c[v]=2;  // first we'll trying coloring vertex 1 with color 2
    // note that no color_mask bit is set for v=1 because we haven't tested the color yet (see comment in while loop that searches for a good color for v)
    
    mask_first_n_bits=(((BIT_MASK)1)<<n)-1;  // sets the first n bits
    /*
    printf("mask_first_n_bits=",mask_first_n_bits);
    print_binary(mask_first_n_bits,sizeof(mask_first_n_bits)*8);
    printf("\n");
    //*/
    
    if (splitlevel==n)  // a splitlevel of n indicates no parallelization
        mask_bit_set_splitlevel=0;
    else
        mask_bit_set_splitlevel=((BIT_MASK)1)<<splitlevel;
    //printf("mask_bit_set_splitlevel=%0x, splitlevel=%d\n",mask_bit_set_splitlevel,splitlevel);
    //printf("mask_first_n_bits=%0x\n",mask_first_n_bits);
    
    odometer=mod;  // initialize the odometer for parallelization; remember that decrementing odometer happens before testing against the residue
    
    
    //printf("Starting main loop.\n");
    
    while (1)  // main loop, runs when v>0, but the exit condition while be checked only when backtracking
    {
        // When we start the loop, we are attempting to color v with c[v], and we need to check if c[v] is valid.
        // If c[v] is valid, then we move to the next vertex.
        // If not, we decrement the color for v until we find a good color or run out of colors for v.
        // We use colors 1..max_num_colors and decrement so that it is fast to check if c[v] is 0, and hence we have run out of colors.
        // Note that we will never change the color of vertex 0, which is always colored with color 1.
        
        
        /*
        if (1)//(v==n-1)  //(v>=34) //(1 || v<=14)
        {
            printf(" v=%d  c=",v);
            for (i=0; i<=v; i++)
                //printf("%d:%d(%d) ",i,c[i],max_color_to_try[i]);
                printf("%d:%d ",i,c[i]);
            printf("\n");
            if (0)
                for (i=1; i<=max_num_colors; i++)
                {
                    printf("color_mask[%2d]=",i);
                    print_binary(color_mask[i],sizeof(color_mask[i])*8);
                    printf("\n");
                }
        }
        //*/
        
        // We check if c[v] is valid, and if not, increment it.
        good_color_found=0;  // at the moment, we don't know that c[v] is valid.
        while (c[v])  // if c[v] becomes 0, then we have not found a valid color for v
        {
            // When this loop is entered, no color_mask should have a color set for v.
            /*
            printf("while loop v=%d c[v]=%d\n",v,c[v]);
            /*
            printf("color_mask[c[%2d]]=",c[v]);
            print_binary(color_mask[c[v]],32);
            printf("\n");
            printf("nbrhd_mask[   %2d]=",v);
            print_binary(nbrhd_mask[v],32);
            printf("\n");
            printf("and = %llu  test=%d\n",color_mask[c[v]] & nbrhd_mask[v],(color_mask[c[v]] & nbrhd_mask[v]) == 0);
            //*/
            if ((color_mask[c[v]] & nbrhd_mask[v]) == 0)  // no previous neighbors of v are colored with c[v], so c[v] is a valid color for v
                    // note that bitwise & has lower precedence than equality testing ==
            {
                color_mask[c[v]]|=cur_mask;  // set v's bit for the new color
                good_color_found=1;  // so we've found a good color c[v] for v
                break;
            }
            else
                c[v]--;  // we decrement colors
        }
        
        /*
        // sanity test; make sure that c[v] and color_mask are consistent
        BIT_MASK test_mask;
        for (int u=0; u<=v; u++)
        {
            test_mask=((BIT_MASK)1)<<u;
            for (j=1; j<=max_num_colors && j<=max_color_to_try[u]; j++)
                if (((color_mask[j]&test_mask)!=0) != (j==c[u]))
                {
                    printf("inconsistency! v=%d color=%d\n",u,j);
                    exit(5);
                }
        }
        //*/
        
        //printf("v=%d c[v]=%d good_color_found=%d\n",v,c[v],good_color_found);
        
        if (good_color_found)
        {
            
            // This code enables parallelization.
            if (cur_mask & mask_bit_set_splitlevel)  // same as (v==splitlevel), but more efficient
                // we need to check whether we should go further (deepen the search tree) or not
            {
                //TODO: set odometer to res initially.  Then subtract 1.  When 0, reset odometer to mod and expand branch.  Then only one branch test, and it's a test of whether odometer is not 0.
                odometer--;
                if (odometer<0)
                    odometer=mod-1;  // reset the odometer
                
                //printf("v=%d splitlevel=%d odometer=%d residue=%d modulus=%d\n",v,splitlevel,odometer,res,mod);
                
                if (odometer!=res)  // we will not check this branch
                {
                    // we decrement the color of v and continue the main loop
                    color_mask[c[v]]&=~cur_mask;  // clear v's bit for the current color
                    c[v]--;
                    
                    //printf("v=%d splitlevel=%d odometer=%d residue=%d modulus=%d\n",v,splitlevel,odometer,res,mod);
                    
                    // and now we just want to loop again, checking this new color for v
                    continue;
                }
            }
            
            
            v++;  // we found a good color for v, so we advance to the next vertex so we can try to color it.
            cur_mask<<=1;
            
            if (cur_mask & mask_skip_max_color_to_try)  // if we have already colored a vertex with max_num_colors, then we won't bother with the max_color_to_try
                // Note that this implies that v<n because of the AND with mask_first_n_bits.
                if ((cur_mask & vertices_in_orbit_with_previous)!=0)
                    // vertex v is in orbit with the previous vertex, and so should have a color less than v-1
                    c[v]=c[v-1]-1;
                else
                    c[v]=max_num_colors;
            else
                if (cur_mask & mask_first_n_bits)  // same as (v<n)
                    //TODO: Maybe combine with mask_skip_max_color_to_try??
                    // If we have not gone beyond all of the vertices in the graph, then v is a vertex needing to be colored.
                    // We reset its color.
                {
                    if (max_color_to_try[v-1]==max_num_colors)
                    {
                        max_color_to_try[v]=max_num_colors;  // or could be max_color_to_try[v-1], maybe can combine statement
                        mask_skip_max_color_to_try=( ~(( ((BIT_MASK)1)<<(v+1) )-1) ) & mask_first_n_bits;
                            // mask with bits set for positions *after* the first vertex v where c[v]==max_num_colors
                        
                        /*
                        printf("v=%2d  mask_skip_max_color_to_try=",v);
                        print_binary(mask_skip_max_color_to_try,n);
                        printf("\n");
                        printf("                        cur_mask=");
                        print_binary(cur_mask,n);
                        printf("\n");
                        printf(" v=%d  c=",v);
                        for (i=0; i<=v; i++)
                            printf("%d:%d ",i,c[i]);
                        printf("\n");
                        //*/
                    }
                    else  // max_color_to_try[v-1]<max_num_colors
                    {
                        if (c[v-1]==max_color_to_try[v-1])
                            max_color_to_try[v]=max_color_to_try[v-1]+1;
                        else
                            max_color_to_try[v]=max_color_to_try[v-1];
                        
                        mask_skip_max_color_to_try=0;
                    }
                    
                    if ((cur_mask & vertices_in_orbit_with_previous)!=0)
                        // vertex v is in orbit with the previous vertex, and so should have a color less than v-1, unless v-1 had used a new color
                        // There is a subtlety about combining counting down, using at most one new color, and the consecutive vertices in orbits.
                        // If v-1 and v are in orbits, then in general we want c[v]<c[v-1].  But if c[v-1] is a new color, then we need for c[v] to also possibly be a new color, which would be c[v-1]+1.
                        if (c[v-1]==max_color_to_try[v-1])  // v-1 used a new color
                            c[v]=max_color_to_try[v];  // there's the possibility c[v] will also have a new color
                        else
                            c[v]=c[v-1]-1;
                    else
                        c[v]=max_color_to_try[v];
                    
                    //color_mask[c[v]]|=cur_mask;  // set v's bit for the new color --- this is not needed
                }
                
                else  // v>=n, so we have colored all of the vertices
                {
                    // we have colored (properly) all of the vertices, and so have a good coloring
                    
                    //printf("We have a good coloring!\n");
                    count_precolorings++;
                    //if (count_precolorings%1000000==0)  // change this to an & statement
                    if ((count_precolorings&0xffffff)==0)  // 0xfffff is 2^30==1048575
                    //if (1)
                    {
                        //printf("count_precolorings=%14lld",count_precolorings);
                        printf("count_precolorings=");
                        print_long(count_precolorings,20);
                        printf("  c=");
                        for (i=0; i<num_verts_to_precolor; i++)
                            printf("%d:%d ",i,c[i]-1);  // TODO: Note the -1 to match old output!
                        printf("\n");
                    }
                    
                    // we need to backtrack and advance to the next precoloring
                    v=num_verts_to_precolor-1;
                    cur_mask=((BIT_MASK)1)<<v;
                    c[v]--;  // decrement color
                    
                    // we need to clear the color_masks for the vertices from v to n
                    for (i=max_num_colors; i>0; i--)
                        color_mask[i]&=mask_extended_vertices;  // this also clears v's color
                    
                }
        }
        else // we've gone too far in the colors (no color is available for v) and so need to backtrack
        {
            // note that color_mask[c[v]] is not set (and c[v] is not valid)
            v--;
            cur_mask>>=1;
            if (v==0)  // we have backtracked to the first vertex and thus are finished.  Note we do not change the color on vertex 0.
                break;
            if (v==num_verts_to_precolor-1)
            {
                // We have backtracked to a precoloring without finding an extension that is a proper coloring.
                count_precolorings++;
                num_precolorings_that_dont_extend++;
                
                // So we print this bad precoloring to report the failure.
                printf("Bad precoloring, count=%5d,      c=",num_precolorings_that_dont_extend);
                for (i=0; i<=v; i++)  // only print the vertices that are precolored
                    printf("%d:%d ",i,c[i]);
                printf("\n");
                
                if (num_precolorings_that_dont_extend>=100)  // no point in finding more than 100 bad precolorings
                {
                    printf("Too many bad colorings, bombing out. count_precolorings=%lld\n",count_precolorings);
                    break;
                }
            }
            
            // in any case, decrement the color of v
            color_mask[c[v]]&=~cur_mask;  // clear v's bit for this color
            c[v]--;
        }  // end of backtrack
    
    }  // end of main while loop
    
    //printf("final count_precolorings=%lld\n",count_precolorings);
    
    delete[] nbrhd_mask;
    delete[] color_mask;
    
    delete[] c;
    delete[] max_color_to_try;
    
    *count_precolorings_to_return=count_precolorings;
    return num_precolorings_that_dont_extend;
}


BIT_MASK compute_vertices_in_orbit_with_previous(UndirectedGraph* G)
{
    int n=G->n;  // the total number of vertices in the graph
    int v;  // the current vertex
    int i;
    
    BIT_MASK *closed_nbrhd_mask=new BIT_MASK[n];  // a bit mask indicating the closed neighborhood of each vertex
    BIT_MASK vertices_in_orbit_with_previous=0;
    
    printf("Vertices in orbit with the previous vertex in the order: ");
    // the low bit (0th bit) of a bit mask corresponds to vertex 0, and then in increasing order
    for (v=0; v<n; v++)
    {
        closed_nbrhd_mask[v]=0;
        for (i=0; i<n; i++)
            if (i==v)
                closed_nbrhd_mask[v]|=(((BIT_MASK)1)<<i);  // we compute closed neighborhoods
            else if (G->get_adj(i,v))  // note that i and v are not sorted
                closed_nbrhd_mask[v]|=(((BIT_MASK)1)<<i);
        
        if ((v>0) && (closed_nbrhd_mask[v]==closed_nbrhd_mask[v-1]))
        {
            printf("%d,",v);
            vertices_in_orbit_with_previous|=(((BIT_MASK)1)<<v);
        }
    }
    printf("\n");
    
    delete[] closed_nbrhd_mask;
    
    return vertices_in_orbit_with_previous;
}


int splitlevel_heuristic
       (int max_num_colors, int num_verts_to_precolor, UndirectedGraph* G,
        int mod
       )
{
    UndirectedGraph *H;
    long long int count_all_precolorings;
    int level;
    BIT_MASK vertices_in_orbit_with_previous;
    
    printf("Estimating the splitlevel to obtain roughly equal modulo classes.\n");
    
    for (level=1; level<num_verts_to_precolor-1; level++)
        // if there are not enough nodes in the search tree, we set the level to be the last precolored vertex, ie, num_verts_to_precolor-1
    {
        //printf("Testing splitlevel=%d\n",level);
        H=new UndirectedGraph(G,level);
        vertices_in_orbit_with_previous=compute_vertices_in_orbit_with_previous(H);
        count_all_precolorings=0;
        verify(max_num_colors,
               H->n,  // all of the vertices of H are to be precolored
               H,
               0,1,H->n,
               vertices_in_orbit_with_previous,
               &count_all_precolorings
              );
        delete H;
        
        //printf("count_all_precolorings=%lld\n",count_all_precolorings);
        
        if (count_all_precolorings > 100*mod)
            // the constant 100 is fairly arbitrary
            break;
    }
    return level;
}


int main(int argc, char *argv[])
{
    const int max_line_length=1000;
    char line_in[max_line_length];
    char *cur;  // the current character that we're considering in line_in
    int cur_index;  // the index of the current character that we're considering in line_in
    
    int max_num_colors;
    int num_verts_to_precolor;
    
    int res,mod,splitlevel_arg,splitlevel;  // for parallelizing
    int opt;  // for parsing the command line
    
    UndirectedGraph *G;
    G=new UndirectedGraph();
    
    int i,j;
    BIT_MASK vertices_in_orbit_with_previous;
    
    long long int count_bad_precolorings,count_all_precolorings;
    
    clock_t start,end;  // for reporting CPU runtime
    
    
    // print info
    printf("precolor_extend compiled using %lu bit masks.\n",sizeof(BIT_MASK)*8);
    
    // defaults
    splitlevel_arg=-1;
    res=-1;
    mod=-1;
    
    // parse the command line
    while ((opt=getopt(argc,argv,"r:m:s:"))!=-1)  // the colons indicate the options take required arguments
    {
        switch (opt)
        {
            case 'r':
                sscanf(optarg,"%d",&res);
                break;
            case 'm':
                sscanf(optarg,"%d",&mod);
                break;
            case 's':
                sscanf(optarg,"%d",&splitlevel_arg);
                break;
            case '?':
                printf("Error parsing command line arguments; problem with option %c\n",optopt);
                printf("USAGE: precolor_extend -r residue -m modulus [-s splitlevel]\n");
                printf("-r and -m must be used together; -s can only be used if -r/-m also are.\n");
                exit(8);
            default:
                ;
        }
    }
    printf("Parallelization parameters set: res=%d mod=%d splitlevel_arg=%d\n",res,mod,splitlevel_arg);
    
    if ((res==-1) ^ (mod==-1))  // using bitwise xor here since there is no logical xor
    {
        printf("-r and -m must be used together\n");
        exit(8);
    }
    if ((splitlevel_arg!=-1) && (mod==-1))
    {
        printf("-s can only be used if -r and -m also are.\n");
        exit(8);
    }
    
    // We read lines in from stdin.
    // Each line should have the format "7,5,graph6", where 7 is the maximum number of colors to use, and 5 is the number of colors to precolor.  Note that there cannot be spaces.
    // If a line starts with '>', then it is treated as a comment.
    
    while (fgets(line_in,max_line_length,stdin)!=0)
    {
        if (line_in[0]=='>')  // treat this line as a comment
            continue;
        
        start=clock();  // record starting time
        
        cur=line_in;
        // maybe use %n in scanf?  Yes!  %n will store in a variable how many characters have been read in.  We need to use an index then, instead of a char pointer.
        sscanf(cur,"%d",&max_num_colors);
        for ( ; *cur!=','; cur++); cur++;  // advance cur past the first entry and the comma
        sscanf(cur,"%d",&num_verts_to_precolor);
        for ( ; *cur!=','; cur++); cur++;  // advance cur past the second entry and the comma
        G->read_graph6_string(cur);
        
        printf("Input read: max_num_colors=%d num_verts_to_precolor=%d n=%d\n",max_num_colors,num_verts_to_precolor,G->n);
        printf(">>graph6<<%s",cur);  // newline still present in line_in
        
        if (G->n > 8*sizeof(BIT_MASK))
        {
            printf("The number n=%d of vertices in the graph is more than the number %d of bits in a word.",G->n,(int)(8*sizeof(BIT_MASK)));
            exit(9);
        }
        
        if (num_verts_to_precolor<1)
        {
            // We always need to have at least one vertex precolored.  This is vertex 0, which is always colored 0 and doesn't change.
            // Seting num_verts_to_precolor to 1 essentially is just verifying that the graph can be colored with max_num_colors colors.
            printf("Setting num_verts_to_precolor to 1.\n");
            num_verts_to_precolor=1;
        }
        
        vertices_in_orbit_with_previous=compute_vertices_in_orbit_with_previous(G);
            // compute the orbits before estimating the splitlevel, if necessary
        
        if (mod==-1)  // not using parallelization
        {
            splitlevel=G->n;  // will never reach this level
            printf("not parallelizing\n");
        }
        else 
        {
            if (splitlevel_arg!=-1)
                splitlevel=splitlevel_arg;
            else
                splitlevel=splitlevel_heuristic(max_num_colors,num_verts_to_precolor,G,
                                                mod);
            printf("parallelizing with splitlevel=%d\n",splitlevel);
        }
        
        count_all_precolorings=0;
        count_bad_precolorings=verify(max_num_colors,num_verts_to_precolor,G,
                                      res,mod,splitlevel,
                                      vertices_in_orbit_with_previous,
                                      &count_all_precolorings
                                     );
        
        //printf("Number of all precolorings: %lld\n",count_all_precolorings);
        printf("# all precolorings:");
        print_long(count_all_precolorings,20);
        printf("\n");
        printf("# bad precolorings: %lld\n",count_bad_precolorings);
        
        end=clock();
        printf("CPU time used: %.3f seconds\n",((double)(end-start))/CLOCKS_PER_SEC);
    }
    
    delete G;
    
    if (count_bad_precolorings==0)
        return 0;  // no bad precolorings found
    else
        return 1;  // normal operation, but bad precolorings found
}
