
// precolor_extend.cpp
// C++ program to determine if every precoloring of a graph extends to a full proper coloring.
// Written by Stephen Hartke
// Licensed under the GPL version 3.


// We read lines in from stdin.
// The first line should have the format "7,5,graph6", where 7 is the maximum number of colors to use, 5 is the number of colors to precolor, and graph6 is the graph6 string for the graph.
// We precolor (properly) the vertices 0..num_verts_to_precolor-1, and then see if the coloring extends to the rest of the vertices.
// The second line indicates a root coloring to start with; colors separated by commas.  This is for parallelizing the checking.
// The third line indicates a comma-separated list of vertices that are each in an orbit with the previous vertex.  Hence for such a vertex, it should have a color greater than the previous vertex.  This partially deals with symmetry (particularly the consecutive vertices that are leaves adjacent to the same stem vertex).



#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "graph.h"


typedef unsigned long long int BIT_MASK;  // we want a 64-bit unsigned integer for bit masks


void print_binary(BIT_MASK x, int num_bits)
{
    int i;
    for (i=0; i<num_bits; i++)
    {
        printf("%1d",x&1);  // print the low bit first
        x>>=1;
    }
}


int verify(int max_num_colors, int num_verts_to_precolor, UndirectedGraph* G,
           int num_verts_root_coloring, int *root_coloring, BIT_MASK vertices_in_orbit_with_previous)
{
    int n=G->n;  // the total number of vertices in the graph
    int *c=new int[n];  // the color on each vertex
    int *num_colors_previously_used=new int[n];
    int v;  // the current vertex
    int i,j;
    int good_color_found;  // flag indicating if c[v] is a valid color for v
    int num_precolorings_that_dont_extend=0;  // count of precolorings that do not extend to proper colorings
    long long int count_precolorings=0;  // number of precolorings checked; long long is 64-bits
    
    
    // We will color the vertices with the colors 0..max_num_colors-1.
    // In the loop, we attempt to color the vertex with the color c[v].
    // Incrementing the color will occur at the beginning of the loop.
    
    // We deal with symmetry of colors in the following way:
    // We assume that vertex 0 is colored 0.
    // num_colors_previously_used[v] means that on vertices 0..v-1, 
    //             only colors 0..num_colors_previously_used[v]-1 are used.
    // When assigning a color to v, we will only go up to num_colors_previously_used[v] (ie, a new color).
    
    
    // to speed up testing if neighbors of v are colored with the proposed c[v]
    BIT_MASK *nbrhd_mask=new BIT_MASK[n];  // a bit mask indicating the (previous) neighbors of each vertex
    BIT_MASK *color_mask=new BIT_MASK[max_num_colors];  // indicates if a given vertex is colored with that color; we will still need c[v] to index the color_mask array
    BIT_MASK cur_mask;  // a single bit set in the position corresponding to the current vertex, v
    BIT_MASK mask_extended_vertices;  // a mask to clear the colors on vertices beyond the precolored vertices
    BIT_MASK test_mask;
    
    //printf("Initializing bit masks...\n");
    // the low bit (0th bit) of a bit mask corresponds to vertex 0, and then in increasing order
    for (v=0; v<n; v++)
    {
        nbrhd_mask[v]=0;
        for (i=v-1; i>=0; i--)
        {
            nbrhd_mask[v]<<=1;
            nbrhd_mask[v]|=G->get_adj_sorted(i,v);  // set the low bit if i and v are adjacent
        }
    }
    //printf("Done initializing neighborhood bit masks.\n");
    for (i=0; i<max_num_colors; i++)
        color_mask[i]=0;
    mask_extended_vertices=(1<<num_verts_to_precolor-1)-1;  // also clear bit num_verts_to_precolor-1
    //printf("Done initializing color bit masks.\n");
    
    
    // if num_verts_to_precolor>=n, this signals that we're generating root colorings.
    // For the code later to work properly when advancing past the root coloring, we need num_verts_to_precolor=n.
    if (num_verts_to_precolor>=n)
        num_verts_to_precolor=n;
    
    
    // initialization
    if (num_verts_root_coloring==0)  // no vertices colored in the root coloring
    {
        c[0]=0;  // we can assume that vertex 0 is colored 0
        num_colors_previously_used[0]=0;
        cur_mask=1;
        color_mask[0]|=cur_mask;  // the low bit (vertex 0) is set for color 0
        v=1;
        cur_mask<<=1;
        c[v]=0;  // need to start
        color_mask[0]|=cur_mask;
        num_colors_previously_used[v]=1;
        
        // for initialization purposes, we can assume that vertex 0 is part of the root coloring, since vertex 0 is always colored 0.
        // This has some convenience, as we may assume that v is always positive, and hence c[v-1] is not a problem.
        num_verts_root_coloring=1;
    }
    else
        // initialize with the vertices colored in the root coloring
    {
        cur_mask=1;
        for (v=0; v<num_verts_root_coloring; v++)
        {
            c[v]=root_coloring[v];
            color_mask[c[v]]|=cur_mask;
            if (v==0)
                num_colors_previously_used[0]=0;
            else
                num_colors_previously_used[v]=(c[v-1]==num_colors_previously_used[v-1]
                                                             // did we use a new color on v-1?
                                              ? num_colors_previously_used[v-1]+1
                                              : num_colors_previously_used[v-1]   );
            
            // increment
            cur_mask<<=1;
        }
        
        // set up the next vertex
        // here, v=num_verts_root_coloring;
        c[v]=(cur_mask & vertices_in_orbit_with_previous)!=0  // vertex v should have a color greater than v-1
                ? c[v-1]+1  // v=0 should never be in this set, so v-1 is valid
                : 0;
        num_colors_previously_used[v]=(c[v-1]==num_colors_previously_used[v-1]
                                                        // did we use a new color on v-1?
                                        ? num_colors_previously_used[v-1]+1
                                        : num_colors_previously_used[v-1]   );
        
    }
    
    // v=num_verts_root_coloring; // this should be the starting condition
    while (v>=num_verts_root_coloring)  // main loop
    {
        // When we start the loop, we are attempting to color v, and we need to check if c[v] is valid, and if not, increment it.
        
        /*
        if (1 || v<=14)
        {
            printf(" v=%d  c=",v);
            for (i=0; i<=v; i++)
                printf("%d:%d ",i,c[i]);
            printf("\n");
            for (i=0; i<max_num_colors; i++)
            {
                printf("color_mask[%2d]=",i);
                print_binary(color_mask[i],32);
                printf("\n");
            }
        }
        //*/
        
        // We check if c[v] is valid, and if not, increment it.
        good_color_found=0;  // at the moment, we don't know that c[v] is valid.
        while (c[v]<max_num_colors && c[v]<=num_colors_previously_used[v])
        {
            // When this loop is entered, no color_mask should have a color set for v.
            /*
            printf("while loop v=%d c[v]=%d\n",v,c[v]);
            printf("color_mask[c[%2d]]=",c[v]);
            print_binary(color_mask[c[v]],32);
            printf("\n");
            printf("nbrhd_mask[   %2d]=",v);
            print_binary(nbrhd_mask[v],32);
            printf("\n");
            printf("and = %llu  test=%d\n",color_mask[c[v]] & nbrhd_mask[v],(color_mask[c[v]] & nbrhd_mask[v]) == 0);
            */
            if ((color_mask[c[v]] & nbrhd_mask[v]) == 0)  // no previous neighbors of v are colored with c[v]
                    // note that bitwise & has lower precedence than equality testing ==
            {
                color_mask[c[v]]|=cur_mask;  // set v's bit for the new color
                good_color_found=1;  // so we've found a good color c[v] for v
                break;
            }
            else
                c[v]++;
        }
        
        /*
        // sanity test; make sure that c[v] and color_mask are consistent
        for (i=0; i<=v; i++)
        {
            test_mask=1<<i;
            for (j=0; j<max_num_colors && j<=num_colors_previously_used[i]; j++)
                if (((color_mask[j]&test_mask)!=0) != (j==c[i]))
                {
                    printf("inconsistency! v=%d color=%d\n",i,j);
                    exit(5);
                }
        }
        //*/
        
        //printf("v=%d c[v]=%d good_color_found=%d\n",v,c[v],good_color_found);
        
        if (good_color_found)
        {
            v++;
            cur_mask<<=1;
            if (v<n)  // if v is still a vertex, then we reset its color.
            {
                c[v]=(cur_mask & vertices_in_orbit_with_previous)!=0  // vertex v should have a color greater than v-1
                     ? c[v-1]+1  // v=0 should never be in this set, so v-1 is valid
                     : 0;
                //color_mask[c[v]]|=cur_mask;  // set v's bit for the new color --- this is not needed
                num_colors_previously_used[v]=(c[v-1]==num_colors_previously_used[v-1]
                                                             // did we use a new color on v-1?
                                              ? num_colors_previously_used[v-1]+1
                                              : num_colors_previously_used[v-1]   );
            }
            else
            {
                // we have colored (properly) all of the vertices, and so have a good coloring
                
                //printf("We have a good coloring!\n");
                count_precolorings++;
                //if (count_precolorings%1000000==0)  // change this to an & statement
                if ((count_precolorings&0xffffff)==0)  // 0xfffff is 2^30==1048575
                {
                    printf("count_precolorings=%14lld",count_precolorings);
                    printf(" v=%d c=",v);
                    for (i=0; i<=v; i++)
                        printf("%d:%d ",i,c[i]);
                    printf("\n");
                }
                
                if (num_verts_to_precolor==n)  
                    // This indicates that we are generating root colorings.
                    // So we'll output the generated coloring.
                {
                    printf("R=");  // for Root coloring
                    for (i=0; i<n; i++)
                    {
                        printf("%d",c[i]);
                        if (i<n-1)
                            printf(",");
                    }
                    printf("\n");
                    
                    // in this case, num_verts_to_precolor=n
                }
                
                // we need to backtrack and advance to the next precoloring
                v=num_verts_to_precolor-1;
                cur_mask=1<<v;
                c[v]++;
                
                // we need to clear the color_masks for the vertices from v to n
                for (i=max_num_colors-1; i>=0; i--)
                    color_mask[i]&=mask_extended_vertices;  // this also clears v's color
                
            }
        }
        else // we've gone too far in the colors and so need to backtrack
        {
            // note that color_mask[c[v]] is not set (and c[v] is not valid)
            v--;
            cur_mask>>=1;
            if (v>0)  // c[0] should never be incremented
            {
                if (v==num_verts_to_precolor-1)
                {
                    // We have backtracked to a precoloring without finding an extension that is a proper coloring
                    // So we print this precoloring to report the failure.
                    num_precolorings_that_dont_extend++;
                    if (num_precolorings_that_dont_extend<100000)  // no point in printing more than 100 bad precolorings
                    {
                        printf("Bad precoloring, count=%5d, c: ",num_precolorings_that_dont_extend);
                        printf(" v=%d  c=",v);
                        for (i=0; i<=v; i++)  // only print the vertices that are precolored
                            printf("%d:%d ",i,c[i]);
                        printf("\n");
                    }
                    count_precolorings++;
                }
                
                // in any case, increment the color of v
                color_mask[c[v]]&=~cur_mask;  // clear v's bit for this color
                c[v]++;
            }
            //else
            //    break;  // no more precolorings to check; but this will be handled by the condition in the while loop
        }
    }
    printf("final count_precolorings=%lld\n",count_precolorings);
    
    delete nbrhd_mask;
    delete color_mask;
    
    delete c;
    delete num_colors_previously_used;
    
    return num_precolorings_that_dont_extend;
}


int main()
{
    const int max_line_length=1000;
    char line_in[max_line_length];
    char *cur;  // the current character that we're considering in line_in
    int cur_index;  // the index of the current character that we're considering in line_in
    
    int max_num_colors;
    int num_verts_to_precolor;
    
    UndirectedGraph *G;
    G=new UndirectedGraph();
    
    int *root_coloring;  // for initializing; used for distributing the computation
    int num_verts_root_coloring;
    int i,j;
    BIT_MASK vertices_in_orbit_with_previous;
    
    int count_bad;
    
    // We read lines in from stdin.
    // The first line should have the format "7,5,graph6", where 7 is the maximum number of colors to use, and 5 is the number of colors to precolor.
    // We precolor (properly) the vertices 0..num_verts_to_precolor-1, and then see if the coloring extends to the rest of the vertices.
    // The second line indicates a root coloring to start with; colors separated by commas.
    // The third line indicates a comma-separated list of vertices that are each in an orbit with the previous vertex.  Hence for such a vertex, it should have a color greater than the previous vertex.  This partially deals with symmetry (particularly the consecutive vertices that are leaves adjacent to the same stem vertex).
    
    if (fgets(line_in,max_line_length,stdin)==NULL)  // problem reading in
    {
        printf("Can't read first line of input!\n");
        exit(1);
    }
    cur=line_in;
    // maybe use %n in scanf?
    sscanf(cur,"%d",&max_num_colors);
    for ( ; *cur!=','; cur++); cur++;  // advance cur past the first entry and the comma
    sscanf(cur,"%d",&num_verts_to_precolor);
    for ( ; *cur!=','; cur++); cur++;  // advance cur past the second entry and the comma
    G->read_graph6_string(cur);
    
    printf("max_num_colors=%d num_verts_to_precolor=%d n=%d\n",max_num_colors,num_verts_to_precolor,G->n);
    printf(">>graph6<<%s",cur);  // newline still present in line_in
    
    if (fgets(line_in,max_line_length,stdin)==NULL)  // problem reading in
    {
        printf("Can't read second line of input!\n");
        exit(2);
    }
    root_coloring=new int[G->n];
    cur_index=0;
    num_verts_root_coloring=0;
    while (cur_index<strlen(line_in))  // fgets always null terminates the returned string
    {
        //printf("cur_index=%d strlen(line_in)=%d\n",cur_index,strlen(line_in));
        sscanf(&line_in[cur_index],"%d%n",&root_coloring[num_verts_root_coloring],&j);
        //printf("characters read j=%d line_in=%s\n",j,&line_in[cur_index]);
        //printf("i=%d root_coloring=%d\n",num_verts_root_coloring,root_coloring[num_verts_root_coloring]);
        num_verts_root_coloring++;
        if (num_verts_root_coloring>=G->n)  // make sure we don't read too many
            break;
        cur_index+=j;  // the number of characters read by 
        for ( ; cur_index<strlen(line_in) && line_in[cur_index]!=','; cur_index++); cur_index++;  // move past comma
    }
    
    printf("Number of vertices in the root coloring=%d\n",num_verts_root_coloring);
    if (num_verts_root_coloring>num_verts_to_precolor)  // this doesn't seem practical, but would it actually cause a problem?
    {
        printf("We can't have num_verts_root_coloring>num_verts_to_precolor!\n");
        exit(2);
    }

    if (fgets(line_in,max_line_length,stdin)==NULL)  // problem reading in
    {
        printf("Can't read third line of input!\n");
        exit(3);
    }
    vertices_in_orbit_with_previous=0;
    cur_index=0;
    while (cur_index<strlen(line_in))  // fgets always null terminates the returned string
    {
        sscanf(&line_in[cur_index],"%d%n",&i,&j);
        printf("vertex in orbit with the previous vertex i=%d\n",i);
        if (i>=0 && i<G->n)
            vertices_in_orbit_with_previous|=1<<i;  // use a bit mask to indicate these vertices
        cur_index+=j;  // the number of characters read by 
        for ( ; cur_index<strlen(line_in) && line_in[cur_index]!=','; cur_index++); cur_index++;  // move past comma
    }
    
    count_bad=verify(max_num_colors,num_verts_to_precolor,G,
                     num_verts_root_coloring,root_coloring,vertices_in_orbit_with_previous);
    printf("Number of bad precolorings: %d\n",count_bad);
    
    delete G;
    delete root_coloring;
}
