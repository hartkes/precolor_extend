
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


long long int verify
          (int max_num_colors, int num_verts_to_precolor, UndirectedGraph* G,
           int res, int mod, int splitlevel,
           BIT_MASK vertices_in_orbit_with_previous,
           long long int *count_precolorings_to_return  // to be returned out
          )
{
    int n=G->n;  // the total number of vertices in the graph
    int *c=new int[n];  // the color on each vertex
    int *num_colors_previously_used=new int[n];
    int v;  // the current vertex
    int i,j;
    int good_color_found;  // flag indicating if c[v] is a valid color for v
    int num_precolorings_that_dont_extend=0;  // count of precolorings that do not extend to proper colorings
    long long int count_precolorings=0;  // number of precolorings checked; long long is 64-bits
    
    int odometer;  // for parallelization; keeps track of the number of nodes of the search tree at level splitlevel
    
    // We will color the vertices with the colors 0..max_num_colors-1.
    // In the loop, we attempt to color the vertex with the color c[v].
    // Incrementing the color will occur later if c[v] is not valid for v.
    
    // We deal with symmetry of colors in the following naive way:
    // We assume that vertex 0 is colored 0.
    // num_colors_previously_used[v] means that on vertices 0..v-1, 
    //             only colors 0..num_colors_previously_used[v]-1 are used.
    // When assigning a color to v, we will only go up to num_colors_previously_used[v] (ie, a new color).
    
    
    // We use bit masks to speed up testing if neighbors of v are colored with the proposed c[v].
    BIT_MASK *nbrhd_mask=new BIT_MASK[n];  // a bit mask indicating the (previous) neighbors of each vertex
    BIT_MASK *color_mask=new BIT_MASK[max_num_colors];  // indexed by color; we still need c[v] to index the color_mask array
            // the v-th bit of color_mask[i] indicates if v is colored with color i.
    BIT_MASK cur_mask;  // a single bit set in the position corresponding to the current vertex, v
    BIT_MASK mask_extended_vertices;  // a mask to clear the colors on vertices beyond the precolored vertices
    
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
    
    
    // initialization
    c[0]=0;  // we can assume that vertex 0 is colored 0
    num_colors_previously_used[0]=0;
    cur_mask=1;
    color_mask[0]|=cur_mask;  // the low bit (vertex 0) is set for color 0
    
    v=1;  // we'll actually start with vertex 1
    cur_mask<<=1;
    c[v]=0;  // first we'll trying coloring vertex 1 with color 0
    // note that no color_mask bit is set for v=1 because we haven't tested the color yet (see comment in while loop that searches for a good color for v)
    num_colors_previously_used[v]=1;
    
    odometer=mod;  // initialize the odometer for parallelization; remember that decrementing odometer happens before testing against the residue
    
    
    if (0)  // putting in a root coloring for debugging purposes
    {
        int root_coloring[18]={0,1,2,3,4,0,4,5,4,5,0,5,4,5,1,3,2,3};
        int num_verts_root_coloring=18;
        
        // clear up the previous initialization
        color_mask[0]=0;
        
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
    
    
    while (v>0)  // main loop
    {
        // When we start the loop, we are attempting to color v with c[v], and we need to check if c[v] is valid.
        // If c[v] is valid, then we move to the next vertex.
        // If not, we increment the color for v until we find a good color or run out of colors for v.
        // Note that we will never change the color of vertex 0, which is always colored with color 0.
        
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
                // we allow equality in the second test, since we'll allow c[v] to be a new color, ie num_colors_previously_used[v]
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
            if ((color_mask[c[v]] & nbrhd_mask[v]) == 0)  // no previous neighbors of v are colored with c[v], so c[v] is a valid color for v
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
        BIT_MASK test_mask;
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
            
            // This code allows for parallelization.
            if (v==splitlevel)  // we need to check whether we should go further (deepen the search tree) or not
            {
                odometer--;
                if (odometer<0)
                    odometer=mod-1;  // reset the odometer
                
                //printf("v=%d splitlevel=%d odometer=%d residue=%d modulus=%d\n",v,splitlevel,odometer,res,mod);
                
                if (odometer!=res)  // we will not check this branch
                {
                    // we increment the color of v and continue the main loop
                    color_mask[c[v]]&=~cur_mask;  // clear v's bit for the current color
                    c[v]++;
                    
                    // and now we just want to loop again, checking this new color for v
                    continue;
                }
            }
            
            
            v++;  // we found a good color for v, so we advance to the next vertex so we can try to color it.
            cur_mask<<=1;
            
            if (v<n)  // if v is a vertex needing to be colored, then we reset its color.
            {
                c[v]=(cur_mask & vertices_in_orbit_with_previous)!=0  // vertex v is in orbit with the previous vertex, and so should have a color greater than v-1
                     ? c[v-1]+1  // v=0 should never be in this set, so v-1 is a valid vertex, and the array index will not be out of bounds
                     : 0;  // otherwise, just start with the first color, color 0
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
                
                // we need to backtrack and advance to the next precoloring
                v=num_verts_to_precolor-1;
                cur_mask=1<<v;
                c[v]++;
                
                // we need to clear the color_masks for the vertices from v to n
                for (i=max_num_colors-1; i>=0; i--)
                    color_mask[i]&=mask_extended_vertices;  // this also clears v's color
                
            }
        }
        else // we've gone too far in the colors (no color is available for v) and so need to backtrack
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
                    if (num_precolorings_that_dont_extend<100)  // no point in printing more than 100 bad precolorings
                    {
                        printf("Bad precoloring, count=%5d, c: ",num_precolorings_that_dont_extend);
                        printf(" v=%d  c=",v);
                        for (i=0; i<=v; i++)  // only print the vertices that are precolored
                            printf("%d:%d ",i,c[i]);
                        printf("\n");
                    }
                    else
                    {
                        printf("Too many bad colorings, bombing out. count_precolorings=%lld\n",count_precolorings);
                        exit(11);
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
    //printf("final count_precolorings=%lld\n",count_precolorings);
    
    delete nbrhd_mask;
    delete color_mask;
    
    delete c;
    delete num_colors_previously_used;
    
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
        
        if ((v>0) && closed_nbrhd_mask[v]==closed_nbrhd_mask[v-1])
        {
            printf("%d,",v);
            vertices_in_orbit_with_previous|=(1<<v);
        }
    }
    printf("\n");
    
    delete closed_nbrhd_mask;
    
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
            printf("The number n=%d of vertices in the graph is more than the number %d of bits in a word.",G->n,8*sizeof(BIT_MASK));
            exit(9);
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
        
        printf("Number of all precolorings: %lld\n",count_all_precolorings);
        printf("Number of bad precolorings: %lld\n",count_bad_precolorings);
    }
    
    delete G;
    
    if (count_bad_precolorings==0)
        return 0;  // no bad precolorings found
    else
        return 1;  // normal operation, but bad precolorings found
}
