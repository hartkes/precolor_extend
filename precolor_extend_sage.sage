#!/usr/bin/env sage

# Script to compute precoloring extension for graphs.


def precoloring_extension(max_num_colors,num_verts_to_precolor,G):

    n=G.num_verts()
    #print(f"Running with {max_num_colors=} {num_verts_to_precolor=} {n=} {G.graph6_string()=}")
    c=[None]*n  # color on each vertex
    count_precolorings=0
    v=0  # the current vertex
    
    # Compute vertices that have the same closed neighborhood as their predecessor.  These are thus in the same orbit.
    vertices_in_orbit_with_previous=set()
    for v in range(1,n):
        if set(G.neighbors(v,closed=True))==set(G.neighbors(v-1,closed=True)):
            vertices_in_orbit_with_previous.add(v)
    print(f"vertices_in_orbit_with_previous={sorted(list(vertices_in_orbit_with_previous))}")
    
    
    # The vertices are 0..n-1.
    # The colors are 1..max_num_colors.  We count down.

    # Initialization
    c[0]=1
    c[1]=2
    v=1
    
    reuse_extension=False  # no extension yet
    
    while v>0:
        
        s=", ".join([f"{x}:{c[x]}" for x in range(v+1)])
        print(f"Starting main loop {v=} c={s}")
        
        # We look for a valid color for v, starting with c[v].
        good_color_found=False
        while c[v]>0:  # if c[v]==0, then a good color was not found
            # We check if c[v] is a valid color, ie, the color does not appear on a previous neighbor.
            for w in G.neighbors(v):
                if w<v and c[w]==c[v]:  # c[v] is *not* a valid color
                    break
            else:
                # no bad neighbors, so c[v] is a valid color
                good_color_found=True
                break  # out of while loop
            
            c[v]-=1  # advance to next color
        
        #print(f"Done looking for color, {v=} {good_color_found=} {c[v]=}")
        
        if good_color_found:
            #TODO: remove "good_color_found" and replace with c[v]==0
            
            # parallelization in here
            
            # advance to the next vertex
            v+=1
            
            # if we have now colored all precolored vertices, then try to reuse previous extension
            # Should we do this before advancing v?
            if (v==num_verts_to_precolor) and reuse_extension:
                #print("We are reusing the extension!")
                while v<n:
                    # We check if c[v] is a valid color, ie, the color does not appear on a previous neighbor.
                    for w in G.neighbors(v):
                        if w<v and c[w]==c[v]:  # c[v] is *not* a valid color
                            break
                    else:
                        # no bad neighbors, so c[v] is a valid color
                        v+=1  # keep color c[v] on v
                        continue  # advance v to next vertex
                    
                    break  # out of while loop
            
            if v==n:  # all vertices have been colored, we have successfully extended the precoloring
                count_precolorings+=1
                #s=", ".join([f"{x}:{c[x]}" for x in range(num_verts_to_precolor)])
                #print(f"Good precoloring, {count_precolorings=:5} c={s}")
                
                v=num_verts_to_precolor-1
                c[v]-=1  # advance the color
                
                reuse_extension=True  # we can try to reuse this extension for the next precoloring
                
                # go back to beginning of while loop
            else:
                if v in vertices_in_orbit_with_previous:  # break symmetry with the previous vertex
                    if c[v-1]==min( max(c[:v-1])+1, max_num_colors ):  # v-1 used a new color
                        c[v]=min( c[v-1]+1, max_num_colors )  # v can use a new color, if this doesn't exceed max_num_colors
                    else:
                        # We set the color of v to be less than the color of v-1, to break symmetry.
                        # Note that v is adjacent to v-1 (since same closed neighborhood), and thus c[v] cannot equal c[v-1].
                        c[v]=c[v-1]-1
                    
                else:
                    c[v]=min( max(c[:v])+1, max_num_colors )
                        # TODO: check that this is what the C++ code does
                        # TODO: Is this what max_color_to_try is?
                    
                # TODO: re-using extensions
                # TODO: parallelization
                
                # go back to beginning of while loop
        
        else:  # no good_color_found, so we backtrack
            v-=1
            
            if v==num_verts_to_precolor-1:
                # We have backtracked to a precoloring without finding a good extension.
                # This is a *bad* precoloring.
                
                # unless we had been trying to reuse the previous extension
                if reuse_extension:
                    #THOUGHT: If we're counting precolorings, then no need to re-use extensions.
                    #print("Reusing extension failed, trying to extend from scratch.")
                    reuse_extension=False
                    # advance to the next vertex
                    v+=1
                    
                    # Set c[v].  This is code copied from above.  Can we be smarter and reuse that code somehow?
                    if v in vertices_in_orbit_with_previous:  # break symmetry with the previous vertex
                        if c[v-1]==min( max(c[:v-1])+1, max_num_colors ):  # v-1 used a new color
                            c[v]=min( c[v-1]+1, max_num_colors )  # v can use a new color, if this doesn't exceed max_num_colors
                        else:
                            # We set the color of v to be less than the color of v-1, to break symmetry.
                            # Note that v is adjacent to v-1 (since same closed neighborhood), and thus c[v] cannot equal c[v-1].
                            c[v]=c[v-1]-1
                        
                    else:
                        c[v]=min( max(c[:v])+1, max_num_colors )
                            
                            
                else:  # we have failed to extend even when starting fresh
                    print(f"Bad precoloring! {c=}")
                    return False
            
            if v==0:
                break  # break of out of while loop, done
            
            c[v]-=1  # advance the color
            # go back to the beginning of while loop
    
    print(f"{count_precolorings=}")
    return True  # no bad precolorings found, all precolorings extend


def read_input(input_filename: str):
    # Read file input_filename and parse each line for precoloring extension.

    with open(input_filename,'rt') as f:
        for line in f:
            if line.startswith('>'):
                continue
            else:
                data=line.strip().split(',')
                max_num_colors=int(data[0])
                num_verts_to_precolor=int(data[1])
                G=Graph(data[2])
                result=precoloring_extension(max_num_colors,num_verts_to_precolor,G)
                if result:
                    print(f"G is reducible!")
                else:
                    print("G has a bad precoloring!")

import sys

if __name__=="__main__":

    if len(sys.argv)<2:
        print("SYNTAX: precoloring_extension_sage.sage <filename.txt>")
        exit(99)

    read_input(sys.argv[1])
