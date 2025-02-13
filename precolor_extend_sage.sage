#!/usr/bin/env sage

# Sage program to verify precoloring extension for graphs.


def precoloring_extension(max_num_colors,num_verts_to_precolor,G,
                          res,mod,splitlevel,  # for parallelization
                          debuglevel=0,  # int, for controlling how much debugging info to print
                                         # 0 is no extra debug info; higher numbers for more info.
                          ):

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
    
    odometer=0  # for parallelization
    
    main_loop_counter=0  # for testing
    
    while v>0:
        
        if debuglevel>=3:
            main_loop_counter+=1
            #s=" ".join([f"{x}:{c[x]}" for x in range(v+1)])
            print(f"StartMainLoop count={main_loop_counter:14} {v=:2} c=",end='')
            for i in range(v+1):
                print(f"{i}:{c[i]} ",end='')
            print()  # newline
        
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
            
            # parallelization
            if v==splitlevel:
                odometer=(odometer+1) % mod
                if debuglevel>=3:
                    print(f"at splitlevel {v=} {odometer=} {res=}")
                if odometer!=res:
                    c[v]-=1
                    continue  # do not advance v, continue on main while loop
            
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
                
                if v<n:
                    # We have partially reused the previous extension, but the previous extension is not completely good.  So we will continue searching for a good extension, continuing at v.
                    c[v]-=1  # advance the color
                    continue  #  continue the main loop
            
            
            if v==n:  # all vertices have been colored, we have successfully extended the precoloring
                count_precolorings+=1
                #s=", ".join([f"{x}:{c[x]}" for x in range(num_verts_to_precolor)])
                #print(f"Good precoloring, {count_precolorings=:5} c={s}")
                
                v=num_verts_to_precolor-1
                c[v]-=1  # advance the color
                
                reuse_extension=True  # we can try to reuse this extension for the next precoloring
                
                # go back to beginning of while loop
            else:
                if v>=num_verts_to_precolor:
                    # We do not constrain the colors used for the extension vertices.
                    c[v]=max_num_colors
                else:
                    if v in vertices_in_orbit_with_previous:  # break symmetry with the previous vertex
                        if c[v-1]==max_num_colors:
                            # All colors have already been seen, and we want the color of c[v] to be different than c[v-1] (since they are adjacent).
                            # We set the color of v to be less than the color of v-1, to break symmetry.
                            # Note that v is adjacent to v-1 (since same closed neighborhood), and thus c[v] cannot equal c[v-1].
                            c[v]=c[v-1]-1
                            
                        elif c[v-1]==max(c[:v-1])+1:  # v-1 used a new color
                            c[v]=c[v-1]+1  # v can use a new color
                            # Note this will not exceed max_num_colors because of the previous case.
                            
                        else:
                            # We set the color of v to be less than the color of v-1, to break symmetry.
                            # Note that v is adjacent to v-1 (since same closed neighborhood), and thus c[v] cannot equal c[v-1].
                            c[v]=c[v-1]-1
                        
                    else:
                        # On the vertices 0..v-1, the colors used are exactly 1..max(c[:v]).
                        # This means that every color in that range appears on one of those vertices.
                        assert(
                               set( c[i] for i in range(v) ) ==
                               set( range(1,max(c[:v])+1) )
                              )
                        
                        c[v]=min( max(c[:v])+1, max_num_colors )
                            # TODO: check that this is what the C++ code does
                            # TODO: Is this what max_color_to_try is?
                
                # go back to beginning of while loop
        
        else:  # no good_color_found, so we backtrack
            v-=1
            
            if v==num_verts_to_precolor-1:
                # We have backtracked to a precoloring without finding a good extension.
                # This is a *bad* precoloring.
                
                # unless we had been trying to reuse the previous extension
                if reuse_extension:
                    #THOUGHT: If we're counting precolorings, then no need to re-use extensions.
                    
                    if debuglevel>=3:
                        print("Reusing extension failed, trying to extend from scratch.")
                    
                    reuse_extension=False
                    
                    # advance to the next vertex, and start "fresh" to find an extension.
                    v+=1
                    
                    # Set c[v].
                    # We do not constrain the colors used for the extension vertices.
                    c[v]=max_num_colors
                    
                    continue  # continue the main loop, so c[v] is not changed
                
                else:  # we have failed to extend even when starting fresh
                    print(f"Bad precoloring! {c=}")
                    return False
            
            if v==0:
                break  # break of out of while loop, done
            
            c[v]-=1  # advance the color
            # go back to the beginning of while loop
    
    print(f"{count_precolorings=}")
    return True  # no bad precolorings found, all precolorings extend


import sys

if __name__=="__main__":

    if len(sys.argv)==0:
        print("SYNTAX: precolor_extend_sage.sage res mod splitlevel [debuglevel=0]")
        exit(99)
    elif len(sys.argv)<4:
        res=0
        mod=1
        splitlevel=2
        debuglevel=0
    else:
        res=int(sys.argv[1])
        mod=int(sys.argv[2])
        splitlevel=int(sys.argv[3])
    
    if len(sys.argv)<5:
        debuglevel=0
    else:
        debuglevel=int(sys.argv[4])
    
    
    for line in sys.stdin:  # We read from stdin to match the C++ program.
        if line.startswith('>'):  # comment
            continue
        else:
            data=line.strip().split(',')
            max_num_colors=int(data[0])
            num_verts_to_precolor=int(data[1])
            G=Graph(data[2])
            result=precoloring_extension(max_num_colors,num_verts_to_precolor,G,res,mod,splitlevel,debuglevel)
            if result:
                print("G is reducible!")
            else:
                print("G has a bad precoloring!")

