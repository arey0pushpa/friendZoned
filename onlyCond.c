
                for (k = 0; k < big; k++)           // THIS IS DYNAMIC 
                {
				 
				 if ((k == 0) && (k == (big - 1)))  {     // If its first Node and only node
                                       // Big == 1
	        		       if (path[k] == vali) {	       // path[k] == vali represents same node	 
					 g0  = graph[valj][path[k]];    // g0 is unsigned int checks if there is an edge btw two nodes
					 v0  = Vedge[valj][path[k]];    // snareVector gets the edgeweight of the corresponding edge.
					 // V02 has been used to get the edgeweight in case graph[i][j] = 2.
                                         v02 = Vedge2[valj][path[k]];   // snareVecor gets the edgeweight of second edge if graph[i][j] == 2 !

                    // Check that there is an edge btw valj ---- pathk  and under investigation vsnare is present on edge.
                    if ( (( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v02 & (1 << j)) ) ))  {
                             C1 = C1 && 1;
                    }
                    else {
                           C1 = C1 && 0;
                    }
				   }
				   else {
					   C1 = 0;
				   }
                    
                  }
                  
                 else if (k == 0) {                    // If its first Node edge
					 g  = graph[valj][path[k]];
					 v  = Vedge[valj][path[k]];
					 v2 = Vedge2[valj][path[k]]; 
                    
                    if ( (( g == 1) && (v & (1 << j))) ||  ( (g == 2) &&  ( (v & ( 1 << j)) || ( v2 & (1 << j)) ) ))  {
                             C1 = C1 && 1;
                    }
                    else {
                           C1 =  0;
                    }
                    
                  }
                  
                  else if (k == (big - 1)) {     // Last node

                            // In case of last node.
						
					 lastg  = graph[path[k]][vali];
					 lastv  = Vedge[path[k]][vali];
					 lastv2 = Vedge2[path[k]][vali];
                     
                     if  ( (( lastg == 1) && (lastv & (1 << j)) ) || ((lastg == 2) && ((lastv & (1 << j)) || (lastv2 & (1 << j))) ) )
                      {
						 C1 = C1 && 1;
				      }
				      
				      else {
					 	 C1 = 0;
					  }
				    }
				    
				    
				 
                 else {         // Any other node besides first and last   					
					
					ng  = graph[path[k]][path[k+1]];
					nv  = Vedge[path[k]][path[k+1]];
					nv2 = Vedge2[path[k]][path[k+1]];
					
                    if (((ng == 1) && (nv & (1 << j))) ||  ( (ng == 2) && ((nv & (1 << j)) || (nv2 & (1 << j))) )) {
                             C1 = C1 && 1;
                    }
                    else {
                        C1 = 0;
                    }
                 }
             
               }
// --------------
